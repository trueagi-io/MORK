use log::trace;
use pathmap::arena_compact::{ACTMmapZipper};
use pathmap::PathMap;
use pathmap::zipper::*;
use mork_expr::{byte_item, destruct, item_byte, serialize, unify, Expr, ExprEnv, Tag};
use mork_expr::macros::SerializableExpr;
use std::collections::BTreeSet;

pub enum ResourceRequest<'a> {
    BTM(&'a [u8]),
    ACT(&'a str),
    Z3(&'a str)
}

fn is_named_expr(e: Expr, name: &[u8], arity: u8) -> bool {
    if e.arity() != Some(arity) {
        return false;
    }

    let mut args = Vec::new();
    ExprEnv::new(0, e).args(&mut args);
    let Some(symbol) = args.first().and_then(|arg| arg.subsexpr().symbol()) else {
        return false;
    };
    unsafe { symbol.as_ref() == Some(name) }
}

/// Selects the first (`HEAD`) or last (`!HEAD`) `limit` matching paths.
///
/// Ordering is the lexicographic order of MORK's encoded expressions, the same
/// order used by the backing `PathMap`.
struct HeadTailSource<const HEAD: bool> {
    limit: usize,
    source_prefix: Vec<u8>,
    target_prefix: Vec<u8>,
}

impl<const HEAD: bool> Source for HeadTailSource<HEAD> {
    fn new(e: Expr) -> Self {
        let mut args = Vec::new();
        ExprEnv::new(0, e).args(&mut args);
        assert_eq!(args.len(), 3, "head/tail expects a limit and a pattern");

        let limit_symbol = args[1]
            .subsexpr()
            .symbol()
            .and_then(|symbol| unsafe { symbol.as_ref() })
            .expect("head/tail limit must be a symbol");
        let limit = std::str::from_utf8(limit_symbol)
            .expect("head/tail limit must be UTF-8")
            .parse()
            .expect("head/tail limit must be a positive integer");
        assert_ne!(limit, 0, "head/tail limit must be positive");

        let target = args[2].subsexpr();
        let source_span = unsafe { e.span().as_ref().unwrap() };
        let target_offset = unsafe { target.ptr.offset_from(e.ptr) as usize };
        let target_prefix = unsafe {
            target
                .prefix()
                .unwrap_or_else(|full| full)
                .as_ref()
                .unwrap()
        };

        Self {
            limit,
            source_prefix: source_span[..target_offset].to_vec(),
            target_prefix: target_prefix.to_vec(),
        }
    }

    fn request(&self) -> impl Iterator<Item = ResourceRequest<'_>> {
        trace!(target: "source", "head/tail requesting {}", serialize(&self.target_prefix));
        std::iter::once(ResourceRequest::BTM([].as_slice()))
    }

    fn source<'trie, 'path, It: Iterator<Item = Resource<'trie, 'path>>>(
        &self,
        mut resources: It,
    ) -> AFactor<'trie, ()>
    where
        'path: 'trie,
    {
        let Resource::BTM(mut source) = resources.next().unwrap() else { unreachable!() };
        let mut selected = BTreeSet::new();

        if source.descend_to_existing(&self.target_prefix) == self.target_prefix.len() {
            while source.to_next_val() {
                let Some(relative) = source
                    .origin_path()
                    .strip_prefix(self.target_prefix.as_slice())
                else {
                    break;
                };
                selected.insert(relative.to_vec());
                if selected.len() > self.limit {
                    let outside = if HEAD {
                        selected.last().unwrap().clone()
                    } else {
                        selected.first().unwrap().clone()
                    };
                    selected.remove(&outside);
                }
            }
        }

        let mut output = PathMap::new();
        for relative in selected {
            let mut path = self.source_prefix.clone();
            path.extend_from_slice(&self.target_prefix);
            path.extend_from_slice(&relative);
            output.insert(&path, ());
        }
        AFactor::MaterializedSource(output.into_read_zipper(&[]))
    }
}

/// Relational union: `(one-of OUTPUT ALTERNATIVE...)`.
///
/// Every alternative is matched independently. Its bindings are applied to
/// `OUTPUT`, producing one materialized relation for downstream factors.
struct OneOfSource {
    output: ExprEnv,
    alternatives: Vec<ExprEnv>,
    prefixes: Vec<Vec<u8>>,
}

impl OneOfSource {
    fn try_from_env(e: ExprEnv) -> Option<Self> {
        let mut args = Vec::new();
        e.args(&mut args);
        if args.len() < 4 {
            return None;
        }
        let name = args[0].subsexpr().symbol()?;
        if unsafe { name.as_ref() } != Some(b"one-of") {
            return None;
        }

        let alternatives = args[2..].to_vec();
        let prefixes = alternatives
            .iter()
            .map(|alternative| unsafe {
                alternative
                    .subsexpr()
                    .prefix()
                    .unwrap_or_else(|full| full)
                    .as_ref()
                    .unwrap()
                    .to_vec()
            })
            .collect();
        Some(Self { output: args[1], alternatives, prefixes })
    }
}

impl Source for OneOfSource {
    fn new(e: Expr) -> Self {
        Self::try_from_env(ExprEnv::new(0, e)).expect("invalid one-of source")
    }

    fn request(&self) -> impl Iterator<Item = ResourceRequest<'_>> {
        self.prefixes
            .iter()
            .map(|prefix| ResourceRequest::BTM(prefix.as_slice()))
    }

    fn source<'trie, 'path, It: Iterator<Item = Resource<'trie, 'path>>>(
        &self,
        mut resources: It,
    ) -> AFactor<'trie, ()>
    where
        'path: 'trie,
    {
        let mut output = PathMap::new();
        let mut buffer = Vec::new();
        let mut stack = Vec::new();
        let mut assignments = Vec::new();

        for alternative in &self.alternatives {
            let Resource::BTM(mut source) = resources.next().unwrap() else { unreachable!() };
            while source.to_next_val() {
                let candidate = Expr { ptr: source.origin_path().as_ptr().cast_mut() };
                let mut pairs = vec![(*alternative, ExprEnv::new(1, candidate))];
                let Ok(bindings) = unify(&mut pairs) else { continue };

                buffer.clear();
                let (_, _, true) = mork_expr::apply_e_clears_stacks_and_cycles_check!(
                    self.output.n,
                    self.output.v,
                    0,
                    self.output.subsexpr(),
                    &bindings,
                    buffer,
                    stack,
                    assignments
                ) else { continue };
                output.insert(&buffer, ());
            }
        }
        AFactor::MaterializedSource(output.into_read_zipper(&[]))
    }
}

pub(crate) enum Resource<'trie, 'path> {
    BTM(ReadZipperUntracked<'trie, 'path, ()>),
    ACT(ACTMmapZipper<'trie, ()>),
    Z3(ReadZipperOwned<()>)
}

pub(crate) trait Source {
    // step 1: parsing the source
    fn new(e: Expr) -> Self;
    // step 2: request access to resources before running
    fn request(&self) -> impl Iterator<Item=ResourceRequest<'_>>;
    // step 3: create the factor in the product/the (virtual) zipper for the source
    fn source<'trie, 'path, It : Iterator<Item=Resource<'trie, 'path>>>(&self, it: It) -> AFactor<'trie, ()> where 'path : 'trie;
}

struct CompatSource {
    e: Expr
}
impl Source for CompatSource {
    fn new(e: Expr) -> Self {
        Self { e }
    }

    fn request(&self) -> impl Iterator<Item=ResourceRequest<'_>> {
        std::iter::once(ResourceRequest::BTM([].as_slice()))
    }

    fn source<'trie, 'path, It: Iterator<Item=Resource<'trie, 'path>>>(&self, mut it: It) -> AFactor<'trie, ()> where 'path : 'trie {
        let Resource::BTM(rz) = it.next().unwrap() else { unreachable!() };
        AFactor::CompatSource(rz)
    }
}

struct BTMSource {
    e: Expr
}
impl Source for BTMSource {
    fn new(e: Expr) -> Self {
        BTMSource { e }
    }

    fn request(&self) -> impl Iterator<Item=ResourceRequest<'_>> {
        std::iter::once(ResourceRequest::BTM([].as_slice()))
    }

    fn source<'trie, 'path, It: Iterator<Item=Resource<'trie, 'path>>>(&self, mut it: It) -> AFactor<'trie, ()> where 'path : 'trie {
        // (I (BTM <pat1>) (ACT <filename> <pat2>)
        //    --factor1--  -----factor2---------
        // prefix: '[2] BTM'
        static PREFIX: [u8; 5] = [item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(3)), b'B', b'T', b'M'];
        let Resource::BTM(rz) = it.next().unwrap() else { unreachable!() };
        let rz = PrefixZipper::new(&PREFIX[..], rz);
        AFactor::PosSource(rz)
    }
}

struct ACTSource {
    e: Expr,
    act: &'static str
}
impl Source for ACTSource {
    fn new(e: Expr) -> Self {
        destruct!(e, ("ACT" {act: &str} se), {
            return ACTSource{ e, act }
        }, _err => { panic!("act not the right shape") });
    }

    fn request(&self) -> impl Iterator<Item=ResourceRequest<'_>> {
        std::iter::once(ResourceRequest::ACT(self.act))
    }

    fn source<'trie, 'path, It: Iterator<Item=Resource<'trie, 'path>>>(&self, mut it: It) -> AFactor<'trie, ()> where 'path : 'trie {
        // prefix: '[3] ACT <filename>'
        static CONSTANT_PREFIX: [u8; 5] = [item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(3)), b'A', b'C', b'T'];
        let Resource::ACT(rz) = it.next().unwrap() else { unreachable!() };
        let mut prefix = vec![];
        prefix.extend_from_slice(&CONSTANT_PREFIX[..]);
        prefix.push(item_byte(Tag::SymbolSize( (self.act.size() as u8) - 1)));
        prefix.extend_from_slice(self.act.as_bytes());
        trace!(target: "source", "act prefix {}", serialize(&prefix[..]));
        let rz = PrefixZipper::new(prefix, rz);
        AFactor::ACTSource(rz)
    }
}

#[cfg(feature = "z3")]
struct Z3Source {
    e: Expr,
    ins: &'static str
}
#[cfg(feature = "z3")]
impl Source for Z3Source {
    fn new(e: Expr) -> Self {
        destruct!(e, ("z3" {instance: &str} se), {
            return Z3Source{ e, ins: instance }
        }, _err => { panic!("z3 not the right shape {:?}", e) });
    }

    fn request(&self) -> impl Iterator<Item=ResourceRequest<'_>> {
        std::iter::once(ResourceRequest::Z3(self.ins))
    }

    fn source<'trie, 'path, It: Iterator<Item=Resource<'trie, 'path>>>(&self, mut it: It) -> AFactor<'trie, ()> where 'path : 'trie {
        // prefix: '[3] z3 <instance name>'
        static CONSTANT_PREFIX: [u8; 4] = [item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(2)), b'z', b'3'];
        let Resource::Z3(rz) = it.next().unwrap() else { unreachable!() };
        let mut prefix = vec![];
        prefix.extend_from_slice(&CONSTANT_PREFIX[..]);
        prefix.push(item_byte(Tag::SymbolSize( (self.ins.size() as u8) - 1)));
        prefix.extend_from_slice(self.ins.as_bytes());
        trace!(target: "source", "z3 prefix {}", serialize(&prefix[..]));
        let rz = PrefixZipper::new(prefix, rz);
        AFactor::Z3Source(rz)
    }
}


struct CmpSource {
    e: Expr,
    cmp: usize
}

impl CmpSource {
    fn policy(ctx: (usize, PathMap<()>), p: &[u8], c: usize) -> ((usize, PathMap<()>), Option<ReadZipperOwned<()>>) {
        let (cmp, map) = ctx;
        if c == 0 {
            if cmp == 0 {
                trace!(target: "source", "== enrolling at {}", serialize(p));
                // bug: de bruijn levels broken, easy fix: shift the copy of p by introductions(p)
                let e = Expr{ ptr: p.as_ptr().cast_mut() };
                let mut qv = p.to_vec();
                e.shift(e.newvars() as _, &mut mork_expr::ExprZipper::new(Expr{ ptr: qv.as_mut_ptr() }));
                ((cmp, map), Some(PathMap::single(&qv[..], ()).into_read_zipper(&[])))
            } else if cmp == 1 {
                let mut cloned = map.clone();
                let present = cloned.remove(p).is_some();
                trace!(target: "source", "!= enrolling (present {:?}) at {}", present, serialize(p));
                ((cmp, map), Some(cloned.into_read_zipper(&[])))
            } else {
                unreachable!()
            }
        } else {
            ((cmp, map), None)
        }
    }
}

impl Source for CmpSource {
    fn new(e: Expr) -> Self {
        let cmp = if unsafe { *e.ptr.offset(2) == b'=' } {
            assert!(unsafe { *e.ptr.offset(3) == b'=' });
            0
        } else if unsafe { *e.ptr.offset(2) == b'!' } {
            assert!(unsafe { *e.ptr.offset(3) == b'=' });
            1
        } else {
            // todo < <= #=
            panic!("comparator not implemented")
        };
        // trace!(target: "source", "cmp {cmp} source");
        CmpSource { e, cmp }
    }

    fn request(&self) -> impl Iterator<Item=ResourceRequest<'_>> {
        std::iter::once(ResourceRequest::BTM([].as_slice()))
    }

    fn source<'trie, 'path, It: Iterator<Item=Resource<'trie, 'path>>>(&self, mut it: It) -> AFactor<'trie, ()> where 'path : 'trie {
        static EQ_PREFIX: [u8; 4] = [item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(2)), b'=', b'='];
        static NE_PREFIX: [u8; 4] = [item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(2)), b'!', b'='];
        let Resource::BTM(rz) = it.next().unwrap() else { unreachable!() };
        let map = rz.try_make_map().unwrap();
        let rz = DependentProductZipperG::new_enroll(rz, (self.cmp, map),
            CmpSource::policy as for<'a> fn((usize, PathMap<()>), &'a [u8], usize) -> ((usize, PathMap<()>), Option<ReadZipperOwned<()>>));
        let rz = PrefixZipper::new(
            if self.cmp == 0 { &EQ_PREFIX[..] }
            else if self.cmp == 1 { &NE_PREFIX[..] }
            else { unreachable!() }, rz);
        AFactor::CmpSource(rz)
    }
}


pub enum ASource { PosSource(BTMSource), ACTSource(ACTSource), CmpSource(CmpSource), HeadSource(HeadTailSource<true>), TailSource(HeadTailSource<false>), OneOfSource(OneOfSource), CompatSource(CompatSource),
    #[cfg(feature = "z3")]
    Z3Source(Z3Source)
}

#[derive(PolyZipper)]
pub enum AFactor<'trie, V: Clone + Send + Sync + Unpin + 'static = ()> {
    CompatSource(ReadZipperUntracked<'trie, 'trie, V>),
    PosSource(PrefixZipper<'trie, ReadZipperUntracked<'trie, 'trie, V>>),
    ACTSource(PrefixZipper<'trie, ACTMmapZipper<'trie, V>>),
    CmpSource(PrefixZipper<'trie, DependentProductZipperG<'trie, ReadZipperUntracked<'trie, 'trie, V>,
        ReadZipperOwned<V>, V, (usize, PathMap<()>), for<'a> fn((usize, PathMap<()>), &'a [u8], usize) -> ((usize, PathMap<()>), Option<ReadZipperOwned<V>>)>>),
    MaterializedSource(ReadZipperOwned<V>),
    #[cfg(feature = "z3")]
    Z3Source(PrefixZipper<'trie, ReadZipperOwned<V>>),
}

impl ASource {
    pub fn compat(e: Expr) -> Self {
        ASource::CompatSource(CompatSource::new(e))
    }

    pub fn pattern(&self, original: ExprEnv) -> ExprEnv {
        match self {
            ASource::OneOfSource(source) => source.output,
            _ => original,
        }
    }

    pub fn from_env(e: ExprEnv) -> Self {
        if let Some(source) = OneOfSource::try_from_env(e) {
            ASource::OneOfSource(source)
        } else {
            ASource::new(e.subsexpr())
        }
    }
}

impl Source for ASource {
    fn new(e: Expr) -> Self {
        if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3)) && *e.ptr.offset(2) == b'B' && *e.ptr.offset(3) == b'T' && *e.ptr.offset(4) == b'M' } {
            ASource::PosSource(BTMSource::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3)) && *e.ptr.offset(2) == b'A' && *e.ptr.offset(3) == b'C' && *e.ptr.offset(4) == b'T' } {
            ASource::ACTSource(ACTSource::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(2)) && *e.ptr.offset(2) == b'z' && *e.ptr.offset(3) == b'3' } {
            #[cfg(feature = "z3")]
            return ASource::Z3Source(Z3Source::new(e));
            #[cfg(not(feature = "z3"))]
            panic!("MORK was not built with the z3 feature, yet trying to call {:?}", e);
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(2)) && (*e.ptr.offset(2) == b'=' || *e.ptr.offset(2) == b'!') && *e.ptr.offset(3) == b'=' } {
            ASource::CmpSource(CmpSource::new(e))
        } else if is_named_expr(e, b"head", 3) {
            ASource::HeadSource(HeadTailSource::new(e))
        } else if is_named_expr(e, b"tail", 3) {
            ASource::TailSource(HeadTailSource::new(e))
        } else {
            unreachable!()
        }
    }

    fn request(&self) -> impl Iterator<Item=ResourceRequest<'_>> {
        gen move {
            match self {
                ASource::PosSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::ACTSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::CmpSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::HeadSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::TailSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::OneOfSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::CompatSource(s) => { for i in s.request().into_iter() { yield i } }
                #[cfg(feature = "z3")]
                ASource::Z3Source(s) => { for i in s.request().into_iter() { yield i } }
            }
        }
    }

    fn source<'trie, 'path, It: Iterator<Item=Resource<'trie, 'path>>>(&self, mut it: It) -> AFactor<'trie, ()> where 'path : 'trie {
        match self {
            ASource::PosSource(s) => { s.source(it) }
            ASource::ACTSource(s) => { s.source(it) }
            ASource::CmpSource(s) => { s.source(it) }
            ASource::HeadSource(s) => { s.source(it) }
            ASource::TailSource(s) => { s.source(it) }
            ASource::OneOfSource(s) => { s.source(it) }
            ASource::CompatSource(s) => { s.source(it) }
            #[cfg(feature = "z3")]
            ASource::Z3Source(s) => { s.source(it) }
        }
    }
}
