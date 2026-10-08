use std::fmt::Debug;

use eval_ffi::{EvalError, ExprSource, SourceItem};
use pathmap::utils::{BitMask, ByteMask};
use log::trace;
use pathmap::arena_compact::{ACTMmapZipper};
use pathmap::PathMap;
use pathmap::zipper::*;
use mork_expr::{byte_item, destruct, item_byte, serialize, Expr, Tag};
use mork_expr::macros::SerializableExpr;

pub enum ResourceRequest {
    BTM(&'static [u8]),
    ACT(&'static str),
    Z3(&'static str)
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
    fn request(&self) -> impl Iterator<Item=ResourceRequest>;
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

    fn request(&self) -> impl Iterator<Item=ResourceRequest> {
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

    fn request(&self) -> impl Iterator<Item=ResourceRequest> {
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

    fn request(&self) -> impl Iterator<Item=ResourceRequest> {
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

    fn request(&self) -> impl Iterator<Item=ResourceRequest> {
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

    fn request(&self) -> impl Iterator<Item=ResourceRequest> {
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


pub enum ASource { PosSource(BTMSource), ACTSource(ACTSource), CmpSource(CmpSource), CompatSource(CompatSource),
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
    #[cfg(feature = "z3")]
    Z3Source(PrefixZipper<'trie, ReadZipperOwned<V>>),
}

impl ASource {
    pub fn compat(e: Expr) -> Self {
        ASource::CompatSource(CompatSource::new(e))
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
        } else {
            unreachable!()
        }
    }

    fn request(&self) -> impl Iterator<Item=ResourceRequest> {
        gen move {
            match self {
                ASource::PosSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::ACTSource(s) => { for i in s.request().into_iter() { yield i } }
                ASource::CmpSource(s) => { for i in s.request().into_iter() { yield i } }
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
            ASource::CompatSource(s) => { s.source(it) }
            #[cfg(feature = "z3")]
            ASource::Z3Source(s) => { s.source(it) }
        }
    }
}











/// The following expresses the DSL grammar in BNF style. Some quirks explaind below.</br>
/// `""` for regex matching terminal tokens.</br>
/// `''` for unescaped terminal tokens.</br>
/// `;` to terminate a non-terminal.</br>
///
/// `{ symbol | variable | tuple[n] | tuple[n..=m] | [n] }` describes the value type as a MORK expr.</br>
/// `{ [n]          }` means that this a sequence of expressions of length n, but is not itself a proper subexpression, a kind of tuple slice.</br>
/// `{ tuple[n]     }` is a tuple of arity n.</br>
/// `{ tuple[n..=m] }` is a tuple of arity at least n, and at most m.</br>
///
/// An example
/// ```ignore
/// (exec 0
///     (I  ( admit
///           (, ($x var
///                  (symbol (#   6)
///                          (#.. (1 3) (10 15))
///                  )
///                  (tuple  (#   4 13)
///                          (#.. (7 9))
///                  )
///              )
///              ($y var
///                  (symbol (#.. (4 6)) ) )
///           )
///           bind
///           (, (($x $y) nonvar)
///              ($z      nonvar)
///              ($b      nonvar)
///           )
///         )
///         ....
///     )
///     (,)
/// )
/// ```
static GRAMMAR : &'static str = "
AdmitDSl          ::= Admit                                               ;  { tuple[2|4]    }

PNumber           ::=  \"[1-9]\"  |  \"[1-5][0-9]\"  |  \"6[0-4]\"        ;  { symbol        }
Number            ::=  '0'  |  PNumber                                    ;  { symbol        }
PNumbers          ::=  '('  '#'    PNumber{1,62}  ')'                     ;  { tuple[2..=63] }
Numbers           ::=  '('  '#'    Number{1,62}   ')'                     ;  { tuple[2..=63] }
PNumberRanges     ::=  '('  '#..'  ('(' PNumber PNumber  ')'){1,62}  ')'  ;  { tuple[2..=63] }
NumberRanges      ::=  '('  '#..'  ('(' Number  Number   ')'){1,62}  ')'  ;  { tuple[2..=63] }
SymbolConstraint  ::=  'symbol'                                           ;  { symbol        }
SymbolConstraint  ::=  '('  'symbol'  PNumbers  ')'                       ;  { tuple[2]      }
SymbolConstraint  ::=  '('  'symbol'  PNumbers{,1}  PNumberRanges)  ')'   ;  { tuple[2..=3]  }
TupleConstraint   ::=  'tuple'                                            ;  { symbol        }
TupleConstraint   ::=  '('  'tuple'   Numbers  ')'                        ;  { tuple[2]      }
TupleConstraint   ::=  '('  'tuple'   Numbers{,1}  NumberRanges  ')'      ;  { tuple[2..=3]  }
Var               ::=  \"$[^ \n\t\\(\\)]{1,}\"                            ;  { variable      }
Vars              ::=  Var                                                ;  { variable      }
Vars              ::=  '('  Var{1,63}  ')                                 ;  { tuple[1..=63] }
AdmitContraint    ::=  '('  Vars
                            '('  (  'var'
                                 |  SymbolConstraint
                                 |  TupleConstraint){1,63}
                                 )
                            ')'
                       ')'                                                ;  { tuple[2]      }
BindConstrait     ::=  '('  Vars  'nonvar'  ')'                           ;  { tuple[2]      }
AdmitDecl         ::=  'admit'  '('  ','  AdmitContraint{,62}  ')'        ;  { [2]           }
BindDecl          ::=  'bind'   '('  ','  BindConstrait{,62}   ')'        ;  { [2]           }
Admit             ::=  '('  AdmitDecl  ')'                                ;  { tuple[2]      }
Admit             ::=  '('  AdmitDecl  BindDecl ')'                       ;  { tuple[4]      }
";

/// If the `nth` bit in the admit_tag_mask is on, the `nth` variable has an admit mask that constraints matching.</br>
/// If it `nth` bit if off, the `admit_masks[nth]` value should not be accessed.
/// It is semanticaly equivalent to a full mask, but to avoid a large constant overhead,
/// we should avoid the need to fill the untagged masks</br>
#[derive(Clone, Copy)]
struct AdmitConstraits {
    admit_masks    : [ByteMask;64],
    admit_tag_mask : u64,
    bind_as_nonvar : u64,
    next_newvar    : u8,
}
impl Debug for AdmitConstraits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AdmitConstraits {{")?;

        let mut nth       = 0_usize;
        let mut remaining = self.admit_tag_mask | self.bind_as_nonvar;
        while remaining != 0 {
            let t = remaining.trailing_zeros() as usize;
            nth += t;

            let cursor = 1 << nth;
            write!(f,"\n\t{} : {{", nth )?;
            if cursor & self.admit_tag_mask != 0 {
                if self.admit_masks[nth].test_bit(item_byte(Tag::NewVar)) { write!(f, "\n\t    var    : true")?; }
                let sym_mask = self.admit_masks[nth].and(&SYMBOL_BITS);

                if sym_mask.count_bits() != 0 {
                    let mut acc = 0_u64;

                    for i in sym_mask.iter() { match byte_item(i) { Tag::SymbolSize(size) => acc |= 1 << size, _ => {} } }
                    write!(f, "\n\t    symbol :")?;
                    for b in acc.to_be_bytes() { write!(f, " {:0>8b}", b)?; }
                }

                let tup_mask = self.admit_masks[nth].and(&TUPLE_BITS);
                if tup_mask.count_bits() != 0 {
                    let mut acc = 0_u64;

                    for i in tup_mask.iter() { match byte_item(i) { Tag::Arity(arity) => acc |= 1 << arity, _ => {} }  }
                    write!(f, "\n\t    tuple  :")?;
                    for b in acc.to_be_bytes() { write!(f, " {:0>8b}", b)?; }
                }
            }
            if cursor & self.bind_as_nonvar != 0 { write!(f, "\n\t    bind   : nonvar")? }
            write!(f,"\n\t}}")?;

            nth+=1;
            remaining >>= t+1;
        }
        write!(f, "\n}}")
    }
}



const VAR_BITS : ByteMask = {
    let mut mask = ByteMask::new();
    mask.set_inclusive_bit_range(item_byte(Tag::NewVar)..=item_byte(Tag::NewVar));
    mask.set_inclusive_bit_range(item_byte(Tag::VarRef(0))..=item_byte(Tag::VarRef(63)));
    mask
};
const SYMBOL_BITS : ByteMask = {
    let mut mask = ByteMask::new();
    mask.set_inclusive_bit_range(item_byte(Tag::SymbolSize(1))..=item_byte(Tag::SymbolSize(63)));
    mask
};
const TUPLE_BITS : ByteMask = {
    let mut mask = ByteMask::new();
    mask.set_inclusive_bit_range(item_byte(Tag::Arity(0))..=item_byte(Tag::Arity(63)));
    mask
};



fn build_admit_constraints(e : Expr, mut next_newvar : u8) -> Result<AdmitConstraits, EvalError> {
    let mut bind_as_nonvar = 0_u64;
    let mut admit_tag_mask = 0_u64;
    let mut admit_masks    = [ByteMask::new(); 64];
    let mut es             = ExprSource::new(e.ptr);
    const GRAMMAR_ERR   : EvalError                          = EvalError::Msg { ptr: GRAMMAR.as_ptr(), len: GRAMMAR.len() };
    const GRAMMAR_ERROR : Result<AdmitConstraits, EvalError> = Err(GRAMMAR_ERR);

    macro_rules! action {
            ($TRACE:ident, $ACTION:ident) => {  #[cfg(debug_assertions)]if ($TRACE.1 &(1 << (AdmitConstraitsTraceAction::$ACTION as u64))) != 0 {$TRACE.0.push(  (line!() as usize, AdmitConstraitsTraceAction::$ACTION))};  };
    }





    
    #[inline(always)]
    fn parse_var_set(es : &mut ExprSource, next_newvar : &mut u8)->Result<u64, EvalError>{
        const GRAMMAR_ERROR : Result<u64, EvalError> = Err(GRAMMAR_ERR);
            // here we accumulate the vars into a bitset for the admit constraints
            let mut var_set = 0_u64;
            match es.read() {
                SourceItem::Tag(Tag::NewVar   ) => { var_set |= (1 << *next_newvar); *next_newvar += 1 },
                SourceItem::Tag(Tag::VarRef(r)) => { var_set |= (1 << r);},
                SourceItem::Tag(Tag::Arity(a) ) => {
                    for each in 0..a {
                        match es.read() {
                            SourceItem::Tag(Tag::NewVar   ) => {var_set |= (1 << *next_newvar); *next_newvar += 1 },
                            SourceItem::Tag(Tag::VarRef(r)) => {var_set |= (1 << r);},
                            _ => return GRAMMAR_ERROR,
                        }
                    }
                },
                _ => return GRAMMAR_ERROR,
            }
            Ok(var_set)   
    }


    /// returns false if there there is a conflict leading to the constraits being unsatisfiable
    #[inline(always)]
    fn effect_on_nth_bit(mask : u64, mut effect : impl FnMut(usize)-> bool) -> bool {
        let mut nth = 0_usize;
        let mut remaining = mask;
        while remaining != 0 {
            let t = remaining.trailing_zeros() as usize;
            nth += t;

            if !effect(nth) { return false; };

            nth+=1;
            remaining >>= t+1;
        }
        true
    };


    let SourceItem::Tag(Tag::Arity(top_level_arity @ (2 | 4))) = es.read() else { return GRAMMAR_ERROR; };    
    let SourceItem::Symbol(b"admit") = es.read() else { return GRAMMAR_ERROR; };


    let comma_list_arity          = es.consume_head_check(b","    )? else { return GRAMMAR_ERROR; };
    
    for each in 0..comma_list_arity {

        let SourceItem::Tag(Tag::Arity(admition_arity @ 2..)) = es.read()     else { return GRAMMAR_ERROR; };

        let admit_var_set = parse_var_set(&mut es, &mut next_newvar)?;
        admit_tag_mask |= admit_var_set;

        let mut mask = ByteMask::new();

        for each in 1..admition_arity {
            match es.read() {
                SourceItem::Symbol(b"var")    => mask = mask.or(&VAR_BITS),
                SourceItem::Symbol(b"symbol") => mask = mask.or(&SYMBOL_BITS),
                SourceItem::Symbol(b"tuple" ) => mask = mask.or(&TUPLE_BITS),
                SourceItem::Tag(Tag::Arity(a @ 2..=3)) => {


                    #[inline(always)]
                    fn handle_numbers_and_ranges<const ZERO_IS_ERROR : bool>(
                        es    : &mut ExprSource,
                        a     : u8,
                        mask  : &mut ByteMask,
                        tag   : impl Fn(u8)->Tag,
                    ) -> Result<(), EvalError> {
                        const GRAMMAR_ERROR : Result<(), EvalError> = Err(GRAMMAR_ERR);
                        #[inline(always)]
                        fn read_number(es : &mut ExprSource )->Result<u8,EvalError> {
                            const GRAMMAR_ERROR : Result<u8, EvalError> = Err(GRAMMAR_ERR);

                            let SourceItem::Symbol(s @ ( [b'0'..=b'9'] 
                                                       | [b'0'..=b'9',b'0'..=b'9']
                                                       ) ) = es.read() else {return GRAMMAR_ERROR;};
                            let mut acc = 0;
                            for &each in s { acc = acc*10 + (each-b'0') }
                                                   
                            if acc > 63 { return GRAMMAR_ERROR; }
                            Ok(acc)
                        }

                        'done : {

                            let range_count = match es.consume_head()? {
                                (n, b"#") => {

                                    for _ in  0..n {
                                        let len = read_number(es)?;
                                        if ZERO_IS_ERROR && len == 0 { return GRAMMAR_ERROR; }
                                        mask.set_bit(item_byte(tag(len)));
                                    }
                                    if a == 2 { break 'done; }
                                    es.consume_head_check(b"#..")?
                                }
                                (n, b"#..") if a == 2 => n,
                                _                     => return GRAMMAR_ERROR,
                            };

                            for _ in 0..range_count {
                                let SourceItem::Tag(Tag::Arity(2)) = es.read() else { return GRAMMAR_ERROR; };
                                let s = read_number(es)?;
                                let e = read_number(es)?;
                                if s > e { return GRAMMAR_ERROR; }
                                if ZERO_IS_ERROR && (s == 0 || e == 0) { return GRAMMAR_ERROR; }

                                mask.set_inclusive_bit_range(item_byte(tag(s))..=item_byte(tag(e)));
                            }
                        }
                        Ok(())
                    }
                    match es.read() {
                        SourceItem::Symbol(b"symbol") => {

                            handle_numbers_and_ranges::<true>( &mut es, a, &mut mask, Tag::SymbolSize)?
                        },
                        SourceItem::Symbol(b"tuple")  => handle_numbers_and_ranges::<false>(&mut es, a, &mut mask, Tag::Arity)?,
                        _                             => return GRAMMAR_ERROR,
                    }
                },
                _ => return GRAMMAR_ERROR,
            }
        }

        effect_on_nth_bit(admit_var_set, |nth|{ admit_masks[nth] = admit_masks[nth].or(&mask); true });
    }

    if top_level_arity == 4 {
        let SourceItem::Symbol(b"bind") = es.read()                        else { return GRAMMAR_ERROR; };
        let bind_list_arity             = es.consume_head_check(b","    )? else { return GRAMMAR_ERROR; };


        for each in 0..bind_list_arity {
            let SourceItem::Tag(Tag::Arity(2)) = es.read() else { return GRAMMAR_ERROR; };
            let bind_set = parse_var_set(&mut es, &mut next_newvar)?;

            match es.read() {
                SourceItem::Symbol(b"nonvar") => { bind_as_nonvar |= bind_set }
                _ => return GRAMMAR_ERROR,
            }
        }
    }

    // We look for conflicts that can't ever be satisfied
    const UNSAT : &[u8] = b"`exec` has conflicting unification `bind` constraints from `admit`";
    if  !effect_on_nth_bit(bind_as_nonvar & admit_tag_mask, |nth| {
            // Here we check if the constraint is only on a variable, under the assumption that exactly __all__ var bits are set,
            // The semantics of `admit` require that the tags are checked a final time after unification,
            //   so if we filter out all nonvars via the mask, then the nonvar bind constraint would not need to fire anyways.

            const VAR_BITS_COUNT : usize = { let vb = VAR_BITS.0; (vb[0].count_ones() + vb[1].count_ones() + vb[2].count_ones() + vb[3].count_ones()) as usize };
            // NewVar --> (total_bits != VAR_BITS_COUNT) otherwise UNSAT
            ! admit_masks[nth].test_bit(item_byte(Tag::NewVar)) || admit_masks[nth].count_bits() != VAR_BITS_COUNT 
        })
    {
        return Err(EvalError::Msg { ptr: UNSAT.as_ptr(), len: UNSAT.len() });
    }

    Ok(AdmitConstraits { admit_masks, admit_tag_mask, bind_as_nonvar, next_newvar })
}


#[cfg(test)] 
mod admit_tests {
    use crate::{expr, sources::build_admit_constraints};

    #[test]
    fn admit_test(){
        let s = crate::space::Space::new();
        let e = expr!(s, "\
            [4] admit                                     \
                [3] , [4] $ var                           \
                            [3] symbol [2] #   6          \
                                       [3] #.. [2] 1 3    \
                                               [2] 10 15  \
                            [3] tuple  [3] #   4 3        \
                                       [2] #.. [2] 7 9    \
                      [3] $ var                           \
                            [2] symbol [2] #.. [2] 4 6    \
                bind                                      \
                [4] , [2] [2] _1 _2   nonvar              \
                      [2] $           nonvar              \
                      [2] $           nonvar              \
        ");
        let admit_set = build_admit_constraints(e, 0);
        println!("e         : {:?}", e.string());
        println!("admit_set : {:?}", admit_set);
    }
}
