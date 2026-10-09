use std::fmt::Debug;
use std::path::Iter;

use eval_ffi::{EvalError, ExprSource, SourceItem};
use pathmap::utils::{BitMask, ByteMask};
use log::trace;
use pathmap::arena_compact::{ACTMmapZipper};
use pathmap::PathMap;
use pathmap::zipper::*;
use mork_expr::{byte_item, destruct, item_byte, serialize, Expr, Tag};
use mork_expr::macros::SerializableExpr;

use crate::sources::AdmitGrammarRule::NumberLargerThan64;

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
static GRAMMAR : [&'static str; {AdmitGrammarRule::_Variants as usize}] = const { 
    use AdmitGrammarRule::*;
    let mut out = [""; _Variants as usize];

    out[AdmitDsl         as usize] = "AdmitDSl          ::= Admit                                               ;  { tuple[2|4]    }";
    out[PNumber          as usize] = "PNumber           ::=  \"[1-9]\"  |  \"[1-5][0-9]\"  |  \"6[0-4]\"        ;  { symbol        }";
    out[Number           as usize] = "Number            ::=  '0'  |  PNumber                                    ;  { symbol        }";
    out[PNumbers         as usize] = "PNumbers          ::=  '('  '#'    PNumber{1,62}  ')'                     ;  { tuple[2..=63] }";
    out[Numbers          as usize] = "Numbers           ::=  '('  '#'    Number{1,62}   ')'                     ;  { tuple[2..=63] }";
    out[PNumberRanges    as usize] = "PNumberRanges     ::=  '('  '#..'  ('(' PNumber PNumber  ')'){1,62}  ')'  ;  { tuple[2..=63] }";
    out[NumberRanges     as usize] = "NumberRanges      ::=  '('  '#..'  ('(' Number  Number   ')'){1,62}  ')'  ;  { tuple[2..=63] }";
    out[SymbolConstraint as usize] = "SymbolConstraint  ::=  'symbol'                                           ;  { symbol        }\n\
                                      SymbolConstraint  ::=  '('  'symbol'  PNumbers  ')'                       ;  { tuple[2]      }\n\
                                      SymbolConstraint  ::=  '('  'symbol'  PNumbers{,1}  PNumberRanges)  ')'   ;  { tuple[2..=3]  }";
    out[TupleConstraint  as usize] = "TupleConstraint   ::=  'tuple'                                            ;  { symbol        }\n\
                                      TupleConstraint   ::=  '('  'tuple'   Numbers  ')'                        ;  { tuple[2]      }\n\
                                      TupleConstraint   ::=  '('  'tuple'   Numbers{,1}  NumberRanges  ')'      ;  { tuple[2..=3]  }";
    out[Var              as usize] = "Var               ::=  \"$[^ \n\t\\(\\)]{1,}\"                            ;  { variable      }";
    out[Vars             as usize] = "Vars              ::=  Var                                                ;  { variable      }\n\
                                      Vars              ::=  '('  Var{1,63}  ')                                 ;  { tuple[1..=63] }";
    out[AdmitConstraint  as usize] = "AdmitContraint    ::=  '('  Vars                                                              \
                                    \n                            '('  (  'var'                                                     \
                                    \n                                 |  SymbolConstraint                                          \
                                    \n                                 |  TupleConstraint                                           \
                                    \n                                 ){1,63}                                                      \
                                    \n                            ')'                                                               \
                                    \n                       ')'                                                ;  { tuple[2]      }";
    out[BindConstrait    as usize] = "BindConstrait     ::=  '('  Vars  'nonvar'  ')'                           ;  { tuple[2]      }";
    out[AdmitDecl        as usize] = "AdmitDecl         ::=  'admit'  '('  ','  AdmitContraint{,62}  ')'        ;  { [2]           }";
    out[BindDecl         as usize] = "BindDecl          ::=  'bind'   '('  ','  BindConstrait{,62}   ')'        ;  { [2]           }";
    out[Admit            as usize] = "Admit             ::=  '('  AdmitDecl  ')'                                ;  { tuple[2]      }\n\
                                      Admit             ::=  '('  AdmitDecl  BindDecl ')'                       ;  { tuple[4]      }";
    
    out[RangeError         as usize] = "for a range (s e), s <= e";
    out[NumberLargerThan64 as usize] = "parsed number larger than 64";
    out[UnSat              as usize] =  "`exec` has conflicting unification `bind` constraints from `admit`";

    out
};

#[repr(usize)]
enum AdmitGrammarRule {
    AdmitDsl,
    PNumber,
    Number,
    PNumbers,
    Numbers,
    PNumberRanges,
    NumberRanges,
    SymbolConstraint,
    TupleConstraint,
    Var,
    Vars,
    AdmitConstraint,
    BindConstrait,
    AdmitDecl,
    BindDecl,
    Admit,

    RangeError,
    NumberLargerThan64,
    UnSat,

    _Variants
}





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
impl AdmitConstraits {
    fn iter(&self)->AdmitConstraitsIter{
        AdmitConstraitsIter::new(self)
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
    const fn grammar_error<T>(rule : AdmitGrammarRule)->Result<T, EvalError> {
        let s = GRAMMAR[rule as usize];
        Err( EvalError::Msg { ptr: s.as_ptr(), len: s.len() } )
    }

    #[inline(always)]
    fn parse_var_set(es : &mut ExprSource, next_newvar : &mut u8)->Result<u64, EvalError>{
        // const GRAMMAR_ERROR : Result<u64, EvalError> = Err(GRAMMAR_ERR);
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
                            _ => return grammar_error(AdmitGrammarRule::Vars),
                        }
                    }
                },
                _ => return grammar_error(AdmitGrammarRule::Vars),
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


    let SourceItem::Tag(Tag::Arity(top_level_arity @ (2 | 4))) = es.read() else { return grammar_error(AdmitGrammarRule::Admit); };    
    let SourceItem::Symbol(b"admit")                           = es.read() else { return grammar_error(AdmitGrammarRule::AdmitDecl); };


    let comma_list_arity          = es.consume_head_check(b","    )? else { return grammar_error(AdmitGrammarRule::AdmitDecl); };
    
    for each in 0..comma_list_arity {

        let SourceItem::Tag(Tag::Arity(admition_arity @ 2..)) = es.read()     else { return grammar_error(AdmitGrammarRule::AdmitConstraint); };

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
                        #[inline(always)]
                        fn read_number(es : &mut ExprSource )->Result<u8,EvalError> {

                            let SourceItem::Symbol(s @ ( [b'0'..=b'9'] 
                                                       | [b'0'..=b'6',b'0'..=b'9']
                                                       ) ) = es.read() else {return grammar_error(AdmitGrammarRule::Number);};
                            let mut acc = 0;
                            for &each in s { acc = acc*10 + (each-b'0') }
                                                   
                            if acc > 63 { return grammar_error(NumberLargerThan64); }
                            Ok(acc)
                        }

                        'done : {

                            let range_count = match es.consume_head()? {
                                (n, b"#") => {

                                    for _ in  0..n {
                                        let len = read_number(es)?;
                                        if ZERO_IS_ERROR && len == 0 { return grammar_error(AdmitGrammarRule::PNumber); }
                                        mask.set_bit(item_byte(tag(len)));
                                    }
                                    if a == 2 { break 'done; }
                                    match es.consume_head_check(b"#..") {
                                        Ok(n_) => n_,
                                        Err(_) => return if ZERO_IS_ERROR {grammar_error(AdmitGrammarRule::PNumberRanges)} else {grammar_error(AdmitGrammarRule::NumberRanges)},
                                    }
                                }
                                (n, b"#..") if a == 2 => n,
                                _                     => return grammar_error(AdmitGrammarRule::AdmitConstraint),
                            };

                            for _ in 0..range_count {
                                let SourceItem::Tag(Tag::Arity(2)) = es.read() else { 
                                    return if ZERO_IS_ERROR {grammar_error(AdmitGrammarRule::PNumberRanges)} else {grammar_error(AdmitGrammarRule::NumberRanges)};
                                };
                                let s = read_number(es)?;
                                let e = read_number(es)?;
                                if s > e { return grammar_error(AdmitGrammarRule::RangeError); }
                                if ZERO_IS_ERROR && s == 0 { return grammar_error(AdmitGrammarRule::PNumber); }

                                mask.set_inclusive_bit_range(item_byte(tag(s))..=item_byte(tag(e)));
                            }
                        }
                        Ok(())
                    }
                    match es.read() {
                        SourceItem::Symbol(b"symbol") => handle_numbers_and_ranges::<true>( &mut es, a, &mut mask, Tag::SymbolSize)?,
                        SourceItem::Symbol(b"tuple")  => handle_numbers_and_ranges::<false>(&mut es, a, &mut mask, Tag::Arity)?,
                        _                             => return grammar_error(AdmitGrammarRule::AdmitConstraint),
                    }
                },
                _ => return grammar_error(AdmitGrammarRule::AdmitConstraint),
            }
        }

        effect_on_nth_bit(admit_var_set, |nth|{ admit_masks[nth] = admit_masks[nth].or(&mask); true });
    }

    if top_level_arity == 4 {
        let SourceItem::Symbol(b"bind") = es.read()                        else { return grammar_error(AdmitGrammarRule::Admit); };
        let bind_list_arity             = es.consume_head_check(b","    )? else { return grammar_error(AdmitGrammarRule::BindDecl); };


        for each in 0..bind_list_arity {
            let SourceItem::Tag(Tag::Arity(2)) = es.read() else { return grammar_error(AdmitGrammarRule::BindConstrait); };
            let bind_set = parse_var_set(&mut es, &mut next_newvar)?;

            match es.read() {
                SourceItem::Symbol(b"nonvar") => { bind_as_nonvar |= bind_set }
                _ => return grammar_error(AdmitGrammarRule::BindConstrait),
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
        return grammar_error(AdmitGrammarRule::UnSat);
    }

    Ok(AdmitConstraits { admit_masks, admit_tag_mask, bind_as_nonvar, next_newvar })
}





#[derive(PartialEq, Eq, Clone, Copy)]
enum AdmitConstraitsItemMatch {
    All,
    Selection(AdmitConstraitsSelection)
}
#[derive(PartialEq, Eq, Clone, Copy)]
struct AdmitConstraitsSelection {
    symbols     : u64,
    tuples      : u64,
    match_var   : bool,
}
#[derive(PartialEq, Eq)]
struct AdmitConstraitItem {
    var_id      : u8,
    match_      : AdmitConstraitsItemMatch,
    bind_nonvar : bool,
}
struct AdmitConstraitsIter<'a> {
    nth           : usize,
    shifting_mask : u64,
    constraints   : &'a AdmitConstraits,
}
impl<'a> AdmitConstraitsIter<'a> {
    fn new(constraints : &'a AdmitConstraits)->Self {
        Self { nth: 0, shifting_mask: constraints.admit_tag_mask | constraints.bind_as_nonvar, constraints }
    }
}
impl<'a> Iterator for AdmitConstraitsIter<'a> {
    type Item = AdmitConstraitItem;
    fn next(&mut self) -> Option<Self::Item> {
        if self.shifting_mask==0 {return None;}

        let t = self.shifting_mask.trailing_zeros() as usize;
        self.nth += t;

        const TUPLE_HEADER : usize = const { 
            let mut i = 0; while i < 64 { assert!((item_byte(Tag::Arity(i)) & 0b_1100_0000) >> 6 == 0b_00) ; i+=1 } 
            0b_00
        };
        
        // This just encodes our understanding of what we expect the representation to be.
        const _VAR_REF_HEADER : usize = const { 
            let mut i = 0; 
            while i < 64 { assert!((item_byte(Tag::VarRef(i)) & 0b_1100_0000) >> 6 == 0b_10); i+=1;}
            0b_10 
        };
        
        const SYM_AND_NEWVAR_HEADER : usize = const { 
            let mut i = 1;
            while i < 64 { assert!((item_byte(Tag::SymbolSize(i)) & 0b_1100_0000) >> 6 == 0b_11); i+=1 }; 
            assert!((item_byte(Tag::NewVar) & 0b_1100_0000) >> 6 == 0b_11);
            0b_11 as usize
        };

        let var_id = self.nth;
        let mask = self.constraints.admit_masks[var_id].0;

        // we work under the assumption that if new_var is set, all vars are set.
        let match_var   = mask[SYM_AND_NEWVAR_HEADER] & (1<<0 /* NewVar */) != 0;
        let symbols     = mask[SYM_AND_NEWVAR_HEADER] & !(1<<0 /* NewVar */);
        let tuples      = mask[TUPLE_HEADER];
        let bind_nonvar = self.constraints.bind_as_nonvar & 1<<var_id != 0;

        let out = AdmitConstraitItem { var_id : var_id as u8, 
            match_ : if !match_var && symbols ==0 && tuples ==0 {
                AdmitConstraitsItemMatch::All
            } else {
                AdmitConstraitsItemMatch::Selection(AdmitConstraitsSelection { symbols, tuples, match_var })
            },
            bind_nonvar
        };
        
        self.nth+=1;
        self.shifting_mask >>= t+1;
    
        Some(out)
    }
}
impl Debug for AdmitConstraitItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AdmitConstraitItem {{")?;
        write!(f, "\n\tvar_id    : {}", self.var_id)?;
        match &self.match_ {
            AdmitConstraitsItemMatch::All => write!(f, "\n\tmatch_   : All")?,
            AdmitConstraitsItemMatch::Selection(self_) => {
                write!(f, "\n\tmatch_   : Selection {{")?;
                
                
                if self_.match_var {
                    write!(f, "\n\t  match_var : true,")?
                }
                if self_.symbols != 0 {
                    write!(f, "\n\t  symbols   :")?;
                    for b in self_.symbols.to_be_bytes() { write!(f, " {:0>8b}", b)?; }
                    write!(f, ",");
                }
                if self_.tuples != 0 {
                    write!(f, "\n\t  tuples    :")?;
                    for b in self_.tuples.to_be_bytes() { write!(f, " {:0>8b}", b)?; }
                    write!(f, ",");
                }
                write!(f, "\n\t}}")?;                
            },
        }
        if self.bind_nonvar {
            write!(f, "\n\t  bind_var  : true,")?
        }
        writeln!(f, "\n}}")
    }
    
}

impl Debug for AdmitConstraits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AdmitConstraits : \n")?;
        for each in self.iter() {
            write!(f, "{:?}", each);
        }
        Ok(())
    }
}





#[cfg(test)]
mod admit_tests {
    use eval_ffi::EvalError;
use mork_expr::item_byte;

use crate::{expr, sources::{AdmitConstraitItem, AdmitConstraitsItemMatch, AdmitConstraitsSelection, GRAMMAR, build_admit_constraints}};


    fn eval_error_str<'a>(e : EvalError)->&'a str {
        match e {
            EvalError::NotEnoughSpace   => "NotEnoughSpace",
            EvalError::Msg { ptr, len } => unsafe { str::from_utf8_unchecked(core::slice::from_raw_parts(ptr, len)) },
        }
    }

    fn id_match_bind_nonvar(
        id          : u8, 
        match_      : AdmitConstraitsItemMatch,
        bind_nonvar : bool,
    ) -> AdmitConstraitItem {
        AdmitConstraitItem { var_id: id, match_: match_, bind_nonvar }
    }
    fn select_symbols_tuples_vars(symbols : u64, tuples : u64, vars : bool) -> AdmitConstraitsItemMatch {
        AdmitConstraitsItemMatch::Selection(
            AdmitConstraitsSelection { symbols, tuples, match_var: vars }
        )
    }
    fn select_all() -> AdmitConstraitsItemMatch {
        AdmitConstraitsItemMatch::All
    }

    fn bitset_u64(ns : &[u8]) -> u64 {
        let mut acc = 0;
        for each in ns {
            core::debug_assert!(*each < 64);
            acc |= (1 << each)
        }
        acc
    }
    fn bitset_inclusive_range_u64(rs : &[std::ops::RangeInclusive<u8>])->u64 {
        let mut acc = 0;
        for each in rs {
            for each_ in *each.start()..=*each.end() {
                core::debug_assert!(each_ < 64);
                acc |= (1 << each_)
            }
        }
        acc
    }

    #[test]
    fn symbol_test() {
        let s = crate::space::Space::new();
        let e = expr!(s, "\
            [2] admit [2] , [2] $ symbol \
        ");
        let admit_set = build_admit_constraints(e, 0);
        let constraint = admit_set.unwrap().iter().next().unwrap();
        assert_eq!(constraint,
            id_match_bind_nonvar(0, select_symbols_tuples_vars((!0)^1, 0, false), false )
        );
    }

    #[test]
    fn var_test() {
        let s = crate::space::Space::new();
        let e = expr!(s, "\
            [2] admit [2] , [2] $ var \
        ");
        let admit_set = build_admit_constraints(e, 0);
        let constraint = admit_set.unwrap().iter().next().unwrap();
        assert_eq!(constraint,
            id_match_bind_nonvar(0, select_symbols_tuples_vars(0, 0, true), false )
        );
    }

    #[test]
    fn tuple_test() {
        let s = crate::space::Space::new();
        let e = expr!(s, "\
            [2] admit [2] , [2] $ tuple \
        ");
        let admit_set = build_admit_constraints(e, 0);
        let constraint = admit_set.unwrap().iter().next().unwrap();
        assert_eq!(constraint,
            id_match_bind_nonvar(0, select_symbols_tuples_vars(0, !0, false), false )
        );
    }

    #[test]
    fn bind_test() {
        let s = crate::space::Space::new();
        let e = expr!(s, "\
            [4] admit [1] ,               \
                bind  [2] , [2] $ nonvar  \
        ");
        let admit_set = build_admit_constraints(e, 0);
        let constraint = admit_set.unwrap().iter().next().unwrap();
        assert_eq!(constraint,
            id_match_bind_nonvar(0, select_symbols_tuples_vars((!0)^1, 0, false), false )
        );
    }

    #[test]
    fn admit_test(){
        let s = crate::space::Space::new();
        let e = expr!(s, "\
            [4] admit                                     \
                [6] , [4] $ var                           \
                            [3] symbol [2] #   6          \
                                       [3] #.. [2] 1 3    \
                                               [2] 10 15  \
                            [3] tuple  [3] #   4 3        \
                                       [2] #.. [2] 7 9    \
                      [3] $ var                           \
                            [2] symbol [2] #.. [2] 4 6    \
                      [2] [2] $ $ symbol                  \
                      [3] $ symbol tuple                  \
                      [4] $ var symbol tuple              \
                bind                                      \
                [4] , [2] [2] _1 _2   nonvar              \
                      [2] $           nonvar              \
                      [2] $           nonvar              \
        ");
        let admit_set = build_admit_constraints(e, 0);

        let admit_set_collect = admit_set.unwrap().iter().collect::<Vec<_>>();
        assert_eq!(
            &admit_set_collect,
            &[
                id_match_bind_nonvar(
                    0, 
                    select_symbols_tuples_vars(
                        bitset_u64(&[6])    | bitset_inclusive_range_u64(&[1..=3, 10..=15]),
                        bitset_u64(&[4, 3]) | bitset_inclusive_range_u64(&[7..=9]),
                        true), 
                    true
                ),
                id_match_bind_nonvar(
                    1,
                    select_symbols_tuples_vars(
                        bitset_inclusive_range_u64(&[4..=6]), 0, true
                    ),
                    true
                ),
                id_match_bind_nonvar(2, select_symbols_tuples_vars((!0)^1, 0, false), false),
                id_match_bind_nonvar(3, select_symbols_tuples_vars((!0)^1, 0, false), false),
                id_match_bind_nonvar(4, select_symbols_tuples_vars((!0)^1, !0, false), false),
                id_match_bind_nonvar(5, select_symbols_tuples_vars((!0)^1, !0, true), false),
                id_match_bind_nonvar(6, select_all(), true),
                id_match_bind_nonvar(7, select_all(), true),
            ],
        );
    }

    #[test]
    fn hit_errors() {
        let s = crate::space::Space::new();

        macro_rules! hit_error {
            ($EXPR:literal => $ERROR:ident) => {
                let e = expr!(s, $EXPR);
                let admit_set = build_admit_constraints(e, 0);
                if let Err(s) = admit_set { assert_eq!(eval_error_str(s), GRAMMAR[super::AdmitGrammarRule::$ERROR as usize]); }
            };
        }

        hit_error!("[3] admit bind  [2] , [2] $ nonvar"                      => Admit              );
        hit_error!("[2] admity [1] ,"                                        => AdmitDecl          );
        hit_error!("[2] admit [2] , [2] $ [2] symbol [2] # 75"               => Number             );
        hit_error!("[2] admit [2] , [2] $ [2] symbol [2] # 65"               => NumberLargerThan64 );
        hit_error!("[2] admit [2] , [2] $ [2] symbol [2] # 0"                => PNumber            );
        hit_error!("[2] admit [2] , [2] $ [2] tuple [2] # 0"                 => Number             );
        hit_error!("[2] admit [2] , [2] $ [2] symbol [2] #. 0"               => AdmitConstraint    );
        hit_error!("[2] admit [2] , [2] $ [2] symbol [2] # 7 [2] #. [2] 0 3" => PNumberRanges      );
        hit_error!("[2] admit [2] , [2] $ [2] tuple [2] # 7 [2] #. [2] 0 3 " => NumberRanges       );
        hit_error!("[2] admit [2] , [2] $ [2] symbol [2] #.. [3] 0 3 7"      => PNumberRanges      );
        hit_error!("[2] admit [2] , [2] $ [2] tuple [2] #.. [2] 7 1"         => RangeError         );
        hit_error!("[2] admit [2] , [2] $ [2] tuple [2] #.. [2] 0 5"         => PNumber            );
        hit_error!("[2] admit [2] , [2] $ [2] symboly [2] #.. [2] 2 5"       => AdmitConstraint    );
        hit_error!("[4] admit [1] , bind [2] , [3] $ nonvar g"               => BindConstrait      );
        hit_error!("[4] admit [1] , bind [2] , [2] $ nonva"                  => BindConstrait      );
        hit_error!("[4] admit [2] , [2] $ var  bind [2] , [2] $ nonvar"      => UnSat              );
    }
}
