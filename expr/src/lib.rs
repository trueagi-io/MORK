#![cfg_attr(feature = "nightly", allow(internal_features), feature(core_intrinsics))]
#![cfg_attr(feature = "nightly", feature(portable_simd))]
#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "nightly", feature(coroutine_trait))]
#![cfg_attr(feature = "nightly", feature(coroutines))]
#![cfg_attr(feature = "nightly", feature(stmt_expr_attributes))]
#![cfg_attr(feature = "nightly", feature(gen_blocks))]
#![cfg_attr(feature = "nightly", feature(yield_expr))]

#[allow(unused_imports)]
use std::{
    fmt::{format, Debug, Formatter, Write}, 
    mem, 
    ops::{self, ControlFlow}, 
    ptr::{self, null, null_mut, slice_from_raw_parts, slice_from_raw_parts_mut}
};
use std::collections::{BTreeMap, HashMap};
use std::collections::hash_map::Entry;
use std::hash::{Hash, Hasher};
use std::ops::{Coroutine, CoroutineState};
use std::pin::pin;
use smallvec::SmallVec;

pub mod macros;

#[cfg(gxhash)]
use gxhash;

#[cfg(feature="nightly")]
#[path="lib_nightly.rs"]
mod lib_nightly;
#[cfg(feature="nightly")]
pub use lib_nightly::*;

#[cfg(not(gxhash))]
mod gxhash {
    // fallback
    // pub use xxhash_rust::xxh64::{Xxh64 as GxHasher};
    /// Just a simple XOR hasher so miri doesn't explode on all the tests that use GxHash
    #[derive(Clone, Default)]
    pub struct GxHasher { state_lo: u64, state_hi: u64, }
    impl GxHasher {
        pub fn with_seed(seed: i64) -> Self {
            //Reinterpret the bits without any kind of rounding, truncation, extension, etc.
            let seed = u64::from_ne_bytes(seed.to_ne_bytes());
            Self { state_lo: seed ^ 0xA5A5A5A5_A5A5A5A5, state_hi: !seed ^ 0x5A5A5A5A_5A5A5A5A, }
        }
        pub fn finish_u128(&self) -> u128 {
            ((self.state_hi as u128) << 64) | self.state_lo as u128
        }
    }
    impl core::hash::Hasher for GxHasher {
        fn write(&mut self, buf: &[u8]) {
            for &c in buf {
                self.write_u8(c);
            }
        }
        fn write_u8(&mut self, i: u8) {
            self.state_lo = self.state_lo.wrapping_add(i as u64);
            self.state_hi ^= (i as u64).rotate_left(11);
            self.state_lo = self.state_lo.rotate_left(3);
        }
        fn write_u128(&mut self, i: u128) {
            let low = i as u64;
            let high = (i >> 64) as u64;
            self.state_lo = self.state_lo.wrapping_add(low);
            self.state_hi ^= high.rotate_left(17);
            self.state_lo ^= high.rotate_left(9);
        }
        fn finish(&self) -> u64 {
            self.finish_u128() as u64
        }
    }

    pub use std::collections::{HashMap, HashSet};
    pub fn gxhash128(data: &[u8], _seed: i64) -> u128 { xxhash_rust::const_xxh3::xxh3_128(data) }
    pub trait HashMapExt{}
    pub trait HashSetExt{}
}


#[derive(Copy, Clone, Debug)]
pub struct Breadcrumb {
    parent: u32,
    arity: u8,
    seen: u8,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
#[repr(C, u8)]
pub enum Tag {
    NewVar, // $
    VarRef(u8), // _1 .. _63
    SymbolSize(u8), // "" "." ".." .. "... x63"
    //                < 64 bytes
    Arity(u8), // [0] ... [63]
    // U64,
}

// [2] <u64> '8 0 0 0 1 2
// [2] shortStr '19 a d a ...

// [2] <u64> '8 0 0 0 1 2

// [2] 64bytes [2] 64bytes [2] ... [2] 64bytes 64bytes
// [63] 64bytes 64bytes 62x.. 64bytes [63] 64bytes 62x.. 64bytes [63] ... [63] ...

// Discrimination <-> Compression
// High discrimination +speed -memory
// - classify "be unique" as soon as possible
// - bring discriminating information to the front (tags)
// High compression -speed +memory
// - stay shared as long as possible
// - bring shared information to the front (bulk)

#[inline(always)]
pub const fn item_byte(b: Tag) -> u8 {
    match b {
        Tag::NewVar => { 0b1100_0000 | 0 }
        Tag::SymbolSize(s) => { debug_assert!(s > 0 && s < 64); 0b1100_0000 | s }
        Tag::VarRef(i) => { debug_assert!(i < 64); 0b1000_0000 | i }
        Tag::Arity(a) => { debug_assert!(a < 64); 0b0000_0000 | a }
    }
}

#[inline(always)]
pub fn byte_item(b: u8) -> Tag {
    if b == 0b1100_0000 { return Tag::NewVar; }
    else if (b & 0b1100_0000) == 0b1100_0000 { return Tag::SymbolSize(b & 0b0011_1111) }
    else if (b & 0b1100_0000) == 0b1000_0000 { return Tag::VarRef(b & 0b0011_1111) }
    else if (b & 0b1100_0000) == 0b0000_0000 { return Tag::Arity(b & 0b0011_1111) }
    else { panic!("reserved {}", b) }
}

pub const fn maybe_byte_item(b: u8) -> Result<Tag, u8> {
    if b == 0b1100_0000 { return Ok(Tag::NewVar); }
    else if (b & 0b1100_0000) == 0b1100_0000 { return Ok(Tag::SymbolSize(b & 0b0011_1111)) }
    else if (b & 0b1100_0000) == 0b1000_0000 { return Ok(Tag::VarRef(b & 0b0011_1111)) }
    else if (b & 0b1100_0000) == 0b0000_0000 { return Ok(Tag::Arity(b & 0b0011_1111)) }
    else { return Err(b) }
}

// pub fn str_item(ptr: *mut u8) -> (usize, Result<Tag, &[u8]>) {
//     let offset = 0;
//     loop {
//         match unsafe { *ptr.byte_add(offset) } {
//             '[' => {
//                 offset += 1;
//                 let i: u8 = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 0, '1' => 1, '2' => 2, '3' => 3, '4' => 4,
//                     '5' => 5, '6' => 6, '7' => 7, '8' => 8, '9' => 9,
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 i = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 10*i + 0, '1' => 10*i + 1, '2' => 10*i + 2, '3' => 10*i + 3, '4' => 10*i + 4,
//                     '5' => 10*i + 5, '6' => 10*i + 6, '7' => 10*i + 7, '8' => 10*i + 8, '9' => 10*i + 9,
//                     ']' => { return (offset, Ok(Tag::Arity(i))); },
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 match unsafe { *ptr.byte_add(offset) } {
//                     ']' => { return (offset, Ok(Tag::Arity(i))); },
//                     _ => { panic!() }
//                 };
//             }
//             '(' => {
//                 offset += 1;
//                 let i: u8 = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 0, '1' => 1, '2' => 2, '3' => 3, '4' => 4,
//                     '5' => 5, '6' => 6, '7' => 7, '8' => 8, '9' => 9,
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 i = match unsafe { *ptr.byte_add(offset) } {
//                     '0' => 10*i + 0, '1' => 10*i + 1, '2' => 10*i + 2, '3' => 10*i + 3, '4' => 10*i + 4,
//                     '5' => 10*i + 5, '6' => 10*i + 6, '7' => 10*i + 7, '8' => 10*i + 8, '9' => 10*i + 9,
//                     ')' => { return (offset, Ok(Tag::SymbolSize(i))); },
//                     _ => { panic!() }
//                 };
//                 offset += 1;
//                 match unsafe { *ptr.byte_add(offset) } {
//                     ')' => { return (offset, Ok(Tag::SymbolSize(i))); },
//                     _ => { panic!() }
//                 };
//             }
//         }
//     }
// }

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Expr {
    pub ptr: *mut u8,
}

#[derive(Clone, Debug)]
pub enum ExtractFailure {
    IntroducedVar(),
    RecurrentVar(u8),
    RefMismatch(u8, u8),
    RefSymbolEarlyMismatch(u8, u8, u8),
    RefSymbolMismatch(u8, Vec<u8>, Vec<u8>),
    RefTypeMismatch(u8, Tag, Tag),
    RefExprEarlyMismatch(u8, u8, u8),
    RefExprMismatch(u8, Vec<u8>, Vec<u8>),
    ExprEarlyMismatch(u8, u8),
    SymbolEarlyMismatch(u8, u8),
    SymbolMismatch(Vec<u8>, Vec<u8>),
    TypeMismatch(Tag, Tag)
}
use ExtractFailure::*;

#[macro_export]
macro_rules! traverse {
    ($t1:ty, $t2:ty, $x:expr, $new_var:expr, $var_ref:expr, $symbol:expr, $zero:expr, $add:expr, $finalize:expr) => {{
        struct AnonTraversal {}
        impl Traversal<$t1, $t2> for AnonTraversal {
            #[inline(always)] fn new_var(&mut self, offset: usize) -> $t2 { ($new_var)(offset) }
            #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> $t2 { ($var_ref)(offset, i) }
            #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> $t2 { ($symbol)(offset, s) }
            #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> $t1 { ($zero)(offset, a) }
            #[inline(always)] fn add(&mut self, offset: usize, acc: $t1, sub: $t2) -> $t1 { ($add)(offset, acc, sub) }
            #[inline(always)] fn finalize(&mut self, offset: usize, acc: $t1) -> $t2 { ($finalize)(offset, acc) }
        }

        execute_loop(&mut AnonTraversal{}, $x, 0).1
    }};
}

#[macro_export]
macro_rules! traverseh {
    ($t1:ty, $t2:ty, $t3:ty, $x:expr, $v0:expr, $new_var:expr, $var_ref:expr, $symbol:expr, $zero:expr, $add:expr, $finalize:expr) => {{
    let mut h: $t3 = $v0;
    struct State<X> { iter: u8, payload: X }
    let mut stack: SmallVec<[State<$t1>; 8]> = SmallVec::new();
    // let mut stack = vec![];
    let mut j: usize = 0;
    let value = 'putting: loop {
        let mut value = match unsafe { byte_item(*$x.ptr.byte_add(j)) } {
            Tag::NewVar => { j += 1; ($new_var)(&mut h, j - 1) }
            Tag::VarRef(r) => { j += 1; ($var_ref)(&mut h, j - 1, r) }
            Tag::SymbolSize(s) => {
                let slice = unsafe { &*slice_from_raw_parts($x.ptr.byte_add(j + 1), s as usize) };
                let v = ($symbol)(&mut h, j, slice);
                j += s as usize + 1;
                v
            }
            Tag::Arity(a) => {
                let acc = ($zero)(&mut h, j, a);
                j += 1;
                if a == 0 {
                    ($finalize)(&mut h, j, acc)
                } else {
                    stack.push(State{ iter: a, payload: acc });
                    continue 'putting;
                }
            }
        };

        'popping: loop {
            match stack.last_mut() {
                None => { break 'putting value }
                Some(&mut State{ iter: ref mut k, payload: ref mut acc }) => {
                    unsafe {
                        std::ptr::write(k, std::ptr::read(k).wrapping_sub(1));
                        std::ptr::write(acc, ($add)(&mut h, j, std::ptr::read(acc), value));
                        if std::ptr::read(k) != 0 { continue 'putting }
                    }
                }
            }

            value = match stack.pop() {
                Some(State{ iter: _, payload: acc }) => ($finalize)(&mut h, j, acc),
                None => break 'popping
            }
        }
    };
    (h, value, j)
    }}
}

impl Expr {
    pub fn symbol(self) -> Option<*const [u8]> {
        unsafe {
        if let Tag::SymbolSize(n) = byte_item(*self.ptr) { Some(slice_from_raw_parts(self.ptr.offset(1), n as usize)) }
        else { None }
        }
    }

    pub fn arity(self) -> Option<u8> {
        unsafe {
            if let Tag::Arity(n) = byte_item(*self.ptr) { Some(n) }
            else { None }
        }
    }

    pub fn span(self) -> *const [u8] {
        if self.ptr.is_null() { slice_from_raw_parts(null(), 0) }
        else {
            let mut ez = ExprZipper::new(self);
            loop {
                if !ez.next() {
                    return ez.finish_span();
                }
            }
        }
    }

    pub fn hash(self) -> u128 {
        let s = unsafe { self.span().as_ref().unwrap() };
        gxhash::gxhash128(s, 0)
    }

    pub fn size(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 1, |_, _| 1, |_, _| 1, |_, x, y| x + y, |_, x| x)
    }

    pub fn leaves(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 1, |_, _| 1, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn expressions(self) -> usize {
        traverse!(usize, usize, self, |_| 0, |_, _| 0, |_, _| 0, |_, _| 1, |_, x, y| x + y, |_, x| x)
    }

    pub fn symbols(self) -> usize {
        traverse!(usize, usize, self, |_| 0, |_, _| 0, |_, _| 1, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn newvars(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 0, |_, _| 0, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn references(self) -> usize {
        traverse!(usize, usize, self, |_| 0, |_, _| 1, |_, _| 0, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn forward_references(self, at: u8) -> usize {
        traverseh!(usize, usize, u64, self, if at > 0 { (!0u64) >> (64 - at) } else { 0 },
            |c: &mut u64, _| { *c |= 1u64 << ((*c).trailing_ones()); 0 }, |c: &mut u64, _, r| if (1u64 << r) & *c == 0 { *c |= 1u64 << r; 1 } else { 0 }, |_, _, _| 0, |_, _, _| 0, |_, _, x, y| x + y, |_, _, x| x).1
    }

    pub fn variables(self) -> usize {
        traverse!(usize, usize, self, |_| 1, |_, _| 1, |_, _| 0, |_, _| 0, |_, x, y| x + y, |_, x| x)
    }

    pub fn max_arity(self) -> Option<u8> {
        traverse!(u8, Option<u8>, self, |_| None, |_, _| None, |_, _| None, |_, a| a, |_, x, y: Option<u8>| u8::max(x, y.unwrap_or(0)), |_, x| Some(x))
    }

    pub fn has_unbound(self) -> bool {
        // Doesn't work for some odd reason
        // std::panic::catch_unwind(|| traverseh!((), (), u8, self, 0,
        //     |c: &mut u8, _| { *c += 1; }, |c: &mut u8, _, r| { if r >= *c { panic!(); } }, |_, _, _| (), |_, _, _| (), |_, _, _, _| (), |_, _, _| ())
        // ).is_err()
        // traverseh!(ops::ControlFlow<(), ()>, ops::ControlFlow<(), ()>, u8, self, 0,
        //     |c: &mut u8, _| { *c += 1; ControlFlow::Continue(()) }, |c: &mut u8, _, r| { if r >= *c { ControlFlow::Break(()) } else { ControlFlow::Continue(()) } }, |_, _, _| ControlFlow::Continue(()), |_, _, _| ControlFlow::Continue(()), |_, _, l, r| { r?; l }, |_, _, l| l).1.is_break()
        traverseh!(bool, bool, u8, self, 0,
            |c: &mut u8, _| { *c += 1; false }, |c: &mut u8, _, r| r >= *c, |_, _, _| false, |_, _, _| false, |_, _, x, y| x || y, |_, _, x| x).1
    }

    pub fn difference(self, other: Expr) -> Option<usize> {
        let mut ez = ExprZipper::new(self);
        let mut oz = ExprZipper::new(other);
        loop {
            if ez.item() != oz.item() {
                return Some(ez.loc)
            }

            if !ez.next() {
                return None
            }
            assert!(oz.next())
        }
    }

    pub fn difference_under<F : Fn(Expr, Expr) -> bool>(self, other: Expr, under: F) -> Option<usize> {
        let mut ez = ExprZipper::new(self);
        let mut oz = ExprZipper::new(other);
        loop {
            if ez.item() != oz.item() {
                return Some(ez.loc)
            }

            if !ez.next() {
                return None
            }
            assert!(oz.next())
        }
    }

    pub fn prefix(self) -> Result<*const [u8], *const [u8]> {
        use ControlFlow::*;
        match traverse!(ControlFlow<usize, usize>, ControlFlow<usize, usize>, self,
            |o| Break(o), |o, _| Break(o), |o, _| Continue(o), |o, _| Continue(o), |_, a, n| { a?; n }, |_, a| a) {
            Break(offset) => { Ok(slice_from_raw_parts(self.ptr, offset)) } // proper prefix
            Continue(offset) => { Err(slice_from_raw_parts(self.ptr, offset)) } // full expr
        }
    }
    
    pub fn substitute(self, substitutions: &[Expr], oz: &mut ExprZipper) -> *const [u8] {
        let mut ez = ExprZipper::new(self);
        let mut var_count = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    match unsafe { substitutions[var_count].span().as_ref() } {
                        None => { oz.write_new_var(); oz.loc += 1; }
                        Some(r) => { oz.write_move(r); }
                    }
                    var_count += 1;
                 }
                Tag::VarRef(r) => {
                    match unsafe { substitutions[r as usize].span().as_ref() } {
                        None => { oz.write_var_ref(r); oz.loc += 1; }
                        Some(r) => { oz.write_move(r); }
                    }
                }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }

    pub fn equate_var(self, new_var: u8, refer_to: u8, oz: &mut ExprZipper) -> *const [u8] {
        assert!(new_var > refer_to);
        let mut ez = ExprZipper::new(self);
        let mut var_count = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    if new_var == var_count {
                        oz.write_var_ref(refer_to);
                        oz.loc += 1;
                    } else {
                        oz.write_new_var();
                        oz.loc += 1;
                    }
                    var_count += 1;
                }
                Tag::VarRef(r) => {
                    if new_var == r {
                        oz.write_var_ref(refer_to);
                        oz.loc += 1;
                    } else if r > new_var {
                        oz.write_var_ref(r - 1);
                        oz.loc += 1;
                    } else {
                        oz.write_var_ref(r);
                        oz.loc += 1;
                    }
                }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }

    pub fn equate_var_inplace(self, new_var: u8, refer_to: u8) -> *const [u8] {
        assert!(new_var >= refer_to);
        let mut ez = ExprZipper::new(self);
        let mut var_count = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    if new_var == var_count {
                        ez.write_var_ref(refer_to);
                    }
                    var_count += 1;
                }
                Tag::VarRef(r) => {
                    if new_var == r {
                        ez.write_var_ref(refer_to);
                    } else if r > new_var {
                        ez.write_var_ref(r - 1);
                    }
                }
                Tag::SymbolSize(_s) => {  }
                Tag::Arity(_) => {  }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }

    pub fn equate_vars_inplace(self, refers: &mut [u8]) {
        let mut ez = ExprZipper::new(self);
        let mut var_count = 0;
        let mut bound = 0;
        // println!("refers {:?}", refers);
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    if refers[var_count] != 0xffu8 {
                        ez.write_var_ref(refers[var_count]);
                        bound += 1;
                    } else {
                        refers[var_count] = var_count as u8 - bound;
                    }
                    var_count += 1;
                }
                Tag::VarRef(r) => {
                    if refers[r as usize] != 0xffu8 {
                        ez.write_var_ref(refers[r as usize]);
                    } else {
                        // unreachable!()
                    }
                }
                Tag::SymbolSize(_s) => {  }
                Tag::Arity(_) => {  }
            }

            if !ez.next() {
                return
            }
        }
    }

    pub fn substitute_one_de_bruijn(self, idx: u8, substitution: Expr, oz: &mut ExprZipper) -> *const [u8] {
        let mut var: u8 = item_byte(Tag::NewVar);
        let nvs = self.newvars();
        let mut vars = vec![Expr{ ptr: &mut var }; nvs];
        vars[idx as usize] = substitution;
        self.substitute_de_bruijn(&vars[..], oz)
    }

    pub fn substitute_de_bruijn_ivc(self, substitutions: &[Expr], oz: &mut ExprZipper, var_count: &mut usize, additions: &mut [u8]) -> *const [u8] {
        let mut ez = ExprZipper::new(self);
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    let nvars = substitutions[*var_count].shift(additions[*var_count], oz);
                    *var_count += 1;
                    // ideally this is something like `_mm512_mask_add_epi8(additions, ~0 << var_count, _mm512_set1_epi8(nvars), additions)`
                    // TODO reference parent and get count that way, future additions don't need to happen yet
                    for j in *var_count..additions.len() { additions[j] += nvars; }
                }
                Tag::VarRef(r) => {
                    substitutions[r as usize].bind(additions[r as usize], oz);
                }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }
    
    pub fn substitute_de_bruijn(self, substitutions: &[Expr], oz: &mut ExprZipper) -> *const [u8] {
        let mut ez = ExprZipper::new(self);
        let mut additions = vec![0u8; substitutions.len()];
        let mut var_count = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    let nvars = substitutions[var_count].shift(additions[var_count], oz);
                    var_count += 1;
                    // ideally this is something like `_mm512_mask_add_epi8(additions, ~0 << var_count, _mm512_set1_epi8(nvars), additions)`
                    // TODO reference parent and get count that way, future additions don't need to happen yet
                    for j in var_count..additions.len() { additions[j] += nvars; }
                }
                Tag::VarRef(r) => {
                    substitutions[r as usize].bind(additions[r as usize], oz);
                }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }


    fn bind(self, n: u8, oz: &mut ExprZipper) -> *const [u8] {
        // this.foldMap(i => Var(if i == 0 then {index += 1; -index - n} else if i > 0 then i else i - n), App(_, _))
        let mut ez = ExprZipper::new(self);
        let mut var_count = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => {
                    oz.write_var_ref(n + var_count); oz.loc += 1; var_count += 1;
                }
                Tag::VarRef(i) => {
                    oz.write_var_ref(n + i); oz.loc += 1; // good
                }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }

    pub fn shift(self, n: u8, oz: &mut ExprZipper) -> u8 {
        // this.foldMap(i => Var(if i >= 0 then i else i - n), App(_, _))
        let mut ez = ExprZipper::new(self);
        let mut new_var = 0u8;
        loop {
            match ez.tag() {
                Tag::NewVar => { oz.write_new_var(); oz.loc += 1; new_var += 1; }
                Tag::VarRef(i) => { oz.write_var_ref(i + n); oz.loc += 1; }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                // return self.loc + match self.tag() {
                //     Tag::NewVar => { 1 }
                //     Tag::VarRef(r) => { 1 }
                //     Tag::SymbolSize(s) => { 1 + (s as usize) }
                //     Tag::Arity(a) => { unreachable!() /* expression can't end in arity */ }
                // }
                return new_var;
            }
        }
    }

    pub fn unbind(self, oz: &mut ExprZipper) -> *const [u8] {
        let mut ez = ExprZipper::new(self);
        let mut bound = [255; 64];
        let mut nvars = 0;
        loop {
            match ez.tag() {
                Tag::NewVar => { oz.write_new_var(); oz.loc += 1; nvars += 1; }
                Tag::VarRef(i) => {
                    if (i as usize) < nvars || bound[i as usize] != 255 { oz.write_var_ref(bound[i as usize]); oz.loc += 1; }
                    else { oz.write_new_var(); bound[i as usize] = nvars as u8; nvars += 1; oz.loc += 1; }
                }
                Tag::SymbolSize(s) => { oz.write_move(unsafe { slice_from_raw_parts(ez.root.ptr.byte_add(ez.loc), s as usize + 1).as_ref().unwrap() }); }
                Tag::Arity(_) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
            }

            if !ez.next() {
                return ez.finish_span()
            }
        }
    }

    /// First-order syntactic anti-unification (least general generalization).
    ///
    /// Writes the generalization into `o`.
    /// Returns substitutions mapping each introduced generalization var to the original subterms.
    pub fn anti_unify(self, other: Expr, o: &mut ExprZipper) -> Result<(), AntiUnificationFailure> {
        let mut st = AuState {
            next_var: 0,
            memo: HashMap::new(),
            left: BTreeMap::new(),
            right: BTreeMap::new(),
        };

        anti_unify_apply(ExprEnv::new(0, self), ExprEnv::new(1, other), o, &mut st)?;

        Ok(())
    }

    // fn anti_unify<W : std::io::Write>(self, other: Expr, w: &mut W) {
    //     let mut se = item_source(self);
    //     let mut oe = item_source(other);
    //     let mut re = item_sink(w);
    //
    //     let mut differences: HashMap<(ExprEnv, ExprEnv), u8> = HashMap::new();
    //     let mut nvars = 0;
    //     loop {
    //         match (pin!(&mut se).resume(()), pin!(&mut oe).resume(()))  {
    //             (CoroutineState::Yielded(si), CoroutineState::Yielded(oi)) => {
    //                 match (si, oi) {
    //                     (SourceItem::Symbol(ss), SourceItem::Symbol(os)) => {
    //                         if ss == os { pin!(&mut re).resume(si); }
    //                         else {
    //                             unreachable!()
    //                             // match differences.entry(ss) {
    //                             //     Entry::Occupied(oe) => {
    //                             //         pin!(&mut re).resume(SourceItem::Tag(Tag::VarRef(oe.get().0)));
    //                             //     }
    //                             //     Entry::Vacant(ve) => {
    //                             //         ve.insert((nvars, os));
    //                             //         nvars += 1;
    //                             //         pin!(&mut re).resume(SourceItem::Tag(Tag::NewVar));
    //                             //     }
    //                             // }
    //                         }
    //                     }
    //                     _ => unreachable!()
    //                 }
    //             }
    //             _ => unreachable!()
    //         }
    //     }
    // }

    #[inline(never)]
    pub fn unifiable(self, other: Expr) -> bool {
        let mut s = vec![(ExprEnv::new(0, self), ExprEnv::new(1, other))];

        unify(s).is_ok()
    }

    pub fn unify(self, other: Expr, o: &mut ExprZipper) -> Result<(), UnificationFailure> {
        let mut s = vec![(ExprEnv::new(0, self), ExprEnv::new(1, other))];

        match unify(s) {
            Ok(bindings) => {
                let mut cycled = BTreeMap::<(u8, u8), u8>::new();
                let mut stack: Vec<(u8, u8)> = vec![];
                let mut assignments: Vec<(u8, u8)> = vec![];
                apply(0, 0, 0, &mut ExprZipper::new(self), &bindings, o, &mut cycled, &mut stack, &mut assignments);
                Ok(())
            }
            Err(f) => Err(f)
        }
    }

    #[allow(non_snake_case)]
    pub fn transformData(self, pattern: Expr, template: Expr, oz: &mut ExprZipper) -> Result<(), ExtractFailure> {
        let mut ez = ExprZipper::new(self);
        match pattern.extract_data(&mut ez) {
            Ok(ref bindings) => { template.substitute(bindings, oz); Ok(()) }
            Err(e) => { Err(e) }
        }
    }

    pub fn transformed(self, template: Expr, pattern: Expr) -> Result<Expr, ExtractFailure> {
        let mut transformation = vec![item_byte(Tag::Arity(2))];
        transformation.extend_from_slice(unsafe { template.span().as_ref().unwrap() });
        transformation.extend_from_slice(unsafe { pattern.span().as_ref().unwrap() });
        let mut data = vec![item_byte(Tag::Arity(2)), item_byte(Tag::NewVar)];
        data.extend_from_slice(unsafe { self.span().as_ref().unwrap() });
        unsafe {
            let e = Expr{ ptr: data.as_mut_ptr().add(2)};
            e.shift(1, &mut ExprZipper::new(e));
        }
        // println!("lhs {:?}", Expr{ ptr: transformation.as_mut_ptr() });
        // println!("rhs {:?}", Expr{ ptr: data.as_mut_ptr() });
        let o = Expr{ ptr: vec![0; 512].leak().as_mut_ptr() };
        let x = Expr{ ptr: transformation.as_mut_ptr() };
        let y = Expr{ ptr: data.as_mut_ptr() };
        let mut s = vec![(ExprEnv::new(0, x), ExprEnv::new(1, y))];
        
        if let Ok(bindings) = unify(s) {
            let mut cycled = BTreeMap::<ExprVar, u8>::new();
            let mut stack: Vec<ExprVar> = vec![];
            let mut assignments: Vec<ExprVar> = vec![];
            apply(0, 0, 0, &mut ExprZipper::new(Expr{ ptr: transformation.as_mut_ptr() }), &bindings, &mut ExprZipper::new(o), &mut cycled, &mut stack, &mut assignments);
            Ok(Expr { ptr: unsafe { o.ptr.byte_add(1) } })
        } else {
            Err(ExtractFailure::ExprEarlyMismatch(0, 0))
        }
    }

    pub fn extract_data(self, iz: &mut ExprZipper) -> Result<Vec<Expr>, ExtractFailure> {
        let mut ez = ExprZipper::new(self);
        let mut bindings: Vec<Expr> = vec![];
        loop {
            match (ez.tag(), iz.tag()) {
                (_, Tag::NewVar) => { return Err(IntroducedVar()) }
                (_, Tag::VarRef(r)) => { return Err(RecurrentVar(r)) }
                (Tag::NewVar, Tag::SymbolSize(_)) => { bindings.push(iz.subexpr()); iz.next(); if !ez.next() { return Ok(bindings) }; }
                (Tag::NewVar, Tag::Arity(_a)) => { bindings.push(iz.subexpr());

                    let mut ez1 = ExprZipper::new(iz.subexpr());
                    let x = loop {
                        if !ez1.next() {
                            break ez1.finish_span();
                        }
                    };

                    iz.loc += (unsafe { x.as_ref().unwrap() }).len();

                    if !ez.next() { return Ok(bindings) }; }
                (Tag::VarRef(i), Tag::SymbolSize(s)) => {
                    if let Tag::SymbolSize(s_) = unsafe { byte_item(*bindings[i as usize].ptr) } {
                        if s != s_ { return Err(RefSymbolEarlyMismatch(i, s, s_)) }
                        let aslice = unsafe { &*slice_from_raw_parts(bindings[i as usize].ptr.byte_add(1), s_ as usize) };
                        let bslice = unsafe { &*slice_from_raw_parts(iz.subexpr().ptr.byte_add(1), s as usize) };
                        if aslice != bslice { return Err(RefSymbolMismatch(i, aslice.to_vec(), bslice.to_vec())) }
                        iz.next(); if !ez.next() { return Ok(bindings) };
                    } else {
                        return Err(RefTypeMismatch(i, ez.tag(), iz.tag()))
                    }
                }
                (Tag::VarRef(i), Tag::Arity(s)) => {
                    println!("{:?} as template for {:?}", self, iz.root);
                    println!("checking _{} against [{}]", i+1, s);
                    if let Tag::Arity(s_) = unsafe { byte_item(*bindings[i as usize].ptr) } {
                        if s != s_ { return Err(RefExprEarlyMismatch(i, s, s_)) }
                        // TODO this is quite wasteful: neither span should be re-calculated
                        let aslice = unsafe { &*bindings[i as usize].span() };
                        let bslice = unsafe { &*iz.subexpr().span() };
                        if aslice != bslice { return Err(RefExprMismatch(i, aslice.to_vec(), bslice.to_vec())) }
                        iz.next(); if !ez.next() { return Ok(bindings) };
                    } else {
                        return Err(RefTypeMismatch(i, ez.tag(), iz.tag()))
                    }
                }
                (Tag::SymbolSize(a), Tag::SymbolSize(b)) => {
                    if a != b { return Err(SymbolEarlyMismatch(a, b)) }
                    let aslice = unsafe { &*slice_from_raw_parts(ez.subexpr().ptr.byte_add(1), a as usize) };
                    let bslice = unsafe { &*slice_from_raw_parts(iz.subexpr().ptr.byte_add(1), b as usize) };
                    if aslice != bslice { return Err(SymbolMismatch(aslice.to_vec(), bslice.to_vec())) }
                    iz.next(); if !ez.next() { return Ok(bindings) };
                }
                (Tag::Arity(a), Tag::Arity(b)) => {
                    if a != b { return Err(ExprEarlyMismatch(a, b)) }
                    iz.next(); if !ez.next() { return Ok(bindings) };
                }
                _ => { return Err(TypeMismatch(ez.tag(), iz.tag())) }
            }
        }
    }

    pub fn substitute_symbols<F : for <'a> FnMut(&'a [u8]) -> &'a [u8]>(self, oz: &mut ExprZipper, mut subst: F) -> *mut [u8] {
        let mut ez = ExprZipper::new(self);
        loop {
            match ez.item() {
                Ok(Tag::NewVar) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
                Ok(Tag::VarRef(_i)) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
                Ok(Tag::SymbolSize(_s)) => { unreachable!() }
                Ok(Tag::Arity(_)) => { unsafe { *oz.root.ptr.byte_add(oz.loc) = *ez.root.ptr.byte_add(ez.loc); oz.loc += 1; }; }
                Err(s) => { let ns = subst(s); oz.write_symbol(ns); oz.loc += 1 + ns.len(); }
            }

            if !ez.next() {
                return slice_from_raw_parts_mut(oz.root.ptr, oz.loc);
            }
        }
    }

    #[inline(never)]
    pub fn string(&self) -> String {
        let mut traversal = DebugTraversal{ string: String::new(), transient: false };
        execute_loop(&mut traversal, *self, 0);
        traversal.string
    }

    #[inline(never)]
    pub fn serialize<Target : std::io::Write, F : for <'a> Fn(&'a [u8]) -> &'a str>(&self, t: &mut Target, map_symbol: F) -> () {
        let mut traversal = SerializerTraversal{ out: t, map_symbol: map_symbol, transient: false };
        execute_loop(&mut traversal, *self, 0);
    }

    // pub const VARNAMES: [&'static str; 64] = ["$x0", "$x1", "$x2", "$x3", "$x4", "$x5", "$x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "x30", "x31", "x32", "x33", "x34", "x35", "x36", "x37", "x38", "x39", "x40", "x41", "x42", "x43", "x44", "x45", "x46", "x47", "x48", "x49", "x50", "x51", "x52", "x53", "x54", "x55", "x56", "x57", "x58", "x59", "x60", "x61", "x62", "x63"];
    pub const VARNAMES: [&'static str; 64] = ["$a", "$b", "$c", "$d", "$e", "$f", "$g", "$h", "$i", "$j", "$x10", "$x11", "$x12", "$x13", "$x14", "$x15", "$x16", "$x17", "$x18", "$x19", "$x20", "$x21", "$x22", "$x23", "$x24", "$x25", "$x26", "$x27", "$x28", "$x29", "$x30", "$x31", "$x32", "$x33", "$x34", "$x35", "$x36", "$x37", "$x38", "$x39", "$x40", "$x41", "$x42", "$x43", "$x44", "$x45", "$x46", "$x47", "$x48", "$x49", "$x50", "$x51", "$x52", "$x53", "$x54", "$x55", "$x56", "$x57", "$x58", "$x59", "$x60", "$x61", "$x62", "$x63"];

    #[inline(never)]
    pub fn serialize2<Target : std::io::Write, F : for <'a> Fn(&'a [u8]) -> &'a str, G : Fn(u8, bool) -> &'static str>(&self, t: &mut Target, map_symbol: F, map_variable: G) -> () {
        let mut traversal = SerializerTraversal2{ out: t, map_symbol: map_symbol, map_variable: map_variable, transient: false, n: 0 };
        execute_loop(&mut traversal, *self, 0);
    }

    #[inline(never)]
    pub fn serialize_highlight<Target : std::io::Write, F : for <'a> Fn(&'a [u8]) -> &'a str, G : Fn(u8, bool) -> &'static str>(&self, t: &mut Target, map_symbol: F, map_variable: G, target: usize) -> () {
        let mut targets = [(target, "\x1B[43m", "\x1B[0m")].repeat(10); // FIXE
        let mut traversal = SerializerTraversalHighlights{ out: t, map_symbol: map_symbol, map_variable: map_variable, transient: false, n: 0, targets: &targets };
        execute_loop(&mut traversal, *self, 0);
    }

    /// Returns `true` if an [`Expr`] has no vars or refs
    pub fn is_ground(self)->bool {
        self.variables() == 0
    }
}

pub trait Traversal<A, R> {
    fn new_var(&mut self, offset: usize) -> R;
    fn var_ref(&mut self, offset: usize, i: u8) -> R;
    fn symbol(&mut self, offset: usize, s: &[u8]) -> R;
    fn zero(&mut self, offset: usize, a: u8) -> A;
    fn add(&mut self, offset: usize, acc: A, sub: R) -> A;
    fn finalize(&mut self, offset: usize, acc: A) -> R;
}

pub struct PairTraversal<A1, A2, R1, R2, T1, T2> { t1: T1, t2: T2, pd: std::marker::PhantomData<(A1, A2, R1, R2)> }

impl <A1, A2, R1, R2, T1 : Traversal<A1, R1>, T2 : Traversal<A2, R2>> Traversal<(A1, A2), (R1, R2)> for PairTraversal<A1, A2, R1, R2, T1, T2> {
    fn new_var(&mut self, offset: usize) -> (R1, R2) { (self.t1.new_var(offset), self.t2.new_var(offset)) }
    fn var_ref(&mut self, offset: usize, i: u8) -> (R1, R2) { (self.t1.var_ref(offset, i), self.t2.var_ref(offset, i)) }
    fn symbol(&mut self, offset: usize, s: &[u8]) -> (R1, R2) { (self.t1.symbol(offset, s), self.t2.symbol(offset, s)) }
    fn zero(&mut self, offset: usize, a: u8) -> (A1, A2) { (self.t1.zero(offset, a), self.t2.zero(offset, a)) }
    fn add(&mut self, offset: usize, acc: (A1, A2), sub: (R1, R2)) -> (A1, A2) { (self.t1.add(offset, acc.0, sub.0), self.t2.add(offset, acc.1, sub.1)) }
    fn finalize(&mut self, offset: usize, acc: (A1, A2)) -> (R1, R2) { (self.t1.finalize(offset, acc.0), self.t2.finalize(offset, acc.1)) }
}

#[allow(unused)]
fn execute<A, R, T : Traversal<A, R>>(t: &mut T, e: Expr, i: usize) -> (usize, R) {
    match unsafe { byte_item(*e.ptr.byte_add(i)) } {
        Tag::NewVar => { (1, t.new_var(i)) }
        Tag::VarRef(r) => { (1, t.var_ref(i, r)) }
        Tag::SymbolSize(s) => {
            let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(i + 1), s as usize) };
            (s as usize + 1, t.symbol(i, slice))
        }
        Tag::Arity(a) => {
            let mut offset = 1;
            let mut acc = t.zero(i, a);
            for k in 0..a {
                let (d, r) = execute(t, e, i + offset);
                acc = t.add(i + offset, acc, r);
                offset += d;
            }
            (offset, t.finalize(i + offset, acc))
        }
    }
}

pub fn execute_loop<A, R, T : Traversal<A, R>>(t: &mut T, e: Expr, i: usize) -> (usize, R) {
    // example run with e = [3] a [2] x y [2] p q
    // 3 zero()
    // value = symbol(a); 2 add(zero(), symbol(a))
    // 2 add(zero(), symbol(a)), 2 zero()
    // value = symbol(x); 2 add(zero(), symbol(a)), 1 add(zero(), symbol(x))
    // value = symbol(y); 2 add(zero(), symbol(a)); value = finalize(add(add(zero(), symbol(x)), symbol(y))); 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y))))
    // 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y)))), 2 zero()
    // value = symbol(p); 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y)))), 1 add(zero(), symbol(p))
    // value = symbol(q); 1 add(add(zero(), symbol(a)), finalize(add(add(zero(), symbol(x)), symbol(y)))); value = finalize(add(add(zero(), symbol(p)), symbol(q))); value = finalize(add(..., ...)); return
    struct State<X> { iter: u8, payload: X }
    let mut stack: SmallVec<[State<A>; 8]> = SmallVec::new();
    // let mut stack = vec![];
    let mut j = i;
    'putting: loop {
        let mut value = match unsafe { byte_item(*e.ptr.byte_add(j)) } {
            Tag::NewVar => { j += 1; t.new_var(j - 1) }
            Tag::VarRef(r) => { j += 1; t.var_ref(j - 1, r) }
            Tag::SymbolSize(s) => {
                let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(j + 1), s as usize) };
                let v = t.symbol(j, slice);
                j += s as usize + 1;
                v
            }
            Tag::Arity(a) => {
                let acc = t.zero(j, a);
                j += 1;
                if a == 0 {
                    t.finalize(j, acc)
                } else {
                    stack.push(State{ iter: a, payload: acc });
                    continue 'putting;
                }
            }
        };

        'popping: loop {
            match stack.last_mut() {
                None => { return (j, value) }
                Some(&mut State{ iter: ref mut k, payload: ref mut acc }) => {
                    unsafe {
                        std::ptr::write(k, std::ptr::read(k).wrapping_sub(1));
                        std::ptr::write(acc, t.add(j, std::ptr::read(acc), value));
                        if std::ptr::read(k) != 0 { continue 'putting }
                    }
                }
            }

            value = match stack.pop() {
                Some(State{ iter: _, payload: acc }) => t.finalize(j, acc),
                None => break 'popping
            }
        }
    }
}

// functor same -> functor arguments -> call recursively
// unify(f(a b), f(p, q)) -> unify(a, p) /\ unify(b, q)
// unify(f(g(1, A), b), f(g(1, p), q)) -> unify(A, p) /\ unify(b, q)
fn match2<F : FnMut(&mut T1, Expr, usize, &mut T2, Expr, usize),
    A1, R1, T1 : Traversal<A1, R1>,
    A2, R2, T2 : Traversal<A2, R2>>(t1: &mut T1, e1: Expr, i1: usize,
                                    t2: &mut T2, e2: Expr, i2: usize, hole: &mut F) -> Result<(usize, R1, usize, R2), (usize, usize)> {
    match unsafe { (byte_item(*e1.ptr.byte_add(i1)), byte_item(*e2.ptr.byte_add(i2))) } {
        (b1 @ (Tag::NewVar | Tag::VarRef(_)), _) => {
            hole(t1, e1, i1, t2, e2, i2);
            let r1 = if let Tag::VarRef(k1) = b1 { t1.var_ref(i1, k1) } else { t1.new_var(i1) };
            let (d2, r2) = execute_loop(t2, e2, i2);
            Ok((1, r1, d2 - i2, r2))
        }
        (_, b2 @ (Tag::NewVar | Tag::VarRef(_))) => {
            hole(t1, e1, i1, t2, e2, i2);
            let r2 = if let Tag::VarRef(k2) = b2 { t2.var_ref(i2, k2) } else { t2.new_var(i2) };
            let (d1, r1) = execute_loop(t1, e1, i1);
            Ok((d1 - i1, r1, 1, r2))
        }
        (Tag::SymbolSize(s1), Tag::SymbolSize(s2)) if s1 == s2 => {
            let slice1 = unsafe { &*slice_from_raw_parts(e1.ptr.byte_add(i1 + 1), s1 as usize) };
            let slice2 = unsafe { &*slice_from_raw_parts(e2.ptr.byte_add(i2 + 1), s2 as usize) };
            if slice1 != slice2 { Err((i1, i2)) }
            else {
                let d = s1 as usize + 1;
                let r1 = t1.symbol(i1, slice1);
                let r2 = t2.symbol(i2, slice2);
                Ok((d, r1, d, r2))
            }
        }
        (Tag::Arity(a1), Tag::Arity(a2)) if a1 == a2 => {
            let mut offset1 = 1;
            let mut offset2 = 1;
            let mut acc1 = t1.zero(i1, a1);
            let mut acc2 = t2.zero(i2, a2);
            for k in 0..a1 {
                let (d1, r1, d2, r2) = match2(t1, e1, i1 + offset1, t2, e2, i2 + offset2, hole)?;
                acc1 = t1.add(i1 + offset1, acc1, r1);
                acc2 = t2.add(i2 + offset2, acc2, r2);
                offset1 += d1;
                offset2 += d2;
            }
            let r1 = t1.finalize(i1 + offset1, acc1);
            let r2 = t2.finalize(i2 + offset2, acc2);
            Ok((offset1, r1, offset2, r2))
        }
        _ => { Err((i1, i2)) }
    }
}

enum Remaining {
    None,
    
}

pub fn execute_loop_truncated<A, R, T : Traversal<A, R>>(t: &mut T, e: Expr, m: usize) -> Result<(usize, R), (Vec<(u8, A)>, u8)> {
let mut stack: Vec<(u8, A)> = Vec::with_capacity(8);
    let mut j = 0;
    'putting: loop {
        if j == m { return Err((stack, 0u8)) }
        let mut value = match unsafe { byte_item(*e.ptr.byte_add(j)) } {
            Tag::NewVar => { j += 1; t.new_var(j - 1) }
            Tag::VarRef(r) => { j += 1; t.var_ref(j - 1, r) }
            Tag::SymbolSize(s) => {
                // if j <
                let slice = unsafe { &*slice_from_raw_parts(e.ptr.byte_add(j + 1), s as usize) };
                let v = t.symbol(j, slice);
                j += s as usize + 1;
                v
            }
            Tag::Arity(a) => {
                let acc = t.zero(j, a);
                j += 1;
                stack.push((a, acc));
                continue 'putting;
            }
        };

        'popping: loop {
            match stack.last_mut() {
                None => { return Ok((j, value)) }
                Some(&mut (ref mut k, ref mut acc )) => {
                    unsafe {
                        std::ptr::write(k, std::ptr::read(k).wrapping_sub(1));
                        std::ptr::write(acc, t.add(j, std::ptr::read(acc), value));
                        if std::ptr::read(k) != 0 { continue 'putting }
                    }
                }
            }

            value = match stack.pop() {
                Some((_, acc)) => t.finalize(j, acc),
                None => break 'popping
            }
        }
    }
}

struct DebugTraversal { string: String, transient: bool }
#[allow(unused_variables)]
impl Traversal<(), ()> for DebugTraversal {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () { if self.transient { self.string.push(' '); }; self.string.push('$'); }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () { if self.transient { self.string.push(' '); }; self.string.push('_'); self.string.push_str((i as u16 + 1).to_string().as_str()); }
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () { match std::str::from_utf8(s) {
        Ok(string) => { if self.transient { self.string.push(' '); }; self.string.push_str(string); }
        Err(_) => { if self.transient { self.string.push(' '); }; for b in s { self.string.push_str(format!("\\x{:x}", b).as_str()); }; }
    } }
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> () { if self.transient { self.string.push(' '); }; self.string.push('('); self.transient = false; }
    #[inline(always)] fn add(&mut self, offset: usize, acc: (), sub: ()) -> () { self.transient = true; }
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: ()) -> () { self.string.push(')'); }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.ptr.is_null() { f.write_str("NULL")? }
        else { f.write_str(&self.string())? }
        Ok(())
    }
}

struct SerializerTraversal<'a, Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str> { out: &'a mut Target, map_symbol: F, transient: bool }
#[allow(unused_variables, unused_must_use)]
impl <Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str> Traversal<(), ()> for SerializerTraversal<'_, Target, F> {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all("$".as_bytes()); }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all("_".as_bytes()); self.out.write_all((i as u16 + 1).to_string().as_bytes()); }
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all((self.map_symbol)(s).as_bytes()); }
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all("(".as_bytes()); self.transient = false; }
    #[inline(always)] fn add(&mut self, offset: usize, acc: (), sub: ()) -> () { self.transient = true; }
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: ()) -> () { self.out.write_all(")".as_bytes()); }
}

struct SerializerTraversal2<'a, Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str, G : Fn(u8, bool) -> &'static str> { out: &'a mut Target, map_symbol: F, map_variable: G, transient: bool, n: u8 }
#[allow(unused_variables, unused_must_use)]
impl <Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str, G : Fn(u8, bool) -> &'static str> Traversal<(), ()> for SerializerTraversal2<'_, Target, F, G> {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all((self.map_variable)(self.n, true).as_bytes()); self.n += 1; }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all((self.map_variable)(i, false).as_bytes()); }
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all((self.map_symbol)(s).as_bytes()); }
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> () { if self.transient { self.out.write_all(" ".as_bytes()); }; self.out.write_all("(".as_bytes()); self.transient = false; }
    #[inline(always)] fn add(&mut self, offset: usize, acc: (), sub: ()) -> () { self.transient = true; }
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: ()) -> () { self.out.write_all(")".as_bytes()); }
}

struct SerializerTraversalHighlights<'a, 't, Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str, G : Fn(u8, bool) -> &'static str> { out: &'a mut Target, map_symbol: F, map_variable: G, transient: bool, n: u8, targets: &'t [(usize, &'static str, &'static str)] }
#[allow(unused_variables, unused_must_use)]
impl <Target : std::io::Write, F : for <'b> Fn(&'b [u8]) -> &'b str, G : Fn(u8, bool) -> &'static str> Traversal<Option<&'static str>, ()> for SerializerTraversalHighlights<'_, '_, Target, F, G> {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () {
        if self.transient { self.out.write_all(" ".as_bytes()); };
        if offset == self.targets[0].0 { self.out.write_all(self.targets[0].1.as_bytes()); }
        self.out.write_all((self.map_variable)(self.n, true).as_bytes());
        if offset == self.targets[0].0 { self.out.write_all(self.targets[0].2.as_bytes()); self.targets = &self.targets[1..]; }
        self.n += 1;
    }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () {
        if self.transient { self.out.write_all(" ".as_bytes()); };
        if offset == self.targets[0].0 { self.out.write_all(self.targets[0].1.as_bytes()); }
        self.out.write_all((self.map_variable)(i, false).as_bytes());
        if offset == self.targets[0].0 { self.out.write_all(self.targets[0].2.as_bytes()); self.targets = &self.targets[1..]; }
    }
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () {
        if self.transient { self.out.write_all(" ".as_bytes()); };
        if offset == self.targets[0].0 { self.out.write_all(self.targets[0].1.as_bytes()); }
        self.out.write_all((self.map_symbol)(s).as_bytes());
        if offset == self.targets[0].0 { self.out.write_all(self.targets[0].2.as_bytes()); self.targets = &self.targets[1..]; }
    }
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> Option<&'static str> {
        if self.transient { self.out.write_all(" ".as_bytes()); };
        if offset == self.targets[0].0 { self.out.write_all(self.targets[0].1.as_bytes()); }
        self.out.write_all("(".as_bytes()); self.transient = false;
        if offset == self.targets[0].0 { let r = Some(self.targets[0].2); self.targets = &self.targets[1..]; r }
        else { None }
    }
    #[inline(always)] fn add(&mut self, offset: usize, acc: Option<&'static str>, sub: ()) -> Option<&'static str> {
        self.transient = true;
        acc
    }
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: Option<&'static str>) -> () {
        self.out.write_all(")".as_bytes());
        if let Some(end) = acc { self.out.write_all(end.as_bytes()); }
    }
}

struct HashTraversal<H : Hasher, F : for <'b> Fn(&'b [u8], &'b mut H), G : for <'b> Fn(u8, bool, &'b mut H)> { hasher: H, map_symbol: F, map_variable: G, n: u8, o: i8 }
impl <H : Hasher, F : for <'b> Fn(&'b [u8], &'b mut H), G : for <'b> Fn(u8, bool, &'b mut H)> Traversal<(), ()> for HashTraversal<H, F, G> {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () {
        (self.map_variable)(self.n, true, &mut self.hasher);
        self.n += 1;
    }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () {
        (self.map_variable)((i as i8 + self.o) as u8, true, &mut self.hasher);
    }
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () {
        (self.map_symbol)(s, &mut self.hasher);
    }
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> () {
        self.hasher.write_u8(a);
    }
    #[inline(always)] fn add(&mut self, offset: usize, acc: (), sub: ()) -> () {
        ()
    }
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: ()) -> () {
        ()
    }
}

#[derive(Clone)]
pub struct ExprZipper {
    pub root: Expr,
    pub loc: usize,
    pub trace: Vec<Breadcrumb>,
}

impl ExprZipper {
    #[inline] pub fn new(e: Expr) -> Self {
        match unsafe { byte_item(*e.ptr) } {
            Tag::NewVar => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::VarRef(_r) => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::SymbolSize(_s) => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::Arity(a) => {
                Self {
                    root: e,
                    loc: 0,
                    trace: vec![Breadcrumb { parent: 0, arity: a, seen: 0 }],
                    // trace: vec![],
                }
            }
        }
    }

    #[inline] pub fn tag(&self) -> Tag { unsafe { byte_item(*self.root.ptr.byte_add(self.loc)) } }
    #[inline] pub fn item(&self) -> Result<Tag, &[u8]> {
        let tag = self.tag();
        if let Tag::SymbolSize(n) = tag { return unsafe { Err(&*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + 1), n as usize)) } }
        else { return Ok(tag) }
    }
    #[inline] pub fn subexpr(&self) -> Expr { unsafe { Expr { ptr: self.root.ptr.byte_add(self.loc) } } }
    #[inline] pub fn span(&self) -> &[u8] { unsafe { &*slice_from_raw_parts(self.root.ptr, self.loc) } }

    pub fn write_arity(&mut self, arity: u8) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::Arity(arity));
            true
        }
    }
    pub fn write_move(&mut self, value: &[u8]) -> bool {
        unsafe {
            let l = value.len();
            std::ptr::copy(value.as_ptr(), self.root.ptr.byte_add(self.loc), l);
            self.loc += l;
            true
        }
    }

    #[inline(always)]
    pub fn write_symbol(&mut self, value: &[u8]) -> bool {
        unsafe {
            let l = value.len();
            debug_assert!(l < 64);
            let w = self.root.ptr.byte_add(self.loc);
            *w = item_byte(Tag::SymbolSize(l as u8));
            std::ptr::copy_nonoverlapping(value.as_ptr(), w.byte_add(1), l);
            true
        }
    }
    pub fn write_new_var(&mut self) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::NewVar);
            true
        }
    }
    pub fn write_var_ref(&mut self, index: u8) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::VarRef(index));
            true
        }
    }

    pub fn tag_str(&self) -> String {
        match self.tag() {
            Tag::NewVar => { "$".to_string() }
            Tag::VarRef(r) => { format!("_{}", r + 1) }
            Tag::SymbolSize(s) => { format!("({})", s) }
            Tag::Arity(a) => { format!("[{}]", a) }
        }
    }

    pub fn item_str(&self) -> String {
        match self.item() {
            Ok(tag) => {
                match tag {
                    Tag::NewVar => { "$".to_string() }
                    Tag::VarRef(r) => { format!("_{}", r + 1) }
                    Tag::Arity(a) => { format!("[{}]", a) }
                    _ => { unreachable!() }
                }
            }
            Err(s) => {
                match std::str::from_utf8(s) {
                    Ok(string) => { format!("{}", string) }
                    Err(_) => { format!("{:?}", s) }
                }
            }
        }
    }

    pub fn next(&mut self) -> bool {
        self.gnext(0)
    }

    pub fn gnext(&mut self, offset: usize) -> bool {
        // let t = self.tag();
        // let ct = self.tag_str();
        let len = self.trace.len();
        match self.trace[offset..].last_mut() {
            None => { false }
            Some(&mut Breadcrumb { parent: _p, arity: a, seen: ref mut s }) => {
                // println!("parent {} loc {} tag {}", p, self.loc, ct);
                // println!("{} < {}", s, a);
                if *s < a {
                    *s += 1;
                    let ss = *s;

                    self.loc += if let Tag::SymbolSize(n) = self.tag() { n as usize + 1 } else { 1 };

                    if let Tag::Arity(a) = self.tag() {
                        self.trace.push(Breadcrumb { parent: self.loc as u32, arity: a, seen: 0 })
                    }

                    // println!("returned true");
                    true
                } else {
                    self.trace.pop();
                    self.next()
                }
            }
        }
    }

    pub fn next_skip(&mut self) -> bool {
        // let t = self.tag();
        let ct = self.tag_str();
        let len = self.trace.len();
        match self.trace[0..].last_mut() {
            None => { false }
            Some(&mut Breadcrumb { parent: p, arity: a, seen: ref mut s }) => {
                println!("parent {} loc {} tag {}", p, self.loc, ct);
                println!("{} < {}", s, a);
                
                // if p as usize == self.loc {  // begin of expression
                //     self.loc += match self.tag() {
                //         Tag::NewVar => { 1 }
                //         Tag::VarRef(_) => { 1 }
                //         Tag::SymbolSize(n) => { n as usize + 1 }
                //         Tag::Arity(_) => { self.subexpr().span().len() }
                //     };
                //     self.trace.pop();
                //     
                // }

                if *s < a {
                    *s += 1;
                    let ss = *s;

                    // self.loc += if let Tag::SymbolSize(n) = self.tag() { n as usize + 1 } else { 1 };
                    // 
                    // if let Tag::Arity(a) = self.tag() {
                    //     self.loc += self.subexpr().span().len();
                    // }


                    self.loc += match self.tag() {
                        Tag::NewVar => { 1 }
                        Tag::VarRef(_) => { 1 }
                        Tag::SymbolSize(n) => { n as usize + 1 }
                        Tag::Arity(_) => { self.subexpr().span().len() }
                    };

                    // println!("returned true");
                    // if ss == a && len == 1 { false }
                    // else { true }
                    true
                } else {
                    self.trace.pop();
                    self.next_skip()
                }
            }
        }
    }

    pub fn parent(&mut self) -> bool {
        let Some(Breadcrumb { parent: p, .. }) = self.trace.last() else { return false; };
        self.loc = *p as usize;
        self.trace.pop();
        true
    }

    pub fn reset(&mut self) -> bool {
        self.loc = 0;
        unsafe { self.trace.set_len(0); }
        if let Tag::Arity(a) = unsafe { byte_item(*self.root.ptr) } {
            self.trace.push(Breadcrumb {parent: 0, arity:a, seen : 0})
        }
        true
    }

    pub fn next_child(&mut self) -> bool {
        self.next_descendant(0, 0)
    }

    pub fn next_descendant(&mut self, to: i32, offset: usize) -> bool {
        let (base, _backup) = if to < 0 {
            let last = self.trace.len() as i32 + to;
            (self.trace[last as usize].parent, self.trace[last as usize])
        } else if to > 0 {
            (self.trace[(to - 1) as usize].parent, self.trace[(to - 1) as usize])
        } else { (0, self.trace[0]) };
        let initial = self.trace.clone();

        #[allow(unused_variables)]
        let mut lc = 0;
        loop {
            if !self.gnext(0) {
                // println!("no next {} {}", lc, self.trace.len());
                self.trace = initial;
                return false; }
            let l = self.trace.len() - 1 - offset;
            let parent = self.trace[l].parent;
            if let Tag::Arity(_) = self.tag() {
                if l > 0 && self.trace[l - 1].parent == base {
                    return true;
                }
            } else {
                if parent == base {
                    return true;
                }
            }
            lc += 1;
        }
    }

    /// Debug traversal
    pub fn traverse(&self, i: usize) -> usize {
        match unsafe { maybe_byte_item(*self.root.ptr.byte_add(self.loc + i)) } {
            Ok(Tag::NewVar) => { print!("$"); 1 }
            Ok(Tag::VarRef(r)) => { print!("_{}", r + 1); 1 }
            Ok(Tag::SymbolSize(s)) => {
                let slice = unsafe { &*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + i + 1), s as usize) };
                match std::str::from_utf8(slice) {
                    Ok(string) => { print!("{}", string) }
                    Err(_) => { for b in slice { print!("\\x{:x}", b) } }
                }
                s as usize + 1
            }
            Ok(Tag::Arity(a)) => {
                print!("(");
                let mut offset = 1;
                for k in 0..a {
                    offset += self.traverse(i + offset);
                    if k != (a - 1) { print!(" ") }
                }
                print!(")");
                offset
            }
            Err(b) => {
                print!("{}", b as usize);
                1
            }
        }
    }

    pub fn finish_span(&self) -> *const [u8] {
        let size = self.loc + match self.tag() {
            Tag::NewVar => { 1 }
            Tag::VarRef(_r) => { 1 }
            Tag::SymbolSize(s) => { 1 + (s as usize) }
            Tag::Arity(0) => { 1 }
            Tag::Arity(_a) => { unreachable!() /* expression can't end in non-zero expression */ }
        };
        return slice_from_raw_parts(self.root.ptr, size)
    }
}

const fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

const fn digit_value(b: u8) -> u8 {
    b - b'0'
}


#[macro_export]
macro_rules! parse {
    ($s:literal) => {{
        const N: usize = $crate::compute_length($s);
        const ARR: [u8; N] = $crate::parse::<N>($s);
        ARR
    }};
}

pub const fn compute_length(s: &str) -> usize {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    let mut n = 0;

    while i < len {
        // Skip spaces
        while i < len && bytes[i] == b' ' {
            i += 1;
        }
        if i >= len {
            break;
        }

        let b = bytes[i];

        if b == b'[' {
            // Parse [number]
            i += 1;
            while i < len && bytes[i] != b']' {
                i += 1;
            }
            i += 1; // Skip ']'
            n += 1; // item_byte(Tag::Arity(number))
        } else if b == b'$' {
            i += 1;
            n += 1; // item_byte(Tag::NewVar)
        } else if b == b'_' {
            // Parse _number
            i += 1;
            while i < len && is_digit(bytes[i]) {
                i += 1;
            }
            n += 1; // item_byte(Tag::VarRef(number - 1))
        } else {
            // Parse symbol (word)
            let mut word_len = 0;
            while i < len && bytes[i] != b' ' {
                word_len += 1;
                i += 1;
            }
            n += 1 + word_len; // item_byte + word bytes
        }
    }

    n
}

pub const fn parse<const N: usize>(s: &str) -> [u8; N] {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut arr = [0u8; N];
    let mut i = 0;
    let mut pos = 0;

    while i < len {
        // Skip spaces
        while i < len && bytes[i] == b' ' {
            i += 1;
        }
        if i >= len {
            break;
        }

        let b = bytes[i];

        if b == b'[' {
            // Parse [number]
            i += 1; // Skip '['
            let mut num = 0u8;
            while i < len && is_digit(bytes[i]) {
                num = num * 10 + digit_value(bytes[i]);
                i += 1;
            }
            if i < len && bytes[i] == b']' {
                i += 1; // Skip ']'
                arr[pos] = item_byte(Tag::Arity(num));
                pos += 1;
            } else {
                // Handle error: expected ']'
                i += 1;
            }
        } else if b == b'$' {
            i += 1; // Skip '$'
            arr[pos] = item_byte(Tag::NewVar);
            pos += 1;
        } else if b == b'_' {
            // Parse _number
            i += 1; // Skip '_'
            let mut num = 0u8;
            while i < len && is_digit(bytes[i]) {
                num = num * 10 + digit_value(bytes[i]);
                i += 1;
            }
            if num > 0 {
                arr[pos] = item_byte(Tag::VarRef(num - 1));
            } else {
                arr[pos] = item_byte(Tag::VarRef(0));
            }
            pos += 1;
        } else {
            // Parse symbol (word)
            let word_start = i;
            let mut word_len = 0;
            while i < len && bytes[i] != b' ' {
                word_len += 1;
                i += 1;
            }
            // Insert item_byte(Tag::SymbolSize(word_len))
            arr[pos] = item_byte(Tag::SymbolSize(word_len));
            pos += 1;
            // Copy the word bytes
            let mut j = 0;
            while j < word_len {
                arr[pos] = bytes[word_start + (j as usize)];
                pos += 1;
                j += 1;
            }
        }
    }

    arr
}


pub fn serialize(bytes: &[u8]) -> String {
    let mut result = String::new();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        match maybe_byte_item(b) {
            Ok(tag) => {
                match tag {
                    Tag::NewVar => {
                        result.push('$');
                        i += 1;
                    },
                    Tag::VarRef(idx) => {
                        result.push('_');
                        result.push_str(&format!("{}", idx + 1)); // idx is 0-based
                        i += 1;
                    },
                    Tag::Arity(a) => {
                        result.push('[');
                        result.push_str(&format!("{}", a));
                        result.push(']');
                        i += 1;
                    },
                    Tag::SymbolSize(s) => {
                        i += 1;
                        if i + (s as usize) > bytes.len() {
                            // panic!("Not enough bytes for symbol (expected {}, remaining {:?})", s, &bytes[i..]);
                            for j in i..bytes.len() {
                                let symbol_byte = bytes[j];
                                // Check if symbol_byte is printable ASCII
                                if (symbol_byte.is_ascii_graphic() || symbol_byte == b' ') && symbol_byte != b'\\' {
                                    result.push(symbol_byte as char);
                                } else {
                                    result.push_str(&format!("\\x{:02X}", symbol_byte));
                                }
                            }
                            result.push_str(format!("<truncated {}>", (i + (s as usize)) - bytes.len()).as_str());
                            i += s as usize;
                            break;
                        } else {
                            // Read the next s bytes as symbol bytes
                            for j in 0..s {
                                let symbol_byte = bytes[i + j as usize];
                                // Check if symbol_byte is printable ASCII
                                if (symbol_byte.is_ascii_graphic() || symbol_byte == b' ') && symbol_byte != b'\\' {
                                    result.push(symbol_byte as char);
                                } else {
                                    result.push_str(&format!("\\x{:02X}", symbol_byte));
                                }
                            }
                            i += s as usize;
                        }
                    }
                }
            },
            Err(b) => {
                // Unknown byte
                result.push_str(&format!("\\x{:02X}", b));
                i += 1;
            }
        }
        // Add space between tokens if needed
        if i < bytes.len() {
            result.push(' ');
        }
    }
    result
}

unsafe impl Sync for Expr {}
unsafe impl Send for Expr {}

type ExprVar = (u8, u8);

#[derive(Clone, Copy, Debug)]
pub struct ExprEnv {
    pub n: u8,
    pub v: u8,
    pub offset: u32,
    pub base: Expr
}

impl PartialEq<Self> for ExprEnv {
    fn eq(&self, other: &Self) -> bool {
        (self.n == other.n) &&
        (self.v == other.v) &&
        (self.offset == other.offset) &&
        (self.base.ptr == other.base.ptr)
    }
}

impl Eq for ExprEnv {}

impl std::hash::Hash for ExprEnv {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u8(self.n);
        state.write_u8(self.v);
        state.write_u32(self.offset);
        // state.write_u64(self.base.ptr as u64);
        // state.write(unsafe { &*slice_from_raw_parts(self as *const ExprEnv as *const u8, size_of::<ExprEnv>()) });
    }
}

pub struct TraverseSide { ee: ExprEnv }
impl Traversal<(), ()> for TraverseSide {
    #[inline(always)] fn new_var(&mut self, offset: usize) -> () { self.ee.v += 1; }
    #[inline(always)] fn var_ref(&mut self, offset: usize, i: u8) -> () {}
    #[inline(always)] fn symbol(&mut self, offset: usize, s: &[u8]) -> () {}
    #[inline(always)] fn zero(&mut self, offset: usize, a: u8) -> () {}
    #[inline(always)] fn add(&mut self, offset: usize, acc: (), sub: ()) -> () {}
    #[inline(always)] fn finalize(&mut self, offset: usize, acc: ()) -> () {}
}

impl ExprEnv {
    pub fn new(i: u8, e: Expr) -> Self {
        Self {
            n: i,
            v: 0,
            offset: 0,
            base: e,
        }
    }

    pub fn v_incr_traversal(&self) -> TraverseSide {
        TraverseSide{ ee: self.clone() }
    }

    pub fn offset(&self, offset: u32) -> ExprEnv {
        ExprEnv{ n: self.n, v: self.v, offset: self.offset + offset, base: self.base }
    }

    pub fn subsexpr(&self) -> Expr {
        Expr { ptr: unsafe { self.base.ptr.add(self.offset as usize) } }
    }

    pub fn show(&self) -> String {
        let mut v = vec![];
        self.base.serialize_highlight(&mut v, |x| std::str::from_utf8(x).unwrap_or_else(|_| format!("{:?}", x).leak()),
                                      |v, i| format!("<{},{}>", self.n, v).leak(), self.offset as usize);
        // self.subsexpr().serialize2(&mut v, |x| std::str::from_utf8(x).unwrap(),
        //                               |v, i| format!("<{},{}>", self.n, v).leak());
        String::from_utf8(v).unwrap()
    }

    pub fn var_opt(&self) -> Option<ExprVar> {
        unsafe {
            match byte_item(*self.base.ptr.add(self.offset as usize)) {
                Tag::NewVar => { Some((self.n, self.v)) }
                Tag::VarRef(i) => { Some((self.n, i)) }
                Tag::SymbolSize(_) => { None }
                Tag::Arity(_) => { None }
            }
        }
    }

    fn same_functor(&self, other: &Self) -> bool {
        unsafe {
            if self.n == other.n && self.offset == other.offset { return true }
            let lhs = self.subsexpr();
            let lprefix = lhs.prefix().unwrap_or_else(|x| slice_from_raw_parts(x as *const _, x.len() + 1)).as_ref().unwrap();
            let rhs = other.subsexpr();
            let rprefix = rhs.prefix().unwrap_or_else(|x| slice_from_raw_parts(x as *const _, x.len() + 1)).as_ref().unwrap();
            // performance
            // if lhs.constant_difference(rhs).is_none() {
            let count = fast_slice_utils::find_prefix_overlap(lprefix, rprefix);
            if count != 0 && (count == lprefix.len() || count == rprefix.len()) {
                true
            } else {
                // let diff = lhs.constant_difference(rhs).unwrap();
                // println!("({}) {:?}  !=  {:?}", diff, self.subsexpr(), other.subsexpr());
                false
            }
        }
    }

    pub fn args(&self, dest: &mut Vec<Self>) {
        unsafe {
        match byte_item(*self.subsexpr().ptr) {
            Tag::NewVar | Tag::VarRef(_) | Tag::SymbolSize(_) => { }
            Tag::Arity(k) => {
                let mut env = ExprEnv{
                    n: self.n,
                    v: self.v,
                    offset: self.offset + 1,
                    base: self.base,
                };
                for sk in 0..k {
                    let (se_c, _, se_offset) = traverseh!((), (), u8, env.subsexpr(), 0,
                        |c: &mut u8, o| { *c += 1; },
                        |_, o, r| {},
                        |_, o, _| {},
                        |_, o, _| {},
                        |_, o, x, y| {},
                        |_, _, _| {});

                    let ne = env.clone();
                    dest.push(ne);
                    env.offset += se_offset as u32;
                    env.v += se_c;
                }
            }
        }
        }
    }
}

#[derive(Debug)]
pub enum UnificationFailure {
    Occurs(ExprVar, ExprEnv),
    Difference(ExprEnv, ExprEnv),
    MaxIter(u32)
}

const APPLY_DEPTH: u32 = 64;
const MAX_UNIFY_ITER: u32 = 1000;
const PRINT_DEBUG: bool = false;
#[inline(never)]
pub fn apply(n: u8, mut original_intros: u8, mut new_intros: u8, ez: &mut ExprZipper, bindings: &BTreeMap<ExprVar, ExprEnv>, oz: &mut ExprZipper, cycled: &mut BTreeMap<ExprVar, u8>, stack: &mut Vec<ExprVar>, assignments: &mut Vec<ExprVar>) -> (u8, u8) {
    let depth = stack.len();
    if stack.len() > APPLY_DEPTH as usize { panic!("apply depth > {APPLY_DEPTH}: {n} {original_intros} {new_intros}"); }
    if PRINT_DEBUG { println!("{}@ n={} original={} new={} ez={:?}", "  ".repeat(depth), n, original_intros, new_intros, ez.subexpr()); }
    unsafe {
        loop {
            match ez.item() {
                Ok(Tag::NewVar) => {
                    match bindings.get(&(n, original_intros)) {
                        None => {
                            if PRINT_DEBUG { println!("{}@ $ no binding for {:?}", "  ".repeat(depth), (n, original_intros)); }
                            // println!("original {original_intros} new {new_intros}");
                            if let Some(pos) = assignments.iter().position(|e| *e == (n, original_intros)) {
                                // println!("{}assignments _{} for {:?} (newvar)", "  ".repeat(depth), pos + 1, (n, original_intros));
                                oz.write_var_ref(pos as u8);
                            } else {
                                oz.write_new_var();
                                new_intros += 1;
                                assignments.push((n, original_intros));
                            }
                            oz.loc += 1;
                            original_intros += 1;

                        }
                        Some(rhs) => {
                            if PRINT_DEBUG { println!("{}@ $ with bindings +{} {} for {:?}", "  ".repeat(depth), rhs.n, rhs.show(), (n, original_intros)); }
                            // println!("stack={stack:?}");
                            if let Some(introduced) = cycled.get(&(n, original_intros)) {
                                if PRINT_DEBUG { println!("{}cycled _{} for {:?} (newvar)", "  ".repeat(depth), *introduced+1, (n, original_intros)) };
                                oz.write_var_ref(*introduced);
                                // println!("nv cycled contains {:?}", (n, original_intros));
                                oz.loc += 1;   
                            } else if stack.contains(&(n, original_intros)) {
                                cycled.insert((n, original_intros), new_intros);
                                // println!("nv cycled insert {:?}", (n, original_intros));
                                oz.write_new_var();
                                oz.loc += 1;
                                new_intros += 1;
                            } else {
                                stack.push((n, original_intros));
                                let (evars_, nvars_) = apply(rhs.n, rhs.v, new_intros, &mut ExprZipper::new(rhs.subsexpr()), bindings, oz, cycled, stack, assignments);
                                new_intros = nvars_;
                                stack.pop();
                            }
                            original_intros += 1;
                        }
                    }
                }
                Ok(Tag::VarRef(i)) => {
                    match bindings.get(&(n, i)) {
                        None => {
                            if PRINT_DEBUG { println!("{}@ _{} no binding for {:?}", "  ".repeat(depth), i+1, (n, i)); }
                            if let Some(pos) = assignments.iter().position(|e| *e == (n, i)) {
                                // println!("{}assignments _{} for {:?} (ref)", "  ".repeat(depth), pos+1, (n, i));
                                oz.write_var_ref(pos as u8);
                            } else {
                                oz.write_new_var();
                                new_intros += 1;
                                assignments.push((n, i)); // this can't be right in general
                            }
                            oz.loc += 1;
                        }
                        Some(rhs) => {
                            if PRINT_DEBUG { println!("{}@ _{} with binding +{} {} for {:?}", "  ".repeat(depth), i+1, rhs.n, rhs.show(), (n, i)); }
                            // println!("stack={stack:?}");
                            if let Some(introduced) = cycled.get(&(n, i)) {
                                // println!("vr cycled contains {:?}", (n, i));
                                if PRINT_DEBUG { println!("{}cycled _{} for {:?} (ref) rhs={}", "  ".repeat(depth), *introduced+1, (n, i), rhs.show()); }
                                oz.write_var_ref(*introduced);
                                oz.loc += 1;
                            } else if stack.contains(&(n, i)) {
                                // println!("vr cycled insert {:?}", (n, i));
                                cycled.insert((n, i), new_intros);
                                oz.write_new_var();
                                oz.loc += 1;
                                new_intros += 1;
                            } else {
                                stack.push((n, i));
                                let (evars_, nvars_) = apply(rhs.n, rhs.v, new_intros, &mut ExprZipper::new(rhs.subsexpr()), bindings, oz, cycled, stack, assignments);
                                new_intros = nvars_;
                                stack.pop();
                            }
                            // oz.write_var_ref(i);
                            // oz.loc += 1;
                        }
                    }
                }
                Ok(Tag::SymbolSize(s)) => {
                    unreachable!()
                }
                Err(slice) => {
                    if PRINT_DEBUG { println!("{}@ \"{}\"", "  ".repeat(depth), unsafe { std::str::from_utf8_unchecked(slice) }); }
                    oz.write_symbol(slice);
                    oz.loc += 1 + slice.len();
                }
                Ok(Tag::Arity(a)) => {
                    if PRINT_DEBUG { println!("{}@ [{}]", "  ".repeat(depth), a); }
                    oz.write_arity(a);
                    oz.loc += 1;
                }
            }

            if !ez.next() {
                return (original_intros, new_intros);
            }
        }
    }
}


#[inline(never)]
pub fn unify(mut stack: Vec<(ExprEnv, ExprEnv)>) -> Result<BTreeMap<ExprVar, ExprEnv>, UnificationFailure> {
    let mut bindings: BTreeMap<ExprVar, ExprEnv> = BTreeMap::new();
    let mut iterations = 0;
    let mut encountered: gxhash::HashSet<(ExprEnv, ExprEnv)> = gxhash::HashSet::new();

    macro_rules! step {
        (occurs $x:expr, $e:expr) => {{
            let x = $x;
            let e = $e;
            if x.0 != e.n { false }
            else {
                let t : u8 = x.1;
                traverseh!(bool, bool, u8, e.subsexpr(), e.v,
                    |c: &mut u8, _| { let eq = *c == t; *c += 1; eq },
                    |c: &mut u8, _, r| r == t, |_, _, _| false, |_, _, _| false, |_, _, x, y| x || y, |_, _, x| x).1
            }
        }};
        (derefBound $t:expr) => {{
            let mut t: ExprEnv = $t;
            'bound: loop {
                match t.var_opt() {
                    None => { break 'bound t; }
                    Some(vs) => {
                        match bindings.get(&vs) {
                            None => { break 'bound t; }
                            Some(binding) => {
                                t = *binding;
                                continue 'bound
                            }
                        }
                    }
                }
            }
        }};
        (isUnbound $v:expr) => {{
            let mut v: ExprVar = $v;
            'unbound: loop {
                match bindings.get(&v) {
                    None => { break 'unbound true }
                    Some(binding) => {
                        match binding.var_opt() {
                            None => { break 'unbound false }
                            Some(vs) => {
                                v = vs;
                                continue 'unbound
                            }
                        }
                    }
                }
            }
        }};
        (push $x:expr, $y:expr) => {{
            let _x: ExprEnv = $x;
            let _y: ExprEnv = $y;
            if PRINT_DEBUG { println!("pushing {} {}", _x.show(), _y.show()); }
            match (_x.var_opt(), _y.var_opt()) {
                (Some(xvs), Some(yvs)) if step!(isUnbound xvs) && step!(isUnbound yvs) => {
                    stack.push((_x, _y));
                }
                _ if !encountered.contains(&(_x, _y)) => {
                    encountered.insert((_x, _y));
                    stack.push((_x, _y));
                }
                _ => {}
            }
        }};
    }

    'popping: while let Some((xpop, ypop)) = stack.pop() {
        if PRINT_DEBUG {
            println!("step {iterations}");
            bindings.iter().for_each(|(k, v)| {
                // let ov = vec![0u8; 512];
                // let o = Expr{ ptr: ov.leak().as_mut_ptr() };
                // apply(v.n, v.v, 0, &mut ExprZipper::new(v.subsexpr()), &bindings, &mut ExprZipper::new(o), 0);
                println!("  binding {:?} +{} {}", *k, v.v, v.show());
                // println!("output {:?}", o);

            });
            println!();
        }

        if iterations > MAX_UNIFY_ITER { 
            return Err(UnificationFailure::MaxIter(iterations))
        }
        iterations += 1;
        if PRINT_DEBUG {
            println!("popping");
            // println!("x: {}, sx : {:?}", xpop.show(), sx.len());
            // println!("y: {}, sy : {:?}", ypop.show(), sy.len());
        }
        let dt1: ExprEnv = step!(derefBound xpop);
        let dt2: ExprEnv = step!(derefBound ypop);

        match (dt1.var_opt(), dt2.var_opt()) {
            (None, None) => {
                let mut ts1 = dt1.clone().v_incr_traversal();
                let mut ts2 = dt2.clone().v_incr_traversal();

                if let Err((o1, o2)) = match2(&mut ts1, dt1.subsexpr(), 0, &mut ts2, dt2.subsexpr(), 0,
                                              &mut |_ts1, e1, i1, _ts2, e2, i2| {
                                                  step!(push _ts1.ee.offset(i1 as u32), _ts2.ee.offset(i2 as u32))
                                              }) {
                    if PRINT_DEBUG { println!("diff {} @ {}  != {} @ {}", dt1.offset(o1 as u32).show(), o1, dt2.offset(o2 as u32).show(), o2); }
                    return Err(UnificationFailure::Difference(dt1, dt2));
                }
            }
            (Some(vx), ov) => {
                if let Some(sv) = ov { if vx == sv { continue 'popping } }
                if step!(occurs vx, dt2)  { return Err(UnificationFailure::Occurs(vx, dt2)) }
                bindings.insert(vx, dt2.clone());
            }
            (ov, Some(vy)) => {
                if let Some(sv) = ov { if vy == sv { continue 'popping } }
                if step!(occurs vy, dt1)  { return Err(UnificationFailure::Occurs(vy, dt1)) }
                bindings.insert(vy, dt1.clone());
            }
        }
    }

    if stack.is_empty() {
        Ok(bindings)
    } else {
        unreachable!()
    }
}


// Generalization vars in the output are numbered by first occurrence (0..).
pub type AuVar = u8;

#[derive(Debug)]
pub enum AntiUnificationFailure {
    TooManyVars,      // > 64 distinct disagreement classes
    MaxDepth(usize),  // guard against pathological inputs
}

pub struct AntiUnifyResult {
    /// For each generalization variable `i`, the (left) subterm it abstracts.
    pub left:  BTreeMap<AuVar, ExprEnv>,
    /// For each generalization variable `i`, the (right) subterm it abstracts.
    pub right: BTreeMap<AuVar, ExprEnv>,
}

/// Assumed to exist (as you said): Hash/Eq compares subexpressions using *absolute* vars
/// (so `NewVar` occurrences and `VarRef` occurrences compare as the same variable identity).
#[derive(Clone, Copy, Debug)]
pub struct RelExprEnv(ExprEnv);

impl PartialEq for RelExprEnv {
    fn eq(&self, other: &Self) -> bool {
        let mut vs = self.0.v;
        let mut vo = other.0.v;
        unsafe {
        traverseh!((), (), bool, self.0.subsexpr(), true,
                        |b: &mut bool, o| {
                            *b &= match byte_item(*other.0.base.ptr.add(other.0.offset as usize + o)) {
                                Tag::NewVar => { let eq = vs == vo; vo += 1; eq }
                                Tag::VarRef(j) => { vs == j }
                                _ => { false }
                            };
                            // println!("$ {:?}", b);
                            vs += 1;
                        },
                        |b: &mut bool, o, r| {
                            *b &= match byte_item(*other.0.base.ptr.add(other.0.offset as usize + o)) {
                                Tag::NewVar => { let eq = r == vo; vo += 1; eq }
                                Tag::VarRef(j) => { r == j }
                                _ => { false }
                            };
                            // println!("_{} {:?}", r as usize + 1, b);
                        },
                        |b: &mut bool, o, s: &[u8]| {
                            let oss = byte_item(*other.0.base.ptr.add(other.0.offset as usize + o));
                            *b &= oss == Tag::SymbolSize(s.len() as _);
                            if !*b { return };
                            let Tag::SymbolSize(ss) = oss else { unreachable!() };
                            *b &= slice_from_raw_parts(other.0.base.ptr.add(other.0.offset as usize + o + 1), ss as usize).as_ref().unwrap() == s;
                            // println!("'{}' {:?}", std::str::from_utf8(s).unwrap(), b);
                        },
                        |b: &mut bool, o, a| {
                            *b &= *other.0.base.ptr.add(other.0.offset as usize + o) == item_byte(Tag::Arity(a));
                            // println!("[{}] {}", a as usize, b);
                        },
                        |_, o, x, y| {},
                        |_, _, _| {}).0
        }
    }
}

impl Eq for RelExprEnv {}

impl std::hash::Hash for RelExprEnv {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut v = self.0.v;
        traverseh!((), (), (), self.0.subsexpr(), (),
                        |_, o| { state.write_u8(0); state.write_u8(v); v += 1; },
                        |_, o, r| { state.write_u8(0); state.write_u8(r); },
                        |_, o, s| { state.write_u8(1); state.write(s); },
                        |_, o, a| { state.write_u8(2); state.write_u8(a); },
                        |_, o, x, y| {},
                        |_, _, _| {});
    }
}

impl From<ExprEnv> for RelExprEnv {
    fn from(e: ExprEnv) -> Self { RelExprEnv(e) }
}

struct AuState {
    next_var: u8,
    // key: (left_subterm, right_subterm)  value: output var id
    memo: HashMap<(RelExprEnv, RelExprEnv), AuVar>,
    left:  BTreeMap<AuVar, ExprEnv>,
    right: BTreeMap<AuVar, ExprEnv>,
}

const AU_MAX_DEPTH: usize = 1000;

#[inline(always)]
fn decomposable(lhs: &ExprEnv, rhs: &ExprEnv) -> bool {
    // Variables are treated as atoms (disagreement => generalized var),
    // and repetition is handled by memoizing disagreement pairs.
    if lhs.var_opt().is_some() || rhs.var_opt().is_some() {
        return false;
    }

    unsafe {
        if let (Some(s1), Some(s2)) = (lhs.subsexpr().symbol(), rhs.subsexpr().symbol()) {
            s1.as_ref() == s2.as_ref()
        } else if let (Some(a1), Some(a2)) = (lhs.subsexpr().arity(), rhs.subsexpr().arity()) {
            a1 == a2
        } else {
            false
        }
    }
}

#[inline(never)]
fn anti_unify_apply(
    lhs0: ExprEnv,
    rhs0: ExprEnv,
    oz: &mut ExprZipper,
    st: &mut AuState,
) -> Result<(), AntiUnificationFailure> {
    let mut stack: Vec<(ExprEnv, ExprEnv)> = vec![(lhs0, rhs0)];

    // Scratch buffers to avoid repeated allocations while decomposing arity nodes.
    let mut largs: Vec<ExprEnv> = Vec::new();
    let mut rargs: Vec<ExprEnv> = Vec::new();

    while let Some((lhs, rhs)) = stack.pop() {
        if PRINT_DEBUG { println!("{} AU {}", lhs.show(), rhs.show()); }
        if stack.len() > AU_MAX_DEPTH {
            return Err(AntiUnificationFailure::MaxDepth(stack.len()));
        }

        if decomposable(&lhs, &rhs) {
            if PRINT_DEBUG { println!("decompose/agree"); }
            unsafe {
                match byte_item(*lhs.base.ptr.add(lhs.offset as usize)) {
                    Tag::Arity(k) => {
                        oz.write_arity(k);
                        oz.loc += 1;

                        largs.clear();
                        rargs.clear();
                        lhs.args(&mut largs);
                        rhs.args(&mut rargs);
                        debug_assert_eq!(largs.len(), rargs.len());

                        // Preorder: push children reversed so they pop in-order.
                        for i in (0..largs.len()).rev() {
                            stack.push((largs[i], rargs[i]));
                        }
                    }

                    Tag::SymbolSize(_) => {
                        // ExprZipper::item() returns Err(&[u8]) for symbol bytes in your codepath.
                        let mut ez = ExprZipper::new(lhs.subsexpr());
                        match ez.item() {
                            Err(sym) => {
                                oz.write_symbol(sym);
                                oz.loc += 1 + sym.len();
                            }
                            Ok(_) => unreachable!("expected symbol bytes at a SymbolSize root"),
                        }
                    }

                    Tag::NewVar | Tag::VarRef(_) => unreachable!("decomposable() excludes vars"),
                }
            }
        } else {
            if PRINT_DEBUG { println!("var/disagree"); }
            // Disagreement case: introduce/reuse a generalization variable.
            let key = (RelExprEnv::from(lhs), RelExprEnv::from(rhs));

            if let Some(&v) = st.memo.get(&key) {
                if PRINT_DEBUG { println!("did find re-use ({}, {}) = {}", lhs.show(), rhs.show(), v); }
                oz.write_var_ref(v);
                oz.loc += 1;
            } else {
                if st.next_var >= 64 {
                    return Err(AntiUnificationFailure::TooManyVars);
                }
                let v: AuVar = st.next_var as AuVar;
                st.next_var += 1;

                if PRINT_DEBUG {
                    println!("did not find re-use, inserting ({}, {}) = {}", lhs.show(), rhs.show(), v);
                    // println!("did not find re-use {:?} {:?}", lhs, rhs);
                    // println!("did not find re-use in {:?}", st.memo);
                }

                st.memo.insert(key, v);
                st.left.insert(v, lhs);
                st.right.insert(v, rhs);

                oz.write_new_var();
                oz.loc += 1;
            }
        }
    }

    Ok(())
}

mod tests {
    use crate::gxhash::GxHasher;
    use super::*;
    #[test]
    fn test_unify() {
        {
            let mut tv = parse!(r"[3] [2] f [2] f a [3] h [2] f [2] f a [2] f a [2] f [2] f a"); // ((f $x) (h $y (f a)) $y)
            let t = Expr { ptr: tv.as_mut_ptr() };

            let mut xv = parse!(r"[3] $ [3] h _1 $ [2] f _2"); // ($z (h $z $w) (f $w))
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2"); // ((f $x) (h $y (f a)) $y)
            let y = Expr { ptr: yv.as_mut_ptr() };

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            assert_eq!(format!("{:?}", to), format!("{:?}", t));
        }
        {
            let mut tv = parse!(r"[4] $ _1 _1 _1"); // $i $i $i $i
            let t = Expr { ptr: tv.as_mut_ptr() };

            let mut xv = parse!(r"[4] $ $ _1 _2"); // $a $b $a $b
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[4] $ $ _2 _1"); // $x $y $y $x
            let y = Expr { ptr: yv.as_mut_ptr() };

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            assert_eq!(format!("{:?}", to), format!("{:?}", t));
        }
        {
            let mut tv = parse!(r"[8] $ _1 _1 _1 _1 _1 _1 _1"); // $i $i $i $i $i $i $i $i
            let t = Expr { ptr: tv.as_mut_ptr() };

            let mut xv = parse!(r"[8] $ $ $ $ _3 _2 _3 _4"); // $a $b $c $d $c $b $c $d
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[8] $ $ $ $ _4 _1 _2 _3"); // $x $y $z $w $w $x $y $z
            let y = Expr { ptr: yv.as_mut_ptr() };

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            assert_eq!(format!("{:?}", to), format!("{:?}", t));
        }
        {
            let mut tv = parse!("[2] [2] flip [3] = $ [3] T _1 [4] a _1 $ $ [2] axiom [3] = [3] T _1 [4] a _1 _2 _3 _1");
            //                   ((flip (= $ (T _1 (a _1 $ _1)))) (axiom (= (T _1 (a _1 _2 _1)) _1)))
            let t = Expr { ptr: tv.as_mut_ptr() };

            let mut xv = parse!("[2] $ [2] axiom [3] = [3] T $ [4] a _2 $ $ _2");
            //                   ($res (axiom (= (T $x (a $x $y $z)) $x)))
            //                    result   input-data
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] [2] flip [3] = $ $ [2] axiom [3] = _2 _1");
            //                   ((flip (= $l $r)) (axiom (= $r $l))
            //                    template          pattern
            let y = Expr { ptr: yv.as_mut_ptr() };

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            assert_eq!(format!("{:?}", to), format!("{:?}", t));
        }
        {
            let mut srcv = parse!(r"[2] axiom [3] = [3] T $ [3] * $ _2 [3] T _1 [3] R [4] a _1 $ $ [3] * _2 _2");
            let src = Expr { ptr: srcv.as_mut_ptr() };
            let mut patv = parse!("[2] axiom [3] = _2 _1");
            let pat = Expr { ptr: patv.as_mut_ptr() };

            let mut templv = parse!("[2] flip [3] = $ $");
            let templ = Expr { ptr: templv.as_mut_ptr() };

            let mut rv = parse!(r"[2] flip [3] = [3] T $ [3] R [4] a _1 $ $ [3] * $ _4 [3] T _1 [3] * _4 _4");
            let r = Expr { ptr: rv.as_mut_ptr() };

            match src.transformed(templ, pat) {
                Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
                Err(e) => { panic!("{:?}", e); }
            }
        }
        // println!("================");
        {
            // let mut tv = parse!("");
            // let t = Expr{ ptr: tv.as_mut_ptr() };

            let mut xv = parse!("[3] [3] [3] [3] [3] [3] a * $ * $ * $ * $ * $ = [3] _5 * [3] _4 * [3] _3 * [3] _2 * [3] _1 * a");
            //                   ($res (axiom (= (T $x (a $x $y $z)) $x)))
            //                    result   input-data
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[3] $ = _1");
            //                   ((flip (= $l $r)) (axiom (= $r $l))
            //                    template          pattern
            let y = Expr { ptr: yv.as_mut_ptr() };

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            println!("{:?}", to);
        }
        {
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] * [3] / 1 $ [3] * _1 $ $ _1 [3] \\ _1 1 [3] * _2 [3] * [3] * _3 _1 [3] \\ _1 1");
            //                   (axiom (= (* (* (* (* (/ 1 $) (* _1 $)) $) _1) (\ _1 1)) (* _2 (* (* _3 _1) (\ _1 1)))))
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] * [3] / 1 $ [3] * _1 $ $ _1 [3] \\ _1 1 [3] * _2 [3] * [3] * _3 _1 [3] \\ _1 1");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            assert_eq!(format!("{:?}", to), format!("{:?}", x));
        }
        {
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] / 1 $ $ $ _1 [3] \\ _1 [3] * _2 [3] * _3 _1");
            //                   (axiom (= (* (* (* (* (/ 1 $) (* _1 $)) $) _1) (\ _1 1)) (* _2 (* (* _3 _1) (\ _1 1)))))
            //                   (axiom (= (* (* (* (* (/ 1 $) (* _1 $)) $) _1) (\ _1 1)) (* _1 (* (* _1 _1) (\ _1 1)))))  <- gotten
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] / 1 $ $ _1 [3] K $ $ [3] \\ _1 [3] * _2 [3] * _1 [3] K _3 _4");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            println!("{:?}", to);
        }
        {
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ [3] / 1 $ $ _3 [3] \\ _3 [3] * [3] K _1 [3] T _2 _3 [3] * _4 _3");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ [3] / 1 $ $ _3 [3] \\ _3 [3] * [3] K _1 [3] T _2 [3] / 1 _3 [3] * _4 _3");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            // occurs
            assert!(matches!(x.unify(y, &mut ExprZipper::new(to)), Err(UnificationFailure::Occurs(_, _))));
        }
        {
            // [2] axiom [3] = [3] * [3] * $ [3] \ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4 _2 _2 _2 _2
            // [2] axiom [3] = [3] * [3] * $ [3] \ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4 [3] \ _2 1 _2 _2 _2

            let mut xv = parse!("[2] axiom [3] = [3] * [3] * $ [3] \\ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4   _2            _2 _2 _2");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * $ [3] \\ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4   [3] \\ _2 1   _2 _2 _2");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(matches!(x.unify(y, &mut ExprZipper::new(to)), Err(UnificationFailure::Occurs((1, 1), _))));
        }
        {
            let mut tv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ _1 _1 [4] L $ [4] L _1 _1 _1 [3] * _1 _1 [3] * [3] * _1 _1 [3] * [4] L [3] T _1 [3] * _1 _1 _1 _1 _2");
            let t = Expr { ptr: tv.as_mut_ptr() };

            let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ _1 [4] L $ [4] L _1 _1 _2 [3] * _2 _1 [3] * [3] * _2 _1 [3] * [4] L [3] T _1 [3] * _1 _2 _1 _2 _3");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ _1 [4] L $ [4] L _1 _1 _2 [3] * _2 _1 [3] * [3] * _2 _1 [3] * [4] L [3] T _1 [3] * _2 _1 _1 _2 _3");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            assert_eq!(format!("{:?}", to), format!("{:?}", t));
        }
        {
            //
            //
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ _1 _2 [3] * _2 [3] * _1 [3] * _2 _1");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ _1 $ [3] * [3] * _1 _1 _2 [3] * [3] * _1 [3] * _1 _2 [3] * _1 [3] * _1 _2");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
        }
        {
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ $ [3] K _2 _1 [3] T [3] * [3] * _2 _1 _3 [3] K _2 _1");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ $ [3] K _1 [4] L _2 [3] * _2 _1 _3 [3] T [3] * [3] * _2 _1 _3 [3] K _1 _2");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
        }
        {
            // LHS (axiom (= (* (* (* (K $ $) $) $) (a _2 _1 (K _4 _3       ))) (* (* (K _1 (L _2 _4 _3)) _4) (T _3 _4))))
            // RHS (axiom (= (* (* (* (K $ $) $) $) (a _1 _4 (K _3 (T _2 _4)))) (* (* (K _1 (L _2 _4 _3)) _4) (T _3 _4))))
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ $ $ [4] a _2 _1 [3] K _4 _3 [3] * [3] * [3] K _1 [4] L _2 _4 _3 _4 [3] T _3 _4");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ $ $ [4] a _1 _4 [3] K _3 [3] T _2 _4 [3] * [3] * [3] K _1 [4] L _2 _4 _3 _4 [3] T _3 _4");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
        }
        {
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * $ [3] * $ _2 _2 [3] * _1 [3] * [3] * _2 _2 _2");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * $ [3] * $ [3] \\ $ 1 [3] \\ [3] \\ _3 1 1 [3] * [3] / 1 _3 [3] * [3] * _3 _1 _2");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
        }
        {
            let mut xv = parse!("[2] axiom [3] = [3] * [3] * $ [3] T $ $ _3 [3] * [3] * _1 _2 [3] T _3 _2");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!("[2] axiom [3] = [3] * [3] * $ [3] T $ $ [3] T [3] T _2 _3 $ [3] * [3] * _1 _2 [3] T _2 [3] T _4 _3");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
        }
        {
            let mut xv = parse!(r"[2] axiom [3] = [3] * [3] K $ [3] * [3] \ $ [3] \ _2 $ [3] / $ 1 [3] T [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] * _3 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[2] axiom [3] = [3] * [3] K $ [3] * [3] \ $ [3] \ _2 $ [3] / $ 1 [3] T [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] * _3 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // x.serialize2()
            // println!("{}", )

            let tov = vec![0u8; 512];
            let to = Expr { ptr: tov.leak().as_mut_ptr() };

            println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
        }
        {
            let mut xv = parse!(r"[4] exec PC0 [4] , [2] petri [4] ? $ $ $ [2] petri [3] ! _1 _2 [4] exec PC0 $ $ [3] , [2] petri _3 [4] exec PC0 _4 _5");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[4] exec PC0 [4] , [2] petri [4] ? [2] add $ [2] [2] S $ $ [4] ? [2] add $ [2] _2 _3 [3] ! _1 [2] S _4 [2] petri [3] ! [2] add result [2] [2] S Z [2] S Z [4] exec PC0 [4] , [2] petri [4] ? $ $ $ [2] petri [3] ! _5 _6 [4] exec PC0 $ $ [3] , [2] petri _7 [4] exec PC0 _8 _9 [3] , $ $");
            let y = Expr { ptr: yv.as_mut_ptr() };

            // (exec PC0 (, (petri (? (add result) ((S Z) (S Z)) (? (add $) (Z (S Z)) (! result (S _1)))))
            //              (petri (! (add result) ((S Z) (S Z))))
            //              (exec PC0 (, (petri (? $ $ $)) (petri (! _2 _3)) (exec PC0 $ $)) (, (petri _4) (exec PC0 _5 _6))))
            //           (, (petri (? (add _1) (Z (S Z)) (! result (S _1))))
            //              (exec PC0 (, (petri (? _2 _3 _4)) (petri (! _2 _3)) (exec PC0 _5 _6)) (, (petri _4) (exec PC0 _5 _6)))))

            let tov = vec![0u8; 512];
            let to = Expr{ ptr: tov.leak().as_mut_ptr() };

            assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
            let mut oz = ExprZipper::new(to);
            oz.next_child(); oz.next_child(); oz.next_child(); oz.next_child();
            oz.next_descendant(-1, 0); oz.next_descendant(-1, 0);
            let t0 = oz.subexpr();
            t0.unbind(&mut ExprZipper::new(t0));
            // not tested
            oz.next_descendant(-2, 0);
            let t1 = oz.subexpr();
            t1.unbind(&mut ExprZipper::new(t1));
            // reflective call equal to input
            assert_eq!(format!("{:?}", t1), format!("{:?}", x));
        }
    }

    #[test]
    fn test_anti_unify() {
        {
            let mut xv = parse!(r"[2] a a");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[2] a a");
            let y = Expr { ptr: yv.as_mut_ptr() };
            let mut rv = parse!(r"[2] a a");
            let r = Expr { ptr: rv.as_mut_ptr() };

            let mut tov = vec![0u8; 512];
            let to = Expr { ptr: tov.as_mut_ptr() };

            x.anti_unify(y, &mut ExprZipper::new(to));
            println!("{:?}", to);
            assert_eq!(format!("{:?}", to), format!("{:?}", r));
        }
        {
            let mut xv = parse!(r"[2] a a");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[2] a b");
            let y = Expr { ptr: yv.as_mut_ptr() };
            let mut rv = parse!(r"[2] a $");
            let r = Expr { ptr: rv.as_mut_ptr() };

            let mut tov = vec![0u8; 512];
            let to = Expr { ptr: tov.as_mut_ptr() };

            x.anti_unify(y, &mut ExprZipper::new(to));
            println!("{:?}", to);
            assert_eq!(format!("{:?}", to), format!("{:?}", r));
        }
        {
            let mut xv = parse!(r"[2] a a");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[2] b b");
            let y = Expr { ptr: yv.as_mut_ptr() };
            let mut rv = parse!(r"[2] $ _1");
            let r = Expr { ptr: rv.as_mut_ptr() };

            let mut tov = vec![0u8; 512];
            let to = Expr { ptr: tov.as_mut_ptr() };

            x.anti_unify(y, &mut ExprZipper::new(to));
            println!("{:?}", to);
            assert_eq!(format!("{:?}", to), format!("{:?}", r));
        }
        {
            let mut xv = parse!(r"[2] a a");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[2] $ _1");
            let y = Expr { ptr: yv.as_mut_ptr() };
            let mut rv = parse!(r"[2] $ _1");
            let r = Expr { ptr: rv.as_mut_ptr() };

            let mut tov = vec![0u8; 512];
            let to = Expr { ptr: tov.as_mut_ptr() };

            x.anti_unify(y, &mut ExprZipper::new(to));
            println!("{:?}", to);
            assert_eq!(format!("{:?}", to), format!("{:?}", r));
        }
        {
            let mut xv = parse!(r"[2] $ _1");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[2] $ _1");
            let y = Expr { ptr: yv.as_mut_ptr() };
            let mut rv = parse!(r"[2] $ _1");
            let r = Expr { ptr: rv.as_mut_ptr() };

            let mut tov = vec![0u8; 512];
            let to = Expr { ptr: tov.as_mut_ptr() };

            x.anti_unify(y, &mut ExprZipper::new(to));
            println!("{:?}", to);
            assert_eq!(format!("{:?}", to), format!("{:?}", r));
        }
        {
            let mut xv = parse!(r"[2] $ $");
            let x = Expr { ptr: xv.as_mut_ptr() };
            let mut yv = parse!(r"[2] $ _1");
            let y = Expr { ptr: yv.as_mut_ptr() };
            let mut rv = parse!(r"[2] $ $");
            let r = Expr { ptr: rv.as_mut_ptr() };

            let mut tov = vec![0u8; 512];
            let to = Expr { ptr: tov.as_mut_ptr() };

            x.anti_unify(y, &mut ExprZipper::new(to));
            println!("{:?}", to);
            assert_eq!(format!("{:?}", to), format!("{:?}", r));
        }
    }

    #[test]
    fn rel_eq() {
        {
            //       lhs---- rhs----
            // (F $_ ($x $x) ($x $x))
            let mut ev = parse!(r"[4] F $ [2] $ _2 [2] _2 _2");
            let e = Expr { ptr: ev.as_mut_ptr() };
            let lhs = RelExprEnv(ExprEnv{ n: 0, v: 1, offset:  1 + 2 + 1, base: e});
            let rhs = RelExprEnv(ExprEnv{ n: 0, v: 2, offset:  1 + 2 + 1 + 1 + 1 + 1, base: e});
            println!("lhs {}", lhs.0.show());
            println!("rhs {}", rhs.0.show());
            assert_eq!(lhs, rhs);
            assert_eq!({ let mut hx = GxHasher::with_seed(0); lhs.hash(&mut hx); hx.finish() },
                       { let mut hx = GxHasher::with_seed(0); rhs.hash(&mut hx); hx.finish() });
        }
        {
            //       lhs---- rhs----
            // (F $_ ($x $x) ($y $x))
            let mut ev = parse!(r"[4] F $ [2] $ _2 [2] $ _2");
            let e = Expr { ptr: ev.as_mut_ptr() };
            let lhs = RelExprEnv(ExprEnv{ n: 0, v: 1, offset:  1 + 2 + 1, base: e});
            let rhs = RelExprEnv(ExprEnv{ n: 0, v: 2, offset:  1 + 2 + 1 + 1 + 1 + 1, base: e});
            println!("lhs {}", lhs.0.show());
            println!("rhs {}", rhs.0.show());
            assert_ne!(lhs, rhs);
            assert_ne!({ let mut hx = GxHasher::with_seed(0); lhs.hash(&mut hx); hx.finish() },
                       { let mut hx = GxHasher::with_seed(0); rhs.hash(&mut hx); hx.finish() });
        }
        {
            //  l- r-
            // ($x $x)
            let mut ev = parse!(r"[2] $ _1");
            let e = Expr { ptr: ev.as_mut_ptr() };
            let lhs = RelExprEnv(ExprEnv{ n: 0, v: 0, offset: 1, base: e});
            let rhs = RelExprEnv(ExprEnv{ n: 0, v: 1, offset: 2, base: e});
            println!("lhs {}", lhs.0.show());
            println!("rhs {}", rhs.0.show());
            assert_eq!(lhs, rhs);
            assert_eq!({ let mut hx = GxHasher::with_seed(0); lhs.hash(&mut hx); hx.finish() },
                       { let mut hx = GxHasher::with_seed(0); rhs.hash(&mut hx); hx.finish() });
        }
    }
}
