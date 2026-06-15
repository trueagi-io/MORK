use core::f64;
use std::io::{BufRead, Read, Write};
use std::marker::PhantomData;
use std::{mem, process, ptr};
use std::any::Any;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Display;
use std::fs::File;
use std::hint::unreachable_unchecked;
use std::mem::MaybeUninit;
use std::ops::{AddAssign, Coroutine, CoroutineState, MulAssign};
use std::pin::Pin;
use std::ptr::{addr_of, null, null_mut, slice_from_raw_parts, slice_from_raw_parts_mut};
use std::sync::LazyLock;
use std::task::Poll;
use std::time::Instant;
use futures::StreamExt;
use pathmap::ring::{AlgebraicStatus, Lattice};
use mork_expr::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, serialize, Tag, traverseh, ExprEnv, unify, UnificationFailure, apply, destruct, OwnedSourceItem};
use mork_frontend::bytestring_parser::{Parser, ParserError, Context};
use mork_interning::{WritePermit, SharedMapping, SharedMappingHandle};
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;
use mork_frontend::json_parser::Transcriber;
use log::*;
use pathmap::morphisms::Catamorphism;
use pathmap::PathMap;
use eval::EvalScope;
use eval_ffi::{ExprSink, ExprSource};
use linalg::dense::Dense;
use linalg::jit::{einsum_jit, JitInput, Tensor};
use mork_expr::macros::SerializableExpr;
use crate::{expr, pure};
use crate::space::ACT_PATH;

#[derive(Eq, PartialEq, Debug)]
pub(crate) enum WriteResourceRequest {
    BTM(&'static [u8]),
    ACT(&'static str),
    Z3(&'static str),
    Tensor(&'static str),
    TensorMap,
}

impl WriteResourceRequest {
    pub(crate) fn pjoin(&self, other: &Self) -> Option<Self> {
        match self {
            WriteResourceRequest::BTM(s) => {
                match other {
                    WriteResourceRequest::BTM(o) => {
                        // be tightened to only happen when one strictly subsumes the other?
                        // no: partial compare checks for inclusion (or a/\b == a)
                        Some(WriteResourceRequest::BTM(&s[..pathmap::utils::find_prefix_overlap(s, o)]))
                    }
                    _ => { None }
                }
            }
            WriteResourceRequest::ACT(s) => {
                match other {
                    WriteResourceRequest::ACT(o) if s == o => { Some(WriteResourceRequest::ACT(s)) }
                    _ => { None }
                }
            }
            WriteResourceRequest::Z3(s) => {
                match other {
                    WriteResourceRequest::Z3(o) if s == o => { Some(WriteResourceRequest::Z3(s)) }
                    _ => { None }
                }
            }
            WriteResourceRequest::Tensor(s) => {
                match other {
                    WriteResourceRequest::Tensor(o) if s == o => { Some(WriteResourceRequest::Tensor(s)) }
                    _ => { None }
                }
            }
            WriteResourceRequest::TensorMap => {
                match other {
                    WriteResourceRequest::TensorMap => { Some(WriteResourceRequest::TensorMap) }
                    _ => { None }
                }
            }
        }
    }
}

impl PartialOrd for WriteResourceRequest {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            WriteResourceRequest::BTM(s) => {
                if let WriteResourceRequest::BTM(o) = other {
                    s.partial_cmp(o)
                } else { None }
            }
            WriteResourceRequest::ACT(s) => {
                if let WriteResourceRequest::ACT(o) = other {
                    if s == o { Some(Ordering::Equal) } else { None }
                } else { None }
            }
            WriteResourceRequest::Z3(s) => {
                if let WriteResourceRequest::Z3(o) = other {
                    if s == o { Some(Ordering::Equal) } else { None }
                } else { None }
            }
            WriteResourceRequest::Tensor(s) => {
                if let WriteResourceRequest::Tensor(o) = other {
                    if s == o { Some(Ordering::Equal) } else { None }
                } else { None }
            }
            WriteResourceRequest::TensorMap => {
                if let WriteResourceRequest::TensorMap = other {
                    Some(Ordering::Equal)
                } else { None }
            }
        }
    }
}

pub(crate) enum WriteResource<'w, 'a, 'k> {
    BTM(&'w mut WriteZipperTracked<'a, 'k, ()>),
    ACT(()),
    Z3(&'w mut subprocess::Popen),
    Tensor(&'w mut Tensor),
    TensorMap(&'w mut HashMap<OwnedSourceItem, Tensor>),
    
}

// trait JoinLattice  {
//     fn join(x: Self, y: Self) -> Self;
// }
//
// impl JoinLattice for WriteResourceRequest {
//     fn join(x: Self, y: Self) -> Self {
//         match (x, y) {
//             (WriteResourceRequest::BTM(x), WriteResourceRequest::BTM(y)) => {
//                 let i = pathmap::utils::find_prefix_overlap(x, y);
//                 &x[..i] // equiv &y[..i]
//             }
//         }
//     }
// }
//
// impl std::cmp::PartialEq for JoinLattice {
//     fn eq(&self, other: &Self) -> bool {
//         Self::is_bottom(self.meet(other))
//     }
//
// }
//
// impl std::cmp::PartialOrd for JoinLattice {
//     fn lteq(x: Self, y: Self) -> bool {
//         x.join(y).eq(y)
//     }
// }

pub(crate) trait Sink {
    fn new(e: Expr) -> Self;
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest>;
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It, path: &[u8]) where 'a : 'w, 'k : 'w;
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It) -> bool where 'a : 'w, 'k : 'w;
}

fn symbol_bytes(e: Expr) -> &'static [u8] {
    unsafe { e.symbol().expect("expected symbol").as_ref().unwrap() }
}

fn symbol_usize(e: Expr) -> usize {
    std::str::from_utf8(symbol_bytes(e)).expect("box coordinate is not utf-8")
        .parse().expect("box coordinate is not usize")
}

fn symbol_f32(e: Expr) -> f32 {
    std::str::from_utf8(symbol_bytes(e)).expect("box value is not utf-8")
        .parse().expect("box value is not f32")
}

fn tuple_usizes(e: Expr) -> Vec<usize> {
    let mut args = Vec::new();
    ExprEnv::new(0, e).args(&mut args);
    assert!(!args.is_empty(), "coordinate must be a tuple like (, 0 0 0)");
    assert_eq!(symbol_bytes(args[0].subsexpr()), b",", "coordinate must use the , tuple functor");
    args[1..].iter().map(|arg| symbol_usize(arg.subsexpr())).collect()
}

fn tuple_strings(e: Expr) -> Vec<String> {
    let mut args = Vec::new();
    ExprEnv::new(0, e).args(&mut args);
    assert!(!args.is_empty(), "expected a tuple like (, A B)");
    assert_eq!(symbol_bytes(args[0].subsexpr()), b",", "tuple must use the , functor");
    args[1..]
        .iter()
        .map(|arg| std::str::from_utf8(symbol_bytes(arg.subsexpr())).expect("tuple symbol is not utf-8").to_owned())
        .collect()
}

fn tensor_shape(tensor: &Tensor) -> Vec<usize> {
    match tensor {
        Tensor::Dense(dense) => dense.shape.clone(),
        Tensor::Csr(sparse) => sparse.shape.clone(),
    }
}

fn infer_einsum_output_shapes(input_specs: &[String], output_specs: &[String], input_shapes: &[Vec<usize>]) -> Vec<Vec<usize>> {
    assert_eq!(input_specs.len(), input_shapes.len(), "einsum input spec/name count mismatch");
    let mut dims = [0usize; 26];
    let mut dim_set = [false; 26];

    for (input, shape) in input_specs.iter().zip(input_shapes.iter()) {
        assert!(!input.is_empty(), "einsum input specs cannot be scalar");
        assert_eq!(input.len(), shape.len(), "einsum input spec {input} rank does not match tensor shape {:?}", shape);
        for (axis, ch) in input.bytes().enumerate() {
            assert!(ch.is_ascii_lowercase(), "einsum index '{}' must be lowercase ascii", ch as char);
            let slot = (ch - b'a') as usize;
            if dim_set[slot] {
                assert_eq!(dims[slot], shape[axis], "einsum dimension mismatch for index '{}'", ch as char);
            } else {
                dims[slot] = shape[axis];
                dim_set[slot] = true;
            }
        }
    }

    output_specs.iter().map(|output| {
        output.bytes().map(|ch| {
            assert!(ch.is_ascii_lowercase(), "einsum output index '{}' must be lowercase ascii", ch as char);
            let slot = (ch - b'a') as usize;
            assert!(dim_set[slot], "einsum output index '{}' is not bound by an input", ch as char);
            dims[slot]
        }).collect()
    }).collect()
}

fn tensor_matches_dense(existing: Option<&Tensor>, dense: &Dense<f32>) -> bool {
    match existing {
        Some(Tensor::Dense(old)) => old.shape == dense.shape && old.data == dense.data,
        _ => false,
    }
}

fn tensor_linear_index(shape: &[usize], coord: &[usize]) -> usize {
    debug_assert_eq!(shape.len(), coord.len());
    let mut idx = 0usize;
    let mut stride = 1usize;
    for (&k, &dim) in coord.iter().rev().zip(shape.iter().rev()) {
        debug_assert!(k < dim);
        idx += k * stride;
        stride *= dim;
    }
    idx
}

fn tensor_coordinate(mut index: usize, shape: &[usize]) -> Vec<usize> {
    let mut coord = vec![0; shape.len()];
    for axis in (0..shape.len()).rev() {
        let dim = shape[axis];
        coord[axis] = index % dim;
        index /= dim;
    }
    coord
}

fn copy_dense_tensor(dst: &mut Dense<f32>, src: &Dense<f32>) {
    assert!(src.shape.len() <= dst.shape.len(), "cannot copy a higher-rank tensor into a lower-rank tensor");
    let lead = dst.shape.len() - src.shape.len();
    for dst_linear in 0..dst.data.len() {
        let dst_coord = tensor_coordinate(dst_linear, &dst.shape);
        let src_coord = &dst_coord[lead..];
        if src_coord.iter().zip(src.shape.iter()).all(|(index, dim)| index < dim) {
            let src_idx = tensor_linear_index(&src.shape, src_coord);
            let value = src.data[src_idx];
            if value != 0.0 {
                dst.data[dst_linear] += value;
            }
        }
    }
}

fn add_tensor_cube(dense: &mut Dense<f32>, cube: &TensorCube) {
    assert!(cube.start.len() <= dense.shape.len(), "tensor-cubes cube rank exceeds tensor rank");
    let lead = dense.shape.len() - cube.start.len();
    let mut start = vec![0; dense.shape.len()];
    let mut end = dense.shape.clone();
    for axis in 0..cube.start.len() {
        start[lead + axis] = cube.start[axis];
        end[lead + axis] = cube.end[axis];
    }

    let mut coord = start.clone();
    loop {
        let idx = tensor_linear_index(&dense.shape, &coord);
        dense.data[idx] += cube.value;

        for axis in (0..coord.len()).rev() {
            coord[axis] += 1;
            if coord[axis] < end[axis] {
                break;
            }
            if axis == 0 {
                return;
            }
            coord[axis] = start[axis];
        }
    }
}

pub struct CompatSink { e: Expr, changed: bool }

impl Sink for CompatSink {
    fn new(e: Expr) -> Self { CompatSink { e, changed: false } }
    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| self.e.span()).as_ref().unwrap() }[..];
        trace!(target: "sink", "+ (compat) requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[wz.root_prefix_path().len()..];
        trace!(target: "sink", "+ (compat) at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "+ (compat) sinking '{}'", serialize(mpath));
        wz.move_to_path(mpath);
        self.changed |= wz.set_val(()).is_none();
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It) -> bool where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "+ (compat) finalizing");
        self.changed
    }
}

pub struct AddSink { e: Expr, changed: bool }
impl Sink for AddSink {
    fn new(e: Expr) -> Self { AddSink { e, changed: false } }
    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| self.e.span()).as_ref().unwrap() }[3..];
        trace!(target: "sink", "+ requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[3+wz.root_prefix_path().len()..];
        trace!(target: "sink", "+ at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "+ sinking '{}'", serialize(mpath));
        wz.move_to_path(mpath);
        self.changed |= wz.set_val(()).is_none();
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It) -> bool where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "+ finalizing");
        self.changed
    }
}

// (U <expr>)
pub struct USink {
    e               : Expr,
    buf             : Option<*mut u8>,
    tmp             : Option<*mut u8>,
    conflict        : bool,
    tmp_expr_env    : Vec<(ExprEnv, ExprEnv)>,
    tmp_stack       : Vec<(u8, u8)>,
    tmp_assignments : Vec<(u8, u8)>,
    last_len        : usize,
}
impl Sink for USink {
    fn new(e: Expr) -> Self {
        USink {
            e,
            buf: None,
            tmp: None,
            conflict: false ,
            tmp_expr_env: Vec::new(),
            tmp_stack:
            Vec::new(),
            tmp_assignments: Vec::new(),
            last_len : usize::MAX
        }
    }
    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| self.e.span()).as_ref().unwrap() }[3..];
        trace!(target: "sink", "U requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        // we could be way more parsimonious not unifying the prefix over and over again
        // let mpath = &path[3+wz.root_prefix_path().len()..];
        trace!(target: "sink", "U new expr '{}'", serialize(&path[3..]));
        if self.conflict { return }
        if let Some(e) = self.buf {
            let mut tmp = self.tmp.unwrap();
            let eau = Expr{ ptr: e };

            let mut cursor = std::io::Cursor::new(unsafe { core::slice::from_raw_parts_mut(tmp, 1 << 32) });

            if !mork_expr::unifies_reuse_state(
                eau,
                Expr{ ptr: path[3..].as_ptr().cast_mut() },
                &mut cursor,
                &mut self.tmp_expr_env,
                &mut self.tmp_stack,
                &mut self.tmp_assignments
            ) {
                self.conflict = true;
                return;
            }

            self.last_len = cursor.position() as usize;


            std::mem::swap(&mut self.buf, &mut self.tmp);
        } else {
            self.buf = Some(unsafe { std::alloc::alloc(std::alloc::Layout::array::<u8>(1 << 32).unwrap()) });
            self.tmp = Some(unsafe { std::alloc::alloc(std::alloc::Layout::array::<u8>(1 << 32).unwrap()) });
            unsafe { std::ptr::copy_nonoverlapping(path[3..].as_ptr(), self.buf.unwrap(), path[3..].len()) }
            self.last_len = path[3..].len();
        }


    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "U finalizing");
        if self.conflict {
            trace!(target: "sink", "U conflict");
            return false;
        }
        match self.buf.take() {
            None => {
                trace!(target: "sink", "U empty");
                false
            }
            Some(buf) => {
                let buf_slice = unsafe { slice_from_raw_parts(buf as *const u8, self.last_len).as_ref().unwrap() };
                trace!(target: "sink", "U unified expression '{}'", serialize(buf_slice));
                let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
                wz.move_to_path(&buf_slice[wz.root_prefix_path().len()..]);
                wz.set_val(());
                true
            }
        }
    }
}

// (AU <expr>)
pub struct AUSink { e: Expr, buf: Option<Box<[u8]>>, tmp: Option<Box<[u8]>>, last: usize }
impl Sink for AUSink {
    fn new(e: Expr) -> Self {
        AUSink { e, buf: None, tmp: None, last: usize::MAX }
    }
    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| self.e.span()).as_ref().unwrap() }[4..];
        trace!(target: "sink", "AU requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        // we could be way more parsimonious not anti-unifying the prefix over and over again
        // let mpath = &path[4+wz.root_prefix_path().len()..];
        trace!(target: "sink", "AU new expr '{}'", serialize(&path[4..]));
        if let Some(mut e) = self.buf.as_mut() {
            let mut tmp = self.tmp.as_mut().unwrap();
            let eau = Expr{ ptr: (*e).as_mut_ptr() };
            let mut wz = ExprZipper::new(Expr{ ptr: (*tmp).as_mut_ptr() });
            eau.anti_unify(Expr{ ptr: path[4..].as_ptr().cast_mut() }, &mut wz).unwrap();
            std::mem::swap(&mut self.buf, &mut self.tmp);
            self.last = wz.loc;
        } else {
            self.buf = Some(path[4..].to_vec().into_boxed_slice());
            self.tmp = self.buf.clone();
        }
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "AU finalizing");
        match self.buf.take() {
            None => {
                trace!(target: "sink", "AU empty");
                false
            }
            Some(buf) => {
                trace!(target: "sink", "AU anti-unified expression '{}'", serialize(&buf[..self.last]));
                let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
                wz.move_to_path(&buf[wz.root_prefix_path().len()..self.last]);
                wz.set_val(());
                true
            }
        }
    }
}

pub struct ACTSink { e: Expr, file: &'static str, tmp: PathMap<()> }
impl Sink for ACTSink {
    fn new(e: Expr) -> Self {
        destruct!(e, ("ACT" {act: &str} se), {
            return ACTSink { e, file: act, tmp: PathMap::new() }
        }, _err => { panic!("act not the right shape") });
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        trace!(target: "sink", "ACT requesting {}", self.file);
        std::iter::once(WriteResourceRequest::ACT(self.file))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "ACT sinking '{}'", serialize(&path[1+1+3+1+self.file.len()..]));
        self.tmp.insert(&path[1+1+3+1+self.file.len()..], ());
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "ACT finalizing");
        let _ = it.next().unwrap() else { unreachable!() };
        pathmap::arena_compact::ArenaCompactTree::dump_from_zipper(
            self.tmp.read_zipper(), |_v| 0, format!("{}{}.act", ACT_PATH, self.file)).map(|_tree| ());
        true
    }
}

pub struct RemoveSink { e: Expr, remove: PathMap<()> }
// perhaps more performant to graft, remove*, and graft back?
impl Sink for RemoveSink {
    fn new(e: Expr) -> Self { RemoveSink { e, remove: PathMap::new() } }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        // !! we're never grabbing the full expression path, because then we don't have the ability to remove the root value
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[3..];
        trace!(target: "sink", "- requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[3+wz.root_prefix_path().len()..];
        trace!(target: "sink", "- at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "- sinking '{}'", serialize(mpath));
        self.remove.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "- finalizing by subtracting {} at '{}'", self.remove.val_count(), serialize(wz.origin_path()));
        // match self.remove.remove(&[]) {
        //     None => {}
        //     Some(s) => {
        //         println!("has root");
        //         wz.remove_val(true);
        //         println!("val not removed");
        //     }
        // }
        match wz.subtract_into(&self.remove.read_zipper(), true) {
            AlgebraicStatus::Element => { true }
            AlgebraicStatus::Identity => { false }
            AlgebraicStatus::None => { true } // GOAT maybe not?
        }
    }
}

pub struct HeadTailSink<const head: bool> { e: Expr, extrema: PathMap<()>, skip: usize, count: usize, max: usize, extremum: Vec<u8> }
impl <const head: bool> Sink for HeadTailSink<head> {
    fn new(e: Expr) -> Self {
        let mut ez = ExprZipper::new(e); ez.next(); ez.next();
        let max_s = ez.item().err().expect("cnt can not be an expression or variable");
        let max: usize = str::from_utf8(max_s).expect("string encoded numbers for now").parse().expect("a number");
        assert_ne!(max, 0);
        Self { e, extrema: PathMap::new(), skip: 1 + 1+4 + 1+max_s.len(), count: 0, max, extremum: vec![] }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[self.skip..];
        trace!(target: "sink", "head/tail requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[self.skip+wz.root_prefix_path().len()..];
        trace!(target: "sink", "head/tail at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        if self.count == self.max {
            if (if head { &self.extremum[..] <= mpath } else { &self.extremum[..] >= mpath }) {
                trace!(target: "sink", "head/tail at max capacity ignoring '{}'", serialize(mpath));
                // doesn't displace any path
            } else {
                trace!(target: "sink", "head/tail at max capacity replacing '{}' with '{}'", serialize(&self.extremum[..]), serialize(mpath));
                assert!(self.extrema.insert(mpath, ()).is_none());
                self.extrema.remove(&self.extremum[..]);
                let mut rz = self.extrema.read_zipper();
                if head { rz.descend_last_path(); }
                else { rz.to_next_val(); }
                self.extremum.clear();
                self.extremum.extend_from_slice(rz.path()); // yikes, throwing away our needless allocation
            }
        } else {
            if &self.extremum[..] <= mpath {
                if self.extrema.insert(mpath, ()).is_none() {
                    trace!(target: "sink", "head/tail adding new top at '{}'", serialize(mpath));
                    self.extremum.clear();
                    self.extremum.extend_from_slice(mpath);
                    self.count += 1;
                }
            } else {
                if self.extrema.insert(mpath, ()).is_none() {
                    trace!(target: "sink", "head/tail adding '{}'", serialize(mpath));
                    self.count += 1;
                }
            }
        }
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "head/tail finalizing by joining {} at '{}'", self.count, serialize(wz.origin_path()));

        match wz.join_into(&self.extrema.read_zipper()) {
            AlgebraicStatus::Element => { true }
            AlgebraicStatus::Identity => { false }
            AlgebraicStatus::None => { true } // GOAT maybe not?
        }
    }
}

#[cfg(feature = "wasm")]
pub struct WASMSink { e: Expr, skip: usize, changed: bool, module: wasmtime::Module, store: wasmtime::Store<()>, instance: wasmtime::Instance }

#[cfg(feature = "wasm")]
static ENGINE_LINKER: LazyLock<(wasmtime::Engine, wasmtime::Linker<()>)> = LazyLock::new(|| {
    let mut config = wasmtime::Config::new();
    config.wasm_multi_memory(true);
    config.strategy(wasmtime::Strategy::Cranelift);
    config.signals_based_traps(true);
    config.memory_reservation(1 << 32);
    config.memory_guard_size(1 << 32);
    #[cfg(all(target_feature = "avx2"))]
    unsafe {
        config.cranelift_flag_enable("has_sse3");
        config.cranelift_flag_enable("has_ssse3");
        config.cranelift_flag_enable("has_sse41");
        config.cranelift_flag_enable("has_sse42");
        config.cranelift_flag_enable("has_avx");
        config.cranelift_flag_enable("has_avx2");
        config.cranelift_flag_enable("has_bmi1");
        config.cranelift_flag_enable("has_bmi2");
        config.cranelift_flag_enable("has_lzcnt");
        config.cranelift_flag_enable("has_popcnt");
        config.cranelift_flag_enable("has_fma");
    }
    #[cfg(all(target_feature = "avx512"))]
    unsafe {
        config.cranelift_flag_enable("has_avx512bitalg");
        config.cranelift_flag_enable("has_avx512dq");
        config.cranelift_flag_enable("has_avx512vl");
        config.cranelift_flag_enable("has_avx512vbmi");
        config.cranelift_flag_enable("has_avx512f");
    }

    let engine = wasmtime::Engine::new(&config).unwrap();

    let mut linker = wasmtime::Linker::new(&engine);

    linker.func_wrap("", "i32.bswap", |param: i32| param.to_be()).unwrap();
    linker.func_wrap("", "i64.bswap", |param: i64| param.to_be()).unwrap();

    (engine, linker)
});

#[cfg(feature = "wasm")]
static mut LINKER: Option<wasmtime::Linker<()>> = None;
macro_rules! wasm_ctx { () => { r#"
(module
  (import "" "i32.bswap" (func $i32.bswap (param i32) (result i32)))
  (import "" "i64.bswap" (func $i64.bswap (param i64) (result i64)))

  (memory $in 1)
  (export "in" (memory $in))
  (memory $out 1)
  (export "out" (memory $out))
  (memory $local 1)

  (func (export "_otf_grounding")
    {:?}
  )
)
"# } }


#[cfg(feature = "wasm")]
impl Sink for WASMSink {
    fn new(e: Expr) -> Self {
        let mut ez = ExprZipper::new(e); ez.next(); ez.next();
        let program_e = ez.subexpr();
        let wat = format!(wasm_ctx!(), program_e);
        let module = wasmtime::Module::new(&ENGINE_LINKER.0, wat).unwrap();
        let mut store = wasmtime::Store::new(&ENGINE_LINKER.0, ());
        let instance = (&ENGINE_LINKER.1).instantiate(&mut store, &module).unwrap();

        WASMSink { e, skip: 1 + 1+4 + program_e.span().len(), changed: false, module, store, instance }
    }
    fn request(&self) -> impl Iterator<Item=&'static [u8]> {
        // let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[self.skip..];
        // trace!(target: "sink", "wasm requesting {}", serialize(p));
        // std::iter::once(p)
        static empty: [u8; 0] = [];
        std::iter::once(&empty[..])
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item=&'w mut WriteZipperUntracked<'a, 'k, ()>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let mut wz = it.next().unwrap();
        let mpath = &path[self.skip+wz.root_prefix_path().len()..];
        trace!(target: "sink", "wasm at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "wasm input '{}'", serialize(mpath));
        let imem = self.instance.get_memory(&mut self.store, "in").unwrap();
        imem.write(&mut self.store, 0, mpath).unwrap();
        let run = self.instance.get_typed_func::<(), ()>(&mut self.store, "_otf_grounding").unwrap();
        match run.call(&mut self.store, ()) {
            Ok(()) => {
                let omem = self.instance.get_memory(&mut self.store, "out").unwrap().data(&mut self.store);
                let ospan = unsafe { Expr{ ptr: omem.as_ptr().cast_mut() }.span().as_ref().unwrap() };
                trace!(target: "sink", "wasm output '{}'", serialize(ospan));
                wz.move_to_path(ospan);
                self.changed |= wz.set_val(()).is_none();
            }
            Err(e) => {
                trace!(target: "sink", "wasm error {:?}", e);
            }
        }

    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item=&'w mut WriteZipperUntracked<'a, 'k, ()>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w  {
        trace!(target: "sink", "wasm finalizing");
        self.changed
    }
}

// ($k $x) (f $x $y)
// (count (count of $k is $i) $i ($x $y))   unify
// (count (count of r2 is $i) $i (P Q))
// (count (count of r2 is 3) 3 ($x $y))
pub struct CountSink { e: Expr, unique: PathMap<()> }
impl Sink for CountSink {
    fn new(e: Expr) -> Self {
        CountSink { e, unique: PathMap::new() }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[7..];
        trace!(target: "sink", "count requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[7+wz.root_prefix_path().len()..];
        let ctx = unsafe { Expr { ptr: mpath.as_ptr().cast_mut() } };
        trace!(target: "sink", "count at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "count registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "count finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new(); std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input.write_zipper_at_path(wz.root_prefix_path()).graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(unsafe { prz_ptr.cast_mut().as_mut().unwrap() }, &[ExprEnv::new(0, Expr{ ptr: v.as_ptr().cast_mut() })], |refs_bindings, loc| {
            let cnt = prz.val_count();
            trace!(target: "sink", "'{}' and under {}", serialize(prz.path()), cnt);
            let clen = prz.path().len();
            let cnt_str = cnt.to_string();
            if prz.descend_to_existing_byte(item_byte(Tag::SymbolSize(cnt_str.len() as _))) {
                let descended = prz.descend_to_existing(cnt_str.as_bytes());
                if descended == cnt_str.len() {
                    let fixed = &prz.path()[..prz.path().len()-(1+cnt_str.len())];
                    trace!(target: "sink", "fixed guard {}", serialize(fixed));
                    wz.move_to_path(fixed);
                    wz.set_val(());
                    changed |= true;
                }
                prz.ascend(descended + 1);
            }
            if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                let ignored = &prz.path()[..prz.path().len()-1];
                trace!(target: "sink", "ignored guard {}", serialize(ignored));
                wz.move_to_path(ignored);
                wz.set_val(());
                changed |= true;
                prz.ascend_byte();
            } 
            if prz.descend_first_byte() {
                if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len()-1]) {
                    let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                    cntv.extend_from_slice(cnt_str.as_bytes());
                    let varref = &prz.path()[..prz.path().len()-1];
                    let ie = Expr { ptr: (&varref[0] as *const u8).cast_mut() };
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() });
                    trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                    let os = ie.substitute_one_de_bruijn(k, Expr{ ptr: cntv.as_mut_ptr() }, &mut oz);
                    unsafe { buffer.set_len(oz.loc) }
                    trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    wz.set_val(());
                    changed |= true
                }
                prz.ascend_byte();
            }
            true
        });
        changed
    }
}

pub struct HashSink { e: Expr, unique: PathMap<()> }
impl Sink for HashSink {
    fn new(e: Expr) -> Self {
        Self { e, unique: PathMap::new() }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[6..];
        trace!(target: "sink", "hash requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[6+wz.root_prefix_path().len()..];
        let ctx = unsafe { Expr { ptr: mpath.as_ptr().cast_mut() } };
        trace!(target: "sink", "hash at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "hash registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "hash finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new(); std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input.write_zipper_at_path(wz.root_prefix_path()).graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(unsafe { prz_ptr.cast_mut().as_mut().unwrap() }, &[ExprEnv::new(0, Expr{ ptr: v.as_ptr().cast_mut() })], |refs_bindings, loc| {
            for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                let Tag::SymbolSize(size) = byte_item(b) else { unreachable!() };
                // if size != 16 { trace!(target: "sink", "hash guard not 16 bytes {size}"); continue }
                prz.descend_to_byte(b);
                debug_assert!(prz.path_exists());
                if !prz.descend_first_k_path(size as _) { unreachable!() }
                loop {
                    let clen = prz.origin_path().len();

                    let hash = prz.fork_read_zipper().hash();

                    let cnt_str = hash.to_be_bytes();
                    trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), hash);
                    assert_eq!(prz.origin_path().len(), clen);

                    let fixed_number = &prz.origin_path()[prz.origin_path().len()-(size as usize)..];
                    if fixed_number == &cnt_str[..] {
                        let fixed = &prz.origin_path()[..prz.origin_path().len()-(1+size as usize)];
                        trace!(target: "sink", "fixed payload {}", serialize(fixed));
                        wz.move_to_path(fixed);
                        wz.set_val(());
                        changed |= true;
                    }

                    if !prz.to_next_k_path(size as _) { break }
                }
                if !prz.ascend_byte() { unreachable!() }
            }

            if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                let ignored = &prz.path()[..prz.path().len()-1];
                trace!(target: "sink", "ignored guard {}", serialize(ignored));
                wz.move_to_path(ignored);
                wz.set_val(());
                changed |= true;
                prz.ascend_byte();
            }
            if prz.descend_first_byte() {
                if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len()-1]) {
                    let hash = prz.fork_read_zipper().hash();
                    let cnt_str = hash.to_be_bytes();

                    let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                    cntv.extend_from_slice(&cnt_str[..]);
                    let varref = &prz.path()[..prz.path().len()-1];
                    let ie = Expr { ptr: (&varref[0] as *const u8).cast_mut() };
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() });
                    trace!(target: "sink", "hash ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                    let os = ie.substitute_one_de_bruijn(k, Expr{ ptr: cntv.as_mut_ptr() }, &mut oz);
                    unsafe { buffer.set_len(oz.loc) }
                    trace!(target: "sink", "hash ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    wz.set_val(());
                    changed |= true
                }
                prz.ascend_byte();
            }
            true
        });
        changed
    }
}


pub struct AndSink { e: Expr, unique: PathMap<()> }
impl Sink for AndSink {
    fn new(e: Expr) -> Self {
        Self { e, unique: PathMap::new() }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[5..];
        trace!(target: "sink", "and requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[5+wz.root_prefix_path().len()..];
        let ctx = unsafe { Expr { ptr: mpath.as_ptr().cast_mut() } };
        trace!(target: "sink", "and at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "and registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "and finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new(); std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input.write_zipper_at_path(wz.root_prefix_path()).graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(unsafe { prz_ptr.cast_mut().as_mut().unwrap() }, &[ExprEnv::new(0, Expr{ ptr: v.as_ptr().cast_mut() })], |refs_bindings, loc| {

            for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                let Tag::SymbolSize(size) = byte_item(b) else { unreachable!() };
                println!("and size {size}");
                prz.descend_to_byte(b);
                debug_assert!(prz.path_exists());
                if !prz.descend_first_k_path(size as _) { unreachable!() }
                loop {
                    let mut total = !0u8;
                    let clen = prz.origin_path().len();

                    let mut rz = prz.fork_read_zipper();
                    while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                        total &= p[clen+1];
                    }
                    let cnt_str = [total];
                    trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), total);
                    assert_eq!(prz.origin_path().len(), clen);

                    let fixed_number = &prz.origin_path()[prz.origin_path().len()-(size as usize)..];
                    if fixed_number == &cnt_str[..] {
                        let fixed = &prz.origin_path()[..prz.origin_path().len()-(1+size as usize)];
                        trace!(target: "sink", "fixed payload {}", serialize(fixed));
                        wz.move_to_path(fixed);
                        wz.set_val(());
                        changed |= true;
                    }

                    if !prz.to_next_k_path(size as _) { break }
                }
                if !prz.ascend_byte() { unreachable!() }
            }

            if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                let ignored = &prz.path()[..prz.path().len()-1];
                trace!(target: "sink", "ignored guard {}", serialize(ignored));
                wz.move_to_path(ignored);
                wz.set_val(());
                changed |= true;
                prz.ascend_byte();
            }
            if prz.descend_first_byte() {
                if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len()-1]) {
                    let mut total = !0u8;
                    let clen = prz.path().len();
                    let mut rz = prz.fork_read_zipper();
                    while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "and path {:?}", serialize(p));
                        trace!(target: "sink", "and path {:?}", serialize(&p[clen+1..]));
                        total &= p[clen+1];
                    }
                    let cnt_str = [total];

                    let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                    cntv.extend_from_slice(&cnt_str[..]);
                    let varref = &prz.path()[..prz.path().len()-1];
                    let ie = Expr { ptr: (&varref[0] as *const u8).cast_mut() };
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() });
                    trace!(target: "sink", "and ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                    let os = ie.substitute_one_de_bruijn(k, Expr{ ptr: cntv.as_mut_ptr() }, &mut oz);
                    unsafe { buffer.set_len(oz.loc) }
                    trace!(target: "sink", "and ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    wz.set_val(());
                    changed |= true
                }
                prz.ascend_byte();
            }
            true
        });
        changed
    }
}

pub struct SumSink { e: Expr, unique: PathMap<()> }
impl Sink for SumSink {
    fn new(e: Expr) -> Self {
        SumSink { e, unique: PathMap::new() }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[5..];
        trace!(target: "sink", "sum requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[5+wz.root_prefix_path().len()..];
        let ctx = unsafe { Expr { ptr: mpath.as_ptr().cast_mut() } };
        trace!(target: "sink", "sum at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "sum registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "sum finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new(); std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input.write_zipper_at_path(wz.root_prefix_path()).graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(unsafe { prz_ptr.cast_mut().as_mut().unwrap() }, &[ExprEnv::new(0, Expr{ ptr: v.as_ptr().cast_mut() })], |refs_bindings, loc| {

            for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                let Tag::SymbolSize(size) = byte_item(b) else { unreachable!() };
                prz.descend_to_byte(b);
                debug_assert!(prz.path_exists());
                if !prz.descend_first_k_path(size as _) { unreachable!() }
                loop {
                    let mut total = 0u32;
                    let clen = prz.origin_path().len();

                    let mut rz = prz.fork_read_zipper();
                    while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                        total += u32::from_str_radix(str::from_utf8(&p[clen+1..]).unwrap(), 10).unwrap();
                    }
                    let cnt_str = total.to_string();
                    trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), total);
                    assert_eq!(prz.origin_path().len(), clen);

                    let fixed_number = &prz.origin_path()[prz.origin_path().len()-(size as usize)..];
                    if fixed_number == cnt_str.as_bytes() {
                        let fixed = &prz.origin_path()[..prz.origin_path().len()-(1+size as usize)];
                        trace!(target: "sink", "fixed payload {}", serialize(fixed));
                        wz.move_to_path(fixed);
                        wz.set_val(());
                        changed |= true;
                    }

                    if !prz.to_next_k_path(size as _) { break }
                }
                if !prz.ascend_byte() { unreachable!() }
            }

            if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                let ignored = &prz.path()[..prz.path().len()-1];
                trace!(target: "sink", "ignored guard {}", serialize(ignored));
                wz.move_to_path(ignored);
                wz.set_val(());
                changed |= true;
                prz.ascend_byte();
            }
            if prz.descend_first_byte() {
                if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len()-1]) {
                    let mut total = 0u32;
                    let clen = prz.path().len();
                    let mut rz = prz.fork_read_zipper();
                    while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "path {:?}", serialize(p));
                        trace!(target: "sink", "path {:?}", serialize(&p[clen+1..]));
                        total += u32::from_str_radix(str::from_utf8(&p[clen+1..]).unwrap(), 10).unwrap();
                    }
                    let cnt_str = total.to_string();

                    let mut cntv = vec![item_byte(Tag::SymbolSize(cnt_str.len() as _))];
                    cntv.extend_from_slice(cnt_str.as_bytes());
                    let varref = &prz.path()[..prz.path().len()-1];
                    let ie = Expr { ptr: (&varref[0] as *const u8).cast_mut() };
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() });
                    trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                    let os = ie.substitute_one_de_bruijn(k, Expr{ ptr: cntv.as_mut_ptr() }, &mut oz);
                    unsafe { buffer.set_len(oz.loc) }
                    trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    wz.set_val(());
                    changed |= true
                }
                prz.ascend_byte();
            }
            true
        });
        changed
    }
}


struct Sum;
struct Min;
struct Max;
struct Prod;

trait FloatReduction {
    const NAME : &'static str;
    const ACC  : f64;
    fn op(acc  : &mut f64, new : f64);
}
impl FloatReduction for Sum {
    const NAME : &'static str= "fsum";
    const ACC  : f64 = 0.0;
    fn op(acc : &mut f64, new : f64) { acc.add_assign(new); }
}
impl FloatReduction for Min {
    const NAME : &'static str= "fmin";
    const ACC  : f64 = f64::MAX;
    fn op(acc : &mut f64, new : f64) { *acc = (*acc).min(new) }
}
impl FloatReduction for Max {
    const NAME : &'static str= "fmax";
    const ACC  : f64 = f64::MIN;
    fn op(acc : &mut f64, new : f64) { *acc = (*acc).max(new) }
}
impl FloatReduction for Prod {
    const NAME : &'static str= "fprod";
    const ACC  : f64 = 1.0;
    fn op(acc : &mut f64, new : f64) { acc.mul_assign(new) }
}


pub struct FloatReductionSink<Reduction> { e: Expr, unique: PathMap<()>, boo : PhantomData<Reduction> }
impl<Reduction : FloatReduction> Sink for FloatReductionSink<Reduction> {
    fn new(e: Expr) -> Self {
        Self { e, unique: PathMap::new(), boo : PhantomData }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[2+Reduction::NAME.len()..];
        trace!(target: "sink", "{} requesting {}", Reduction::NAME, serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[2+Reduction::NAME.len()+wz.root_prefix_path().len()..];
        let ctx = unsafe { Expr { ptr: mpath.as_ptr().cast_mut() } };
        trace!(target: "sink", "{} at '{}' sinking raw '{}'", Reduction::NAME, serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "{} registering in ctx {:?}", Reduction::NAME, serialize(mpath));
        self.unique.insert(mpath, ());
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "{} finalizing by reducing {} at '{}'", Reduction::NAME, self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new(); std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input.write_zipper_at_path(wz.root_prefix_path()).graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(unsafe { prz_ptr.cast_mut().as_mut().unwrap() }, &[ExprEnv::new(0, Expr{ ptr: v.as_ptr().cast_mut() })], |refs_bindings, loc| {

            for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                let Tag::SymbolSize(size) = byte_item(b) else { unreachable!() };
                prz.descend_to_byte(b);
                debug_assert!(prz.path_exists());
                if !prz.descend_first_k_path(size as _) { unreachable!() }
                loop {
                    let mut total = Reduction::ACC;
                    let clen = prz.origin_path().len();

                    let mut rz = prz.fork_read_zipper();
                    while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                        Reduction::op(&mut total, str::parse::<f64>(str::from_utf8(&p[clen+1..]).unwrap()).unwrap());
                    }
                    let min_str = total.to_string();
                    trace!(target: "sink", "'{}' and under {}", serialize(prz.origin_path()), total);
                    assert_eq!(prz.origin_path().len(), clen);

                    let fixed_number = &prz.origin_path()[prz.origin_path().len()-(size as usize)..];
                    if fixed_number == min_str.as_bytes() {
                        let fixed = &prz.origin_path()[..prz.origin_path().len()-(1+size as usize)];
                        trace!(target: "sink", "fixed payload {}", serialize(fixed));
                        wz.move_to_path(fixed);
                        wz.set_val(());
                        changed |= true;
                    }

                    if !prz.to_next_k_path(size as _) { break }
                }
                if !prz.ascend_byte() { unreachable!() }
            }

            if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                let ignored = &prz.path()[..prz.path().len()-1];
                trace!(target: "sink", "ignored guard {}", serialize(ignored));
                wz.move_to_path(ignored);
                wz.set_val(());
                changed |= true;
                prz.ascend_byte();
            }
            if prz.descend_first_byte() {
                if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len()-1]) {
                    let mut total = Reduction::ACC;
                    let clen = prz.path().len();
                    let mut rz = prz.fork_read_zipper();
                    while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "path {:?}", serialize(p));
                        trace!(target: "sink", "path {:?}", serialize(&p[clen+1..]));
                        Reduction::op(&mut total, str::parse::<f64>(str::from_utf8(&p[clen+1..]).unwrap()).unwrap());
                    }
                    let min_str = total.to_string();

                    let mut cntv = vec![item_byte(Tag::SymbolSize(min_str.len() as _))];
                    cntv.extend_from_slice(min_str.as_bytes());
                    let varref = &prz.path()[..prz.path().len()-1];
                    let ie = Expr { ptr: (&varref[0] as *const u8).cast_mut() };
                    let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() });
                    trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&cntv[..]));
                    let os = ie.substitute_one_de_bruijn(k, Expr{ ptr: cntv.as_mut_ptr() }, &mut oz);
                    unsafe { buffer.set_len(oz.loc) }
                    trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                    wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                    wz.set_val(());
                    changed |= true
                }
                prz.ascend_byte();
            }
            true
        });
        changed
    }
}


// (pure (result $x) $x (f32_from_string 0.2))
#[cfg(feature = "grounding")]
pub struct PureSink { e: Expr, unique: PathMap<()> , scope: EvalScope }
impl Sink for PureSink {
    fn new(e: Expr) -> Self {
        let mut scope = EvalScope::new();
        pure::register(&mut scope);
        PureSink { e, unique: PathMap::new(), scope }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[6..];
        trace!(target: "sink", "count requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[6+wz.root_prefix_path().len()..];
        let ctx = unsafe { Expr { ptr: mpath.as_ptr().cast_mut() } };
        trace!(target: "sink", "pure at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        trace!(target: "sink", "pure registering in ctx {:?}", serialize(mpath));
        self.unique.insert(mpath, ());

    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "pure finalizing by reducing {} at '{}'", self.unique.val_count(), serialize(wz.origin_path()));

        let mut _to_swap = PathMap::new(); std::mem::swap(&mut self.unique, &mut _to_swap);
        let mut rooted_input = PathMap::new();
        rooted_input.write_zipper_at_path(wz.root_prefix_path()).graft_map(_to_swap);

        static v: &'static [u8] = &[item_byte(Tag::NewVar)];
        let mut prz = OneFactor::new(rooted_input.into_read_zipper(&[]));
        let prz_ptr = (&prz) as *const OneFactor<_>;
        let mut changed = false;
        let mut buffer: Vec<u8> = Vec::with_capacity(1 << 32);
        crate::space::Space::query_multi_raw(unsafe { prz_ptr.cast_mut().as_mut().unwrap() }, &[ExprEnv::new(0, Expr{ ptr: v.as_ptr().cast_mut() })], |refs_bindings, loc| {

            for b in prz.child_mask().and(&ByteMask(crate::space::SIZES)).iter() {
                let Tag::SymbolSize(size) = byte_item(b) else { unreachable!() };
                prz.descend_to_byte(b);
                debug_assert!(prz.path_exists());
                if !prz.descend_first_k_path(size as _) { unreachable!() }
                loop {
                    let clen = prz.origin_path().len();

                    let mut rz = prz.fork_read_zipper();
                    'vals: while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "path number {:?}", serialize(&p[clen..]));
                        todo!();
                    }

                    if !prz.to_next_k_path(size as _) { break }
                }
                if !prz.ascend_byte() { unreachable!() }
            }

            for b in prz.child_mask().and(&ByteMask(crate::space::ARITIES)).iter() {
                todo!();
            }

            if prz.descend_to_existing_byte(item_byte(Tag::NewVar)) {
                let ignored = &prz.path()[..prz.path().len()-1];
                trace!(target: "sink", "ignored guard {}", serialize(ignored));
                wz.move_to_path(ignored);
                wz.set_val(());
                changed |= true;
                prz.ascend_byte();
            }
            if prz.descend_first_byte() {
                if let Tag::VarRef(k) = byte_item(prz.path()[prz.path().len()-1]) {
                    let clen = prz.path().len();
                    let mut rz = prz.fork_read_zipper();
                    'vals: while rz.to_next_val() {
                        let p = rz.origin_path();
                        trace!(target: "sink", "path {:?}", serialize(p));
                        trace!(target: "sink", "path {:?}", serialize(&p[clen..]));

                        let mut res = match self.scope.eval(ExprSource::new(&p[clen])) {
                            Ok(res) => { res }
                            Err(er) => { trace!(target: "pure", "err {}", er); continue 'vals }
                        };

                        trace!(target: "sink", "result {:?}", serialize(&res[..]));

                        let varref = &prz.path()[..prz.path().len()-1];
                        let ie = Expr { ptr: (&varref[0] as *const u8).cast_mut() };
                        let mut oz = ExprZipper::new(Expr{ ptr: buffer.as_mut_ptr() });
                        trace!(target: "sink", "ref guard '{}' var {:?} with '{}'", serialize(varref), k, serialize(&res[..]));
                        let os = ie.substitute_one_de_bruijn(k, Expr{ ptr: res.as_mut_ptr() }, &mut oz);
                        unsafe { buffer.set_len(oz.loc) }
                        trace!(target: "sink", "ref guard subs '{:?}'", serialize(&buffer[..oz.loc]));
                        wz.move_to_path(&buffer[wz.root_prefix_path().len()..oz.loc]);
                        wz.set_val(());
                        changed |= true;
                        self.scope.return_alloc(res);
                    }
                }
                prz.ascend_byte();
            }
            true
        });
        changed
    }
}

struct TensorCube {
    start: Vec<usize>,
    end: Vec<usize>,
    value: f32,
}

// (tensor-cubes <name> (, <start0> ... <startN>) (, <end0> ... <endN>) <value>)
pub struct TensorCubesSink { e: Expr, cubes: Vec<TensorCube>, ins: &'static str, changed: bool }
impl Sink for TensorCubesSink {
    fn new(e: Expr) -> Self {
        destruct!(e, ("tensor-cubes" {instance: &str} {start: Expr} {end: Expr} {value: Expr}), {
            trace!(target: "sink", "tensor-cubes requesting tensor {instance}");
            TensorCubesSink { e, cubes: vec![], ins: instance, changed: false }
        }, _err => { unreachable!() })
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::Tensor(self.ins))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::Tensor(_) = it.next().unwrap() else { unreachable!() };
        let concrete = Expr { ptr: path.as_ptr().cast_mut() };
        destruct!(concrete, ("tensor-cubes" {instance: &str} start end value), {
            assert_eq!(instance, self.ins, "tensor resource name changed after substitution");
            let start = tuple_usizes(start);
            let end = tuple_usizes(end);
            let value = symbol_f32(value);
            assert_eq!(start.len(), end.len(), "tensor-cubes start/end ranks differ");
            assert!(!start.is_empty(), "tensor-cubes rank must be at least 1");
            for (lo, hi) in start.iter().zip(end.iter()) {
                assert!(lo < hi, "tensor-cubes uses half-open ranges and requires start < end on every axis");
            }
            trace!(target: "sink", "tensor-cubes sinking {} {:?} {:?} {}", self.ins, start, end, value);
            self.cubes.push(TensorCube { start, end, value });
            self.changed = true;
        }, _err => { panic!("tensor-cubes concrete sink not the right shape {:?}", concrete) })
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::Tensor(tensor) = it.next().unwrap() else { unreachable!() };
        if !self.changed {
            return false;
        }
        let existing_dense = match tensor {
            Tensor::Dense(dense) if dense.shape.is_empty() && dense.data.len() == 1 && dense.data[0] == 0.0 => None,
            Tensor::Dense(dense) => Some(dense.clone()),
            Tensor::Csr(_) => panic!("tensor-cubes can only add to dense tensors"),
        };

        let rank = self.cubes.iter()
            .map(|cube| cube.start.len())
            .chain(existing_dense.as_ref().map(|dense| dense.shape.len()))
            .max()
            .unwrap();
        let mut shape = vec![0; rank];
        if let Some(existing) = existing_dense.as_ref() {
            let lead = rank - existing.shape.len();
            for (axis, dim) in existing.shape.iter().enumerate() {
                shape[lead + axis] = *dim;
            }
        }
        for cube in &self.cubes {
            let lead = rank - cube.start.len();
            for axis in 0..cube.start.len() {
                shape[lead + axis] = shape[lead + axis].max(cube.end[axis]);
            }
        }
        let mut dense = Dense::<f32>::zeros(shape);
        if let Some(existing) = existing_dense {
            copy_dense_tensor(&mut dense, &existing);
        }
        for cube in &self.cubes {
            add_tensor_cube(&mut dense, cube);
        }
        *tensor = Tensor::Dense(dense);
        true
    }
}


struct EinsumOp {
    input_names: Vec<String>,
    output_names: Vec<String>,
    input_specs: Vec<String>,
    output_specs: Vec<String>,
}

// (einsum (, <input tensor> ...) (, <output tensor> ...) (, <input spec> ...) (, <output spec> ...))
pub struct EinsumSink { e: Expr, ops: Vec<EinsumOp>, changed: bool }
impl Sink for EinsumSink {
    fn new(e: Expr) -> Self {
        destruct!(e, ("einsum" {inputs: Expr} {outputs: Expr} {input_specs: Expr} {output_specs: Expr}), {
            EinsumSink { e, ops: vec![], changed: false }
        }, _err => { unreachable!() })
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::TensorMap)
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::TensorMap(_) = it.next().unwrap() else { unreachable!() };
        let concrete = Expr { ptr: path.as_ptr().cast_mut() };
        destruct!(concrete, ("einsum" inputs outputs input_specs output_specs), {
            let input_names = tuple_strings(inputs);
            let mut output_names = tuple_strings(outputs);
            let input_specs = tuple_strings(input_specs);
            let mut output_specs = tuple_strings(output_specs);

            if output_names.is_empty() && output_specs.is_empty() {
                assert_eq!(input_names.len(), 1, "einsum scalar projection with omitted output name requires one input");
                output_names.push(input_names[0].clone());
                output_specs.push(String::new());
            } else if output_specs.is_empty() && output_names.len() == 1 {
                output_specs.push(String::new());
            }
            assert_eq!(input_names.len(), input_specs.len(), "einsum input name/spec count mismatch");
            assert_eq!(output_names.len(), output_specs.len(), "einsum output name/spec count mismatch");
            self.ops.push(EinsumOp { input_names, output_names, input_specs, output_specs });
        }, _err => { panic!("einsum concrete sink not the right shape {:?}", concrete) })
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::TensorMap(tensors) = it.next().unwrap() else { unreachable!() };
        for op in &self.ops {
            let input_keys: Vec<_> = op.input_names.iter().map(|name| OwnedSourceItem::from(name.as_str())).collect();
            let spec = format!("{}->{}", op.input_specs.join(","), op.output_specs.join(","));
            let output_denses = {
                let input_tensors: Vec<&Tensor> = input_keys.iter().zip(op.input_names.iter())
                    .map(|(key, name)| tensors.get(key).unwrap_or_else(|| panic!("non existent tensor {}", name)))
                    .collect();
                let input_shapes: Vec<Vec<usize>> = input_tensors.iter().map(|tensor| tensor_shape(tensor)).collect();
                let output_shapes = infer_einsum_output_shapes(&op.input_specs, &op.output_specs, &input_shapes);
                let jit_inputs: Vec<JitInput> = input_tensors.iter().map(|tensor| JitInput::from(*tensor)).collect();
                let mut output_denses: Vec<Dense<f32>> = output_shapes.into_iter().map(Dense::<f32>::zeros).collect();
                let mut output_refs: Vec<&mut Dense<f32>> = output_denses.iter_mut().collect();
                einsum_jit(&spec, &jit_inputs, &mut output_refs).unwrap_or_else(|err| panic!("einsum {spec} failed: {err}"));
                output_denses
            };

            for (name, dense) in op.output_names.iter().zip(output_denses.into_iter()) {
                let key = OwnedSourceItem::from(name.as_str());
                self.changed |= !tensor_matches_dense(tensors.get(&key), &dense);
                tensors.insert(key, Tensor::Dense(dense));
            }
        }
        self.changed
    }
}


// (z3 <instance> <declaration or assertion>)
#[cfg(feature = "z3")]
pub struct Z3Sink { e: Expr, buffer: Vec<u8>, ins: &'static str }
#[cfg(feature = "z3")]
impl Sink for Z3Sink {
    fn new(e: Expr) -> Self {
        destruct!(e, ("z3" {instance: &str} {decl: Expr}), {
            trace!(target: "sink", "z3 requesting instance {instance}");
            Z3Sink { e, buffer: vec![], ins: instance }
        }, _err => { unreachable!() })
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        return std::iter::once(WriteResourceRequest::Z3(self.ins));
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let spath = &path[1+1+2+1+self.ins.bytes().len()..];
        trace!(target: "sink", "z3 sinking '{}'", serialize(spath));
        let e = Expr { ptr: spath.as_ptr().cast_mut() };
        e.serialize(&mut self.buffer, |e| std::str::from_utf8(e).unwrap());
        self.buffer.push(b'\n');
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "z3 writing buffer {:?}", std::str::from_utf8(&self.buffer[..]).unwrap());
        let WriteResource::Z3(ref mut p) = it.next().unwrap() else { unreachable!() };
        let mut stdin = p.stdin.as_mut().unwrap();
        stdin.write(&self.buffer[..]).unwrap();
        stdin.flush().unwrap();
        true
    }
}


pub enum ASink { AddSink(AddSink), RemoveSink(RemoveSink), HeadSink(HeadTailSink<true>), TailSink(HeadTailSink<false>), CountSink(CountSink), HashSink(HashSink), SumSink(SumSink), AndSink(AndSink), ACTSink(ACTSink),
    #[cfg(feature = "wasm")]
    WASMSink(WASMSink),
    #[cfg(feature = "grounding")]
    PureSink(PureSink),
    #[cfg(feature = "z3")]
    Z3Sink(Z3Sink),
    TensorCubesSink(TensorCubesSink),
    EinsumSink(EinsumSink),
    AUSink(AUSink),
    USink(USink),
    CompatSink(CompatSink),
    FSumSink(FloatReductionSink<Sum>),
    FMinSink(FloatReductionSink<Min>),
    FMaxSink(FloatReductionSink<Max>),
    FProdSink(FloatReductionSink<Prod>),
}

impl ASink {
    pub fn compat(e: Expr) -> Self {
        ASink::CompatSink(CompatSink::new(e))
    }
}

impl Sink for ASink {
    fn new(e: Expr) -> Self {
        if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1)) && *e.ptr.offset(2) == b'-' } {
            ASink::RemoveSink(RemoveSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1)) && *e.ptr.offset(2) == b'+' } {
            ASink::AddSink(AddSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1)) && *e.ptr.offset(2) == b'U' } {
            ASink::USink(USink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(2)) && *e.ptr.offset(2) == b'A' && *e.ptr.offset(3) == b'U' } {
            ASink::AUSink(AUSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'h' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'a' && *e.ptr.offset(5) == b'd' } {
            ASink::HeadSink(HeadTailSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'a' && *e.ptr.offset(4) == b'i' && *e.ptr.offset(5) == b'l' } {
            ASink::TailSink(HeadTailSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(5)) &&
            *e.ptr.offset(2) == b'c' && *e.ptr.offset(3) == b'o' && *e.ptr.offset(4) == b'u' && *e.ptr.offset(5) == b'n' && *e.ptr.offset(6) == b't' } {
            ASink::CountSink(CountSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'h' && *e.ptr.offset(3) == b'a' && *e.ptr.offset(4) == b's' && *e.ptr.offset(5) == b'h' } {
            ASink::HashSink(HashSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3)) &&
            *e.ptr.offset(2) == b's' && *e.ptr.offset(3) == b'u' && *e.ptr.offset(4) == b'm' } {
            return ASink::SumSink(SumSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'f' && *e.ptr.offset(3) == b's'&& *e.ptr.offset(4) == b'u'&& *e.ptr.offset(5) == b'm' } {
            return ASink::FSumSink(FloatReductionSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'f' && *e.ptr.offset(3) == b'm' && *e.ptr.offset(4) == b'i' && *e.ptr.offset(5) == b'n' } {
            return ASink::FMinSink(FloatReductionSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'f' && *e.ptr.offset(3) == b'm' && *e.ptr.offset(4) == b'a' && *e.ptr.offset(5) == b'x' } {
            return ASink::FMaxSink(FloatReductionSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(5)) &&
            *e.ptr.offset(2) == b'f' && *e.ptr.offset(3) == b'p' && *e.ptr.offset(4) == b'r' && *e.ptr.offset(5) == b'o' && *e.ptr.offset(6) == b'd' } {
            return ASink::FProdSink(FloatReductionSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3)) &&
            *e.ptr.offset(2) == b'a' && *e.ptr.offset(3) == b'n' && *e.ptr.offset(4) == b'd' } {
            return ASink::AndSink(AndSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3)) &&
            *e.ptr.offset(2) == b'A' && *e.ptr.offset(3) == b'C' && *e.ptr.offset(4) == b'T' } {
            return ASink::ACTSink(ACTSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'w' && *e.ptr.offset(3) == b'a' && *e.ptr.offset(4) == b's' && *e.ptr.offset(5) == b'm' } {
            #[cfg(feature = "wasm")]
            return ASink::WASMSink(WASMSink::new(e));
            #[cfg(not(feature = "wasm"))]
            panic!("MORK was not built with the wasm feature, yet trying to call {:?}", e);
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'p' && *e.ptr.offset(3) == b'u' && *e.ptr.offset(4) == b'r' && *e.ptr.offset(5) == b'e' } {
            #[cfg(feature = "grounding")]
            return ASink::PureSink(PureSink::new(e));
            #[cfg(not(feature = "grounding"))]
            panic!("MORK was not built with the grounding feature, yet trying to call {:?}", e);
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(2)) &&
            *e.ptr.offset(2) == b'z' && *e.ptr.offset(3) == b'3'} {
            #[cfg(feature = "z3")]
            return ASink::Z3Sink(Z3Sink::new(e));
            #[cfg(not(feature = "z3"))]
            panic!("MORK was not built with the z3 feature, yet trying to call {:?}", e);
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(5)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(12)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'n' && *e.ptr.offset(5) == b's' &&
            *e.ptr.offset(6) == b'o' && *e.ptr.offset(7) == b'r' && *e.ptr.offset(8) == b'-' && *e.ptr.offset(9) == b'c' &&
            *e.ptr.offset(10) == b'u' && *e.ptr.offset(11) == b'b' && *e.ptr.offset(12) == b'e' && *e.ptr.offset(13) == b's' } {
            return ASink::TensorCubesSink(TensorCubesSink::new(e));
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(5)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(6)) &&
            *e.ptr.offset(2) == b'e' && *e.ptr.offset(3) == b'i' && *e.ptr.offset(4) == b'n' && *e.ptr.offset(5) == b's' &&
            *e.ptr.offset(6) == b'u' && *e.ptr.offset(7) == b'm' } {
            return ASink::EinsumSink(EinsumSink::new(e));
        } else {
            panic!("unrecognized sink")
        }
    }

    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        gen move {
            match self {
                ASink::AddSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::USink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::AUSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::RemoveSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::HeadSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::TailSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::CountSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::HashSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::SumSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::AndSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::ACTSink(s) => { for i in s.request().into_iter() { yield i } }
                #[cfg(feature = "wasm")]
                ASink::WASMSink(s) => { for i in s.request().into_iter() { yield i } }
                #[cfg(feature = "grounding")]
                ASink::PureSink(s) => { for i in s.request().into_iter() { yield i } }
                #[cfg(feature = "z3")]
                ASink::Z3Sink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::TensorCubesSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::EinsumSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::CompatSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FSumSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FMinSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FMaxSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FProdSink(s) => { for i in s.request().into_iter() { yield i } }
            }
        }
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        match self {
            ASink::AddSink(s) => { s.sink(it, path) }
            ASink::USink(s) => { s.sink(it, path) }
            ASink::AUSink(s) => { s.sink(it, path) }
            ASink::RemoveSink(s) => { s.sink(it, path) }
            ASink::HeadSink(s) => { s.sink(it, path) }
            ASink::TailSink(s) => { s.sink(it, path) }
            ASink::CountSink(s) => { s.sink(it, path) }
            ASink::HashSink(s) => { s.sink(it, path) }
            ASink::SumSink(s) => { s.sink(it, path) }
            ASink::AndSink(s) => { s.sink(it, path) }
            ASink::ACTSink(s) => { s.sink(it, path) }
            #[cfg(feature = "wasm")]
            ASink::WASMSink(s) => { s.sink(it, path) }
            #[cfg(feature = "grounding")]
            ASink::PureSink(s) => { s.sink(it, path) }
            #[cfg(feature = "z3")]
            ASink::Z3Sink(s) => { s.sink(it, path) }
            ASink::TensorCubesSink(s) => { s.sink(it, path) }
            ASink::EinsumSink(s) => { s.sink(it, path) }
            ASink::CompatSink(s) => { s.sink(it, path) }
            ASink::FSumSink(s) => { s.sink(it, path) }
            ASink::FMinSink(s) => { s.sink(it, path) }
            ASink::FMaxSink(s) => { s.sink(it, path) }
            ASink::FProdSink(s) => { s.sink(it, path) }
        }
    }

    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It) -> bool where 'a : 'w, 'k : 'w {
        match self {
            ASink::AddSink(s) => { s.finalize(it) }
            ASink::USink(s) => { s.finalize(it) }
            ASink::AUSink(s) => { s.finalize(it) }
            ASink::RemoveSink(s) => { s.finalize(it) }
            ASink::HeadSink(s) => { s.finalize(it) }
            ASink::TailSink(s) => { s.finalize(it) }
            ASink::CountSink(s) => { s.finalize(it) }
            ASink::HashSink(s) => { s.finalize(it) }
            ASink::SumSink(s) => { s.finalize(it) }
            ASink::AndSink(s) => { s.finalize(it) }
            ASink::ACTSink(s) => { s.finalize(it) }
            #[cfg(feature = "wasm")]
            ASink::WASMSink(s) => { s.finalize(it) }
            #[cfg(feature = "grounding")]
            ASink::PureSink(s) => { s.finalize(it) }
            #[cfg(feature = "z3")]
            ASink::Z3Sink(s) => { s.finalize(it) }
            ASink::TensorCubesSink(s) => { s.finalize(it) }
            ASink::EinsumSink(s) => { s.finalize(it) }
            ASink::CompatSink(s) => { s.finalize(it) }
            ASink::FSumSink(s) => { s.finalize(it) }
            ASink::FMinSink(s) => { s.finalize(it) }
            ASink::FMaxSink(s) => { s.finalize(it) }
            ASink::FProdSink(s) => { s.finalize(it) }
        }
    }
}
