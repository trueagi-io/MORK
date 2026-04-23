use core::f64;
use std::io::{BufRead, Read, Write};
use std::marker::PhantomData;
use std::{mem, process, ptr};
use std::any::Any;
use std::cmp::Ordering;
use std::collections::BTreeMap;
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
use mork_expr::{byte_item, Expr, ExprZipper, ExtractFailure, item_byte, parse, serialize, Tag, traverseh, ExprEnv, unify, UnificationFailure, apply, destruct};
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
use mork_expr::macros::SerializableExpr;
use crate::{expr, pure};
use crate::space::ACT_PATH;

#[derive(Eq, PartialEq, Debug)]
pub(crate) enum WriteResourceRequest {
    BTM(&'static [u8]),
    ACT(&'static str),
    Z3(&'static str),
    TensorStore,
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
            WriteResourceRequest::TensorStore => {
                match other {
                    WriteResourceRequest::TensorStore => { Some(WriteResourceRequest::TensorStore) }
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
            WriteResourceRequest::TensorStore => {
                if let WriteResourceRequest::TensorStore = other {
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
    TensorStore(&'w mut std::collections::HashMap<Vec<u8>, crate::sparse::SparseTensorF64>),
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

pub trait Sink {
    fn new(e: Expr) -> Self;
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest>;
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It, path: &[u8]) where 'a : 'w, 'k : 'w;
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It) -> bool where 'a : 'w, 'k : 'w;
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
pub struct USink { e: Expr, buf: Option<*mut u8>, tmp: Option<*mut u8>, last: usize, conflict: bool }
impl Sink for USink {
    fn new(e: Expr) -> Self {
        USink { e, buf: None, tmp: None, last: usize::MAX, conflict: false }
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
            let mut wz = ExprZipper::new(Expr{ ptr: tmp });
            let Ok(_) = eau.unify(Expr{ ptr: path[3..].as_ptr().cast_mut() }, &mut wz) else {
                self.conflict = true;
                return;
            };
            std::mem::swap(&mut self.buf, &mut self.tmp);
            self.last = wz.loc;
        } else {
            self.buf = Some(unsafe { std::alloc::alloc(std::alloc::Layout::array::<u8>(1 << 32).unwrap()) });
            self.tmp = Some(unsafe { std::alloc::alloc(std::alloc::Layout::array::<u8>(1 << 32).unwrap()) });
            unsafe { std::ptr::copy_nonoverlapping(path[3..].as_ptr(), self.buf.unwrap(), path[3..].len()) }
            self.last = path[3..].len();
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
                let buf = unsafe { slice_from_raw_parts(buf as *const u8, self.last).as_ref().unwrap() };
                trace!(target: "sink", "U unified expression '{}'", serialize(buf));
                let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
                wz.move_to_path(&buf[wz.root_prefix_path().len()..]);
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

pub struct HeadSink { e: Expr, head: PathMap<()>, skip: usize, count: usize, max: usize, top: Vec<u8> }
impl Sink for HeadSink {
    fn new(e: Expr) -> Self {
        let mut ez = ExprZipper::new(e); ez.next(); ez.next();
        let max_s = ez.item().err().expect("cnt can not be an expression or variable");
        let max: usize = str::from_utf8(max_s).expect("string encoded numbers for now").parse().expect("a number");
        assert_ne!(max, 0);
        HeadSink { e, head: PathMap::new(), skip: 1 + 1+4 + 1+max_s.len(), count: 0, max, top: vec![] }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let p = &unsafe { self.e.prefix().unwrap_or_else(|x| { let s = self.e.span(); slice_from_raw_parts(self.e.ptr, s.len() - 1) }).as_ref().unwrap() }[self.skip..];
        trace!(target: "sink", "head requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        let mpath = &path[self.skip+wz.root_prefix_path().len()..];
        trace!(target: "sink", "head at '{}' sinking raw '{}'", serialize(wz.root_prefix_path()), serialize(path));
        if self.count == self.max {
            if &self.top[..] <= mpath {
                trace!(target: "sink", "head at max capacity ignoring '{}'", serialize(mpath));
                // doesn't displace any path
            } else {
                trace!(target: "sink", "head at max capacity replacing '{}' with '{}'", serialize(&self.top[..]), serialize(mpath));
                assert!(self.head.insert(mpath, ()).is_none());
                self.head.remove(&self.top[..]);
                let mut rz = self.head.read_zipper();
                rz.descend_last_path();
                self.top.clear();
                self.top.extend_from_slice(rz.path()); // yikes, throwing away our needless allocation
            }
        } else {
            if &self.top[..] <= mpath {
                if self.head.insert(mpath, ()).is_none() {
                    trace!(target: "sink", "head adding new top at '{}'", serialize(mpath));
                    self.top.clear();
                    self.top.extend_from_slice(mpath);
                    self.count += 1;
                }
            } else {
                if self.head.insert(mpath, ()).is_none() {
                    trace!(target: "sink", "head adding '{}'", serialize(mpath));
                    self.count += 1;
                }
            }
        }
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        let WriteResource::BTM(wz) = it.next().unwrap() else { unreachable!() };
        wz.reset();
        trace!(target: "sink", "head finalizing by joining {} at '{}'", self.count, serialize(wz.origin_path()));

        match wz.join_into(&self.head.read_zipper()) {
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
        crate::sparse::register(&mut scope);
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


// ============================================================================
// Tensor sinks — all tensor I/O goes through WriteResource::TensorStore
// ============================================================================

/// Helper: parse symbol args from an expression path, skipping a known header.
fn parse_symbol_args<'a>(path: &'a [u8], header_size: usize) -> Vec<&'a [u8]> {
    let rest = &path[header_size..];
    let mut pos = 0;
    let mut args = Vec::new();
    while pos < rest.len() {
        match byte_item(rest[pos]) {
            Tag::SymbolSize(len) => {
                let len = len as usize;
                pos += 1;
                if pos + len <= rest.len() {
                    args.push(&rest[pos..pos+len]);
                }
                pos += len;
            }
            _ => { pos += 1; }
        }
    }
    args
}

/// TensorCollectSink — writes (indices, value) tuples directly into a named SparseTensorF64.
/// Syntax: (tensor_collect name $i0 $i1 ... $val)
///
/// The first matching tuple replaces any existing tensor at `name` with a
/// fresh one; subsequent matches in the same exec invocation accumulate
/// into it. This assumes no concurrent tensor-as-source path is reading
/// `name` during the exec — if that ever becomes possible the writes must
/// be buffered until `finalize()` (see TensorFreeSink for that pattern).
pub struct TensorCollectSink {
    e: Expr,
    name: Vec<u8>,
    rank: usize,
    initialized: bool,
}

impl TensorCollectSink {
    const HEADER_SIZE: usize = 16; // Arity(N) + SymbolSize(14) + "tensor_collect"
}

impl Sink for TensorCollectSink {
    fn new(e: Expr) -> Self {
        let arity = unsafe {
            if let Tag::Arity(a) = byte_item(*e.ptr) { a as usize } else { panic!("tensor_collect: expected arity") }
        };
        let rank = arity.saturating_sub(3);
        let name = unsafe {
            let name_tag = *e.ptr.add(Self::HEADER_SIZE);
            if let Tag::SymbolSize(len) = byte_item(name_tag) {
                std::slice::from_raw_parts(e.ptr.add(Self::HEADER_SIZE + 1), len as usize).to_vec()
            } else {
                panic!("tensor_collect: second arg must be a symbol (tensor name)")
            }
        };
        TensorCollectSink { e, name, rank, initialized: false }
    }

    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::TensorStore)
    }

    fn sink<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a: 'w, 'k: 'w {
        let name_len = self.name.len();
        let args = parse_symbol_args(path, Self::HEADER_SIZE + 1 + name_len);

        if args.len() < self.rank + 1 { return; }

        let mut indices = Vec::with_capacity(self.rank);
        for i in 0..self.rank {
            let Ok(s) = std::str::from_utf8(args[i]) else { return; };
            let Ok(idx) = s.parse::<usize>() else { return; };
            indices.push(idx);
        }
        let Ok(s) = std::str::from_utf8(args[self.rank]) else { return; };
        let Ok(val) = s.parse::<f64>() else { return; };

        let WriteResource::TensorStore(store) = it.next().unwrap() else { unreachable!() };
        if !self.initialized {
            store.insert(self.name.clone(), crate::sparse::SparseTensorF64::new(self.rank));
            self.initialized = true;
        }
        store.get_mut(&self.name).unwrap().set(&indices, val);
    }

    fn finalize<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, _it: It) -> bool where 'a: 'w, 'k: 'w {
        self.initialized
    }
}

/// TensorEinsumSink — runs einsum on named tensors.
/// Syntax: (tensor_einsum "spec" input1 input2 ... output)
/// Variables are bound from pattern matching; actual values arrive in sink().
pub struct TensorEinsumSink {
    e: Expr,
    spec: Vec<u8>,
    input_names: Vec<Vec<u8>>,
    output_name: Vec<u8>,
    parsed: bool,
}

impl TensorEinsumSink {
    // "tensor_einsum" is 13 chars → header = Arity + SymbolSize(13) + "tensor_einsum" = 15
    const HEADER_SIZE: usize = 15;
}

impl Sink for TensorEinsumSink {
    fn new(e: Expr) -> Self {
        let span = unsafe { e.span().as_ref().unwrap() };
        let args = parse_symbol_args(span, Self::HEADER_SIZE);
        let spec = args.first().map(|a| a.to_vec()).unwrap_or_default();
        let mut names: Vec<Vec<u8>> = args.get(1..).unwrap_or(&[]).iter().map(|a| a.to_vec()).collect();
        let output_name = names.pop().unwrap_or_default();
        TensorEinsumSink { e, spec, input_names: names, output_name, parsed: !args.is_empty() }
    }
    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::TensorStore)
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, _it: It, _path: &[u8]) where 'a: 'w, 'k: 'w {}
    fn finalize<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a: 'w, 'k: 'w {
        if !self.parsed { return false; }
        let WriteResource::TensorStore(store) = it.next().unwrap() else { unreachable!() };
        // Strip quotes from spec if present (MORK parser includes them)
        let spec_bytes = if self.spec.starts_with(b"\"") && self.spec.ends_with(b"\"") {
            &self.spec[1..self.spec.len()-1]
        } else {
            &self.spec[..]
        };
        let spec_str = match std::str::from_utf8(spec_bytes) {
            Ok(s) => s,
            Err(_) => { log::error!(target: "tensor", "tensor_einsum: invalid spec"); return false; }
        };

        let inputs: Vec<&crate::sparse::SparseTensorF64> = self.input_names.iter()
            .filter_map(|name| store.get(name))
            .collect();
        if inputs.len() != self.input_names.len() {
            log::error!(target: "tensor", "tensor_einsum: missing input tensor(s)");
            return false;
        }

        // Parse spec to determine output shape
        let arrow = match spec_str.find("->") {
            Some(a) => a,
            None => { log::error!(target: "tensor", "tensor_einsum: spec missing '->'"); return false; }
        };
        let output_spec = &spec_str[arrow+2..];
        let input_specs: Vec<&str> = spec_str[..arrow].split(',').collect();

        let mut dim_map = std::collections::HashMap::new();
        for (i, ispec) in input_specs.iter().enumerate() {
            if let Some(inp) = inputs.get(i) {
                for (axis, ch) in ispec.bytes().enumerate() {
                    let d = inp.dims.get(axis).copied().unwrap_or(0);
                    dim_map.entry(ch).or_insert(d);
                }
            }
        }
        let out_dims: Vec<usize> = output_spec.bytes()
            .map(|ch| dim_map.get(&ch).copied().unwrap_or(1))
            .collect();

        let mut output = crate::sparse::SparseTensorF64::with_dims(out_dims);
        let dyn_inputs: Vec<&dyn einsum_dyn::NDIndex<f64>> = inputs.iter()
            .map(|t| *t as &dyn einsum_dyn::NDIndex<f64>)
            .collect();
        let mut dyn_out: &mut dyn einsum_dyn::NDIndex<f64> = &mut output;
        if let Err(e) = einsum_dyn::sparse::einsum_vm_oneshot_dyn(spec_str, &dyn_inputs, &mut [dyn_out]) {
            log::error!(target: "tensor", "tensor_einsum failed: {}", e);
            return false;
        }
        store.insert(self.output_name.clone(), output);
        true
    }
}

/// TensorBinopSink — element-wise add or mul on named tensors.
/// Syntax: (tensor_add A B C) or (tensor_mul A B C)
pub struct TensorBinopSink {
    e: Expr,
    op: TensorBinop,
    header_size: usize,
    a_name: Vec<u8>,
    b_name: Vec<u8>,
    c_name: Vec<u8>,
    parsed: bool,
}

enum TensorBinop { Add, Mul }

impl TensorBinopSink {
    fn new_with_op(e: Expr, op: TensorBinop, header_size: usize) -> Self {
        TensorBinopSink { e, op, header_size, a_name: Vec::new(), b_name: Vec::new(), c_name: Vec::new(), parsed: false }
    }
}

impl Sink for TensorBinopSink {
    fn new(e: Expr) -> Self { panic!("use new_with_op") }
    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::TensorStore)
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, _it: It, path: &[u8]) where 'a: 'w, 'k: 'w {
        if self.parsed { return; }
        let args = parse_symbol_args(path, self.header_size);
        self.a_name = args.first().map(|a| a.to_vec()).unwrap_or_default();
        self.b_name = args.get(1).map(|a| a.to_vec()).unwrap_or_default();
        self.c_name = args.get(2).map(|a| a.to_vec()).unwrap_or_default();
        self.parsed = true;
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a: 'w, 'k: 'w {
        if !self.parsed { return false; }
        let WriteResource::TensorStore(store) = it.next().unwrap() else { unreachable!() };
        let (a, b) = match (store.get(&self.a_name), store.get(&self.b_name)) {
            (Some(a), Some(b)) => (a, b),
            _ => { log::error!(target: "tensor", "tensor binop: missing input"); return false; }
        };
        let c = match self.op {
            TensorBinop::Add => a.add(b),
            TensorBinop::Mul => a.mul(b),
        };
        store.insert(self.c_name.clone(), c);
        true
    }
}

/// TensorFreeSink — removes named tensors.
/// Syntax: (tensor_free A)
///
/// Names are buffered during `sink()` and the actual removals happen in
/// `finalize()`. We cannot free in `sink()` because a future source type
/// (tensor-as-source) could be iterating the tensor store while pattern
/// matches drive these calls — mutating the store mid-iteration would
/// invalidate the upstream zipper.
pub struct TensorFreeSink {
    e: Expr,
    names: Vec<Vec<u8>>,
}

impl Sink for TensorFreeSink {
    fn new(e: Expr) -> Self {
        TensorFreeSink { e, names: Vec::new() }
    }
    fn request(&self) -> impl Iterator<Item=WriteResourceRequest> {
        std::iter::once(WriteResourceRequest::TensorStore)
    }
    fn sink<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, _it: It, path: &[u8]) where 'a: 'w, 'k: 'w {
        // "tensor_free" is 11 chars → header = 13
        let args = parse_symbol_args(path, 13);
        if let Some(name) = args.first() {
            self.names.push(name.to_vec());
        }
    }
    fn finalize<'w, 'a, 'k, It: Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a: 'w, 'k: 'w {
        let WriteResource::TensorStore(store) = it.next().unwrap() else { unreachable!() };
        let mut any = false;
        for name in self.names.drain(..) {
            if store.remove(&name).is_some() {
                any = true;
            }
        }
        any
    }
}

pub enum ASink { AddSink(AddSink), RemoveSink(RemoveSink), HeadSink(HeadSink), CountSink(CountSink), HashSink(HashSink), SumSink(SumSink), AndSink(AndSink), ACTSink(ACTSink),
    TensorCollectSink(TensorCollectSink),
    TensorEinsumSink(TensorEinsumSink),
    TensorBinopSink(TensorBinopSink),
    TensorFreeSink(TensorFreeSink),
    #[cfg(feature = "wasm")]
    WASMSink(WASMSink),
    #[cfg(feature = "grounding")]
    PureSink(PureSink),
    #[cfg(feature = "z3")]
    Z3Sink(Z3Sink),
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
    /// Set an opaque context pointer on any PureSink's EvalScope.
    /// This allows pure functions to access external state (e.g. tensor store).
    pub fn set_context(&mut self, ctx: *mut ()) {
        #[cfg(feature = "grounding")]
        if let ASink::PureSink(s) = self {
            s.scope.context = ctx;
        }
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
            ASink::HeadSink(HeadSink::new(e))
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
        } else if unsafe { *e.ptr.offset(1) == item_byte(Tag::SymbolSize(14)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'n' && *e.ptr.offset(5) == b's' &&
            *e.ptr.offset(6) == b'o' && *e.ptr.offset(7) == b'r' && *e.ptr.offset(8) == b'_' && *e.ptr.offset(9) == b'c' &&
            *e.ptr.offset(10) == b'o' && *e.ptr.offset(11) == b'l' && *e.ptr.offset(12) == b'l' && *e.ptr.offset(13) == b'e' &&
            *e.ptr.offset(14) == b'c' && *e.ptr.offset(15) == b't' } {
            return ASink::TensorCollectSink(TensorCollectSink::new(e));
        } else if unsafe { *e.ptr.offset(1) == item_byte(Tag::SymbolSize(13)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'n' && *e.ptr.offset(5) == b's' &&
            *e.ptr.offset(6) == b'o' && *e.ptr.offset(7) == b'r' && *e.ptr.offset(8) == b'_' && *e.ptr.offset(9) == b'e' &&
            *e.ptr.offset(10) == b'i' && *e.ptr.offset(11) == b'n' && *e.ptr.offset(12) == b's' && *e.ptr.offset(13) == b'u' &&
            *e.ptr.offset(14) == b'm' } {
            return ASink::TensorEinsumSink(TensorEinsumSink::new(e));
        } else if unsafe { *e.ptr.offset(1) == item_byte(Tag::SymbolSize(10)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'n' && *e.ptr.offset(5) == b's' &&
            *e.ptr.offset(6) == b'o' && *e.ptr.offset(7) == b'r' && *e.ptr.offset(8) == b'_' && *e.ptr.offset(9) == b'a' &&
            *e.ptr.offset(10) == b'd' && *e.ptr.offset(11) == b'd' } {
            // "tensor_add" = 10 chars, header = 12
            return ASink::TensorBinopSink(TensorBinopSink::new_with_op(e, TensorBinop::Add, 12));
        } else if unsafe { *e.ptr.offset(1) == item_byte(Tag::SymbolSize(10)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'n' && *e.ptr.offset(5) == b's' &&
            *e.ptr.offset(6) == b'o' && *e.ptr.offset(7) == b'r' && *e.ptr.offset(8) == b'_' && *e.ptr.offset(9) == b'm' &&
            *e.ptr.offset(10) == b'u' && *e.ptr.offset(11) == b'l' } {
            // "tensor_mul" = 10 chars, header = 12
            return ASink::TensorBinopSink(TensorBinopSink::new_with_op(e, TensorBinop::Mul, 12));
        } else if unsafe { *e.ptr.offset(1) == item_byte(Tag::SymbolSize(11)) &&
            *e.ptr.offset(2) == b't' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'n' && *e.ptr.offset(5) == b's' &&
            *e.ptr.offset(6) == b'o' && *e.ptr.offset(7) == b'r' && *e.ptr.offset(8) == b'_' && *e.ptr.offset(9) == b'f' &&
            *e.ptr.offset(10) == b'r' && *e.ptr.offset(11) == b'e' && *e.ptr.offset(12) == b'e' } {
            return ASink::TensorFreeSink(TensorFreeSink::new(e));
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
                ASink::CompatSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FSumSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FMinSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FMaxSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::FProdSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::TensorCollectSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::TensorEinsumSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::TensorBinopSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::TensorFreeSink(s) => { for i in s.request().into_iter() { yield i } }
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
            ASink::CompatSink(s) => { s.sink(it, path) }
            ASink::FSumSink(s) => { s.sink(it, path) }
            ASink::FMinSink(s) => { s.sink(it, path) }
            ASink::FMaxSink(s) => { s.sink(it, path) }
            ASink::FProdSink(s) => { s.sink(it, path) }
            ASink::TensorCollectSink(s) => { s.sink(it, path) }
            ASink::TensorEinsumSink(s) => { s.sink(it, path) }
            ASink::TensorBinopSink(s) => { s.sink(it, path) }
            ASink::TensorFreeSink(s) => { s.sink(it, path) }
        }
    }

    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It) -> bool where 'a : 'w, 'k : 'w {
        match self {
            ASink::AddSink(s) => { s.finalize(it) }
            ASink::USink(s) => { s.finalize(it) }
            ASink::AUSink(s) => { s.finalize(it) }
            ASink::RemoveSink(s) => { s.finalize(it) }
            ASink::HeadSink(s) => { s.finalize(it) }
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
            ASink::CompatSink(s) => { s.finalize(it) }
            ASink::FSumSink(s) => { s.finalize(it) }
            ASink::FMinSink(s) => { s.finalize(it) }
            ASink::FMaxSink(s) => { s.finalize(it) }
            ASink::FProdSink(s) => { s.finalize(it) }
            ASink::TensorCollectSink(s) => { s.finalize(it) }
            ASink::TensorEinsumSink(s) => { s.finalize(it) }
            ASink::TensorBinopSink(s) => { s.finalize(it) }
            ASink::TensorFreeSink(s) => { s.finalize(it) }
        }
    }
}
