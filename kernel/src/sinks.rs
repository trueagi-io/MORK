use std::io::{BufRead, Read, Write};
use std::{mem, process, ptr};
use std::any::Any;
use std::collections::BTreeMap;
use std::fmt::Display;
use std::fs::File;
use std::hint::unreachable_unchecked;
use std::mem::MaybeUninit;
use std::ops::{Coroutine, CoroutineState};
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

pub(crate) enum WriteResourceRequest {
    BTM(&'static [u8]),
    ACT(&'static str),
    Z3(&'static str),
}

pub(crate) enum WriteResource<'w, 'a, 'k> {
    BTM(&'w mut WriteZipperTracked<'a, 'k, ()>),
    ACT(()),
    Z3(subprocess::Popen)
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
        trace!(target: "sink", "ACT sinking '{}'", serialize(path));
        self.tmp.insert(path, ());
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

/// Reduce has multi-set semantics, only accepts with ground results (values output from the `Out` operation).
///
/// `In`  applys on all input values.  
/// 
/// `Op`  applys on all all pairs of b.
/// 
/// `Out` applys _only_ after the reductions with Op finishes.
/// 
/// 
/// ```ignore
/// ; syntax
/// (Reduce 
/// $OutTemplate $out $in 
///       ; the operations must be just the single names from pure/eval
///  with (In  $eval_unary_op_in)  ; In  : a     -> b
///       (Op  $eval_binary_op)    ; Op  : b * b -> b
///       (Out $eval_unary_op_out) ; Out : b     -> c
/// )
/// ```
/// an example of a valid reduce triple is `(In f64_from_string) (Op sum_f64) (Out f64_to_string)`
struct Reduce {
    scope     : eval::EvalScope,

    e            : Expr,
    skip         : bool,

    /// Having the nested Pathmaps makes it easier to separate the concern of what values were bound by a source.
    /// the outer pathmap is the index that dictates what reduce will be applied
    /// the middle one on what template,
    /// the one before last is the out value,
    /// the innermost pathmap is the values that will be reduced for that index.
    /// The order here matters! it preserves the variables in the exprs.
    /// the usize is required to encode multiset behavior 
    
    // (Remy) this code is sub optimal, but I want get a version that works done first.
    // a plain Pathmap<usize> would be enough normally.
    // I would need to check branching points as I acend and decent and compare them to locations I found along the way with a stack.
    // It's very doable, but heavy in numerics.
    accumulator : PathMap<PathMap<PathMap<PathMap<usize>>>>,
}

impl Sink for Reduce {
    fn new(e: Expr) -> Self {
        let mut skip = false;
        if e.arity() != Some(8) { skip = false };

        destruct!(
            e,
            ("reduce" _template _out _in 
             "with" ("In"  _In)
                    ("Op"  _Op)
                    ("Out" _Out)
            ),
            {   Reduce {
                    e,
                    skip        : false,
                    scope       : eval::EvalScope::new(),
                    accumulator : PathMap::new(),
                }
            },
            err => return Reduce { 
                e,
                skip        : true,
                scope       : eval::EvalScope::new(),
                accumulator : PathMap::new(),
            }
        )
    }

    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        let out_template = Expr{ptr : unsafe { 
            self.e.ptr.add(Expr{ptr:self.e.ptr.add(1/* arity tag */)}.span().len() + 1 /* arity tag again */) 
        }}; // I cannot fail to get this arity 8 guarantees this.

        let p = unsafe { self.out_template.prefix().unwrap_or_else(|x| { out_template.span() }).as_ref().unwrap() };
        trace!(target: "sink", "reduce requesting {}", serialize(p));
        std::iter::once(WriteResourceRequest::BTM(p))
    }

    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        if self.skip {return;}
        
        let path_as_ptr = path as *const[u8] as *const u8 as *mut u8;
        // The tempory pathmap is organized by operation, then arguments.
        destruct!(
            Expr{ ptr : path_as_ptr },
            ("reduce" template out in_ 
             _with ("In"  _In)
                   ("Op"  _Op)
                   ("Out" _Out)
            ),
            {
                // We only support single eval operators
                if [_In,_Op,_Out].map(|e| unsafe { mork_expr::byte_item(*e.ptr) }).into_iter().any(|b|!matches!(b, mork_expr::Tag::SymbolSize(_)))
                {   self.skip = true;
                    return;
                }

                let mut wz = self.accumulator.write_zipper();
                
                // add arity byte
                wz.descend_to_byte(mork_expr::item_byte(mork_expr::Tag::Arity(4)));

                // index by operations
                wz.descend_to(unsafe { &path[_with.ptr.byte_offset_from_unsigned(path_as_ptr)..]});

                let mut wz_template =          wz.get_val_or_set_mut(PathMap::new()).write_zipper_at_path(unsafe { core::ptr::slice_from_raw_parts(template.ptr,  out.ptr.byte_offset_from_unsigned(template.ptr)).as_ref().unwrap() });
                let mut wz_out      = wz_template.get_val_or_set_mut(PathMap::new()).write_zipper_at_path(unsafe { core::ptr::slice_from_raw_parts(     out.ptr,   in_.ptr.byte_offset_from_unsigned(     out.ptr)).as_ref().unwrap() });
                let mut wz_in       =      wz_out.get_val_or_set_mut(PathMap::new()).write_zipper_at_path(unsafe { core::ptr::slice_from_raw_parts(      in_.ptr, _with.ptr.byte_offset_from_unsigned(      in_.ptr)).as_ref().unwrap() });
                *wz_in.get_val_or_set_mut(0) += 1; // this should guarantee that the count of a value is always at least 1.

            },
            err => { self.skip = false; return}
        );
    }

    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        if self.skip { return false; }
        
        let WriteResource::BTM(mut wr_wz) = it.next().unwrap() else {unreachable!()};
        wr_wz.reset();
        let prefix_len = wr_wz.root_prefix_path().len();

        let Self { scope, e, out_template, skip, accumulator } = self;


        let mut ops_rz = accumulator.read_zipper();


        let [ mut buffer_in
            , mut buffer_op
            , mut buffer_out
            , mut buffer_template_original
            , mut buffer_template_computed 
            ] = 
            [ 2 /* unary op */
            , 3 /* binary op*/
            , 2 /* unary op */

            , 2 /* pair */
            , 2 /* pair */
            ].map(|b|Vec::from([mork_expr::item_byte(mork_expr::Tag::Arity(b))]));


        const UNIFICATION_BUFFER_SIZE : usize = 1 << 28;
        let mut unification_buffer = Vec::with_capacity(UNIFICATION_BUFFER_SIZE); // thats a 256 mib buffer
        // ! CAUTION !
        // This section is subtly unsafe, we need to have an __arity 2__ at the beginning of the allocation.
        // This is required, because if we do `ExprZipper::reset(&mut self)`, reset expects the zipper to point to an already 
        // initialized Expr, and reads the first byte to prepare a stack. Although it isn't strictly needed, putting the first byte makes 
        // refactoring the code mildy safer, it means `ExprZipper::reset(&mut self)` can happen before or after applying unification, 
        // while still having a valid zipper stack.
        // the alternative is reallocating the zipper stack every unification.
        unification_buffer.push(mork_expr::item_byte(mork_expr::Tag::Arity(2 /* pair */)));
        let unification_expr = Expr{ptr : unification_buffer.as_mut_ptr()};
        let mut unification_zipper = ExprZipper::new(unification_expr);

        
        const NEXT_STEP_GUARANTEE : &'static str = "to_next_step should guarantee that there is a value";

        'err_cleanup : {
            // we break here when there was a user error, falling through to cleanup
            'ops : loop {
                if !ops_rz.to_next_val() { break 'err_cleanup; /* if we are here we are done, we skip cleanup on error */}
    
                let ops = Expr{ptr:ops_rz.path() as *const[u8] as *const u8 as *mut u8};
                let [in_name, op_name, out_name] : [Expr; 3]  = destruct!(
                    ops,
                    ("with" ("In"  _In)
                            ("Op"  _Op)
                            ("Out" _Out)),
                    [_In, _Op, _Out],
                    err => unreachable!("Implementation of finalize() and sink() are out of sync.")
                );
                
                // put the names of each operation into the buffers
                // we the lengths with the arity when truncating on iterations, 
                let [buf_in_name_len,buf_op_name_len,buf_out_name_len] =
                [ (&mut buffer_in,  in_name)
                , (&mut buffer_op,  op_name)
                , (&mut buffer_out, out_name)
                ].map(
                    |(mut buf, op_name)| {
                        buf.truncate(1); // keep arity
                        buf.extend_from_slice(unsafe { op_name.span().as_ref().unwrap() });
                        buf.len()
                    }
                );             

                let mut template_rz = ops_rz.val().expect(NEXT_STEP_GUARANTEE).read_zipper();
                'template : while template_rz.to_next_val() {
                    let template_path = template_rz.path();
                    
                    // keep arity
                    buffer_template_original.truncate(1);
                    buffer_template_computed.truncate(1);
                    // append template
                    buffer_template_original.extend_from_slice(template_path);
                    buffer_template_computed.extend_from_slice(template_path);
                    // need this for truncation
                    let buf_template_len = buffer_template_original.len();                

                    let mut out_rz = template_rz.val().expect(NEXT_STEP_GUARANTEE).read_zipper();
                   'out : while out_rz.to_next_val() {                
    
                        let mut in_rz = out_rz.val().expect(NEXT_STEP_GUARANTEE).read_zipper();    
    
                        // if we got to this point, there must be at least one value
                        core::assert!(in_rz.to_next_val());

                        // any branch as at least one value, we acquire and get it's multiplicity
                        let mut first_val = |in_rz: &ReadZipperUntracked<'_, '_, usize>, scope : &mut EvalScope| {
                            let mut n = *in_rz.get_val().unwrap();
                            buffer_in.truncate(buf_in_name_len);
                            buffer_in.extend_from_slice(in_rz.path());
                            let e_src = ExprSource::new(buffer_in.as_ptr());                    
                            let maybe_val = scope.eval(e_src);
                            (maybe_val, n-1)
                        };
                        let (Ok(val), n) = first_val(&in_rz, scope) else { break 'ops; };
    
                        
                        let mut acc = val.clone();
    
                        let mut update_acc = |val:&_, n, scope : &mut EvalScope| 'update : {
                            for _ in 0..n {
                                buffer_op.truncate(buf_op_name_len);
                                buffer_op.extend_from_slice(&acc);
                                buffer_op.extend_from_slice(&val);
                                
                                let e_src    = ExprSource::new(buffer_op.as_ptr());
                                let Ok(next) = scope.eval(e_src) else { break 'update false;};
                                scope.return_alloc(core::mem::replace(&mut acc, next));
                            }
                            break 'update true;
                        };
                        
                        // it's n-1 the first time, because we need to construct the accumulator from the first one
                        if !update_acc(&val, n-1, scope) { break 'ops; }
                        scope.return_alloc(val);              
                        
                        // now we repeat, but we have an accumulator
                        '_in : while in_rz.to_next_val() {
                            let (Ok(val), n) = first_val(&in_rz, scope) else {break 'ops};
                            if !update_acc(&val,n, scope) { break 'ops; }
                            scope.return_alloc(val);
                        }

                        // we now have the full accumulator
                        // we now apply the out operation
                        buffer_out.truncate(buf_out_name_len);
                        buffer_out.extend_from_slice(&acc);
                        let e_src = ExprSource::new(buffer_out.as_ptr());
                        let Ok(mut result) = scope.eval(e_src) else { break 'ops };                        
                        scope.return_alloc(acc);

                        // this should happen anyways when running eval, but just to be sure...
                        if !(Expr{ptr : result.as_mut_ptr()}.is_ground()) {break 'ops; }

                        // keep the template
                        buffer_template_original.truncate(buf_template_len);
                        buffer_template_computed.truncate(buf_template_len);

                        // concat the out value pattern, and the out result
                        buffer_template_original.extend_from_slice(out_rz.path());
                        buffer_template_computed.extend_from_slice(&result);

                        // unify
                        unification_zipper.reset();
                        let Ok(_) = Expr::unify(
                                Expr{ptr : buffer_template_original.as_mut_ptr()},
                                Expr{ptr : buffer_template_computed.as_mut_ptr()},
                                &mut unification_zipper,
                            ) else {
                            // we are only filtering, it's not a user error
                            // try the template again with other out filters
                            scope.return_alloc(result); break 'out; 
                        };

                        // Success! We add to the output.
                        wr_wz.reset();
                        wr_wz.move_to_path(&unification_buffer[prefix_len..unification_zipper.loc]);
                        wr_wz.set_val(());


                        scope.return_alloc(result);
                    }
                }
    
            }
            

            // cleanup in case of an error
            wr_wz.reset();
            wr_wz.remove_branches(true);
            wr_wz.remove_val(true);
            return false;
        }        

        true
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

// (z3 <instance> <declaration or assertion>)
#[cfg(feature = "z3")]
pub struct Z3Sink { e: Expr, buffer: Vec<u8> }
#[cfg(feature = "z3")]
impl Sink for Z3Sink {
    fn new(e: Expr) -> Self {
        Z3Sink { e, buffer: vec![] }
    }
    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        destruct!(self.e, ("z3" {instance: &str} {decl: Expr}), {
            trace!(target: "sinks", "z3 requesting instance {instance}");
            return std::iter::once(WriteResourceRequest::Z3(instance));
        }, _err => { unreachable!() });
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "z3 at raw '{}'", serialize(path));
        let e = Expr { ptr: path.as_ptr().cast_mut() };
        e.serialize(&mut self.buffer, |e| std::str::from_utf8(e).unwrap());
        self.buffer.push(b'\n');
    }
    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, mut it: It) -> bool where 'a : 'w, 'k : 'w {
        trace!(target: "sink", "z3 writing buffer {}", std::str::from_utf8(&self.buffer[..]).unwrap());
        let WriteResource::Z3(ref mut p) = it.next().unwrap() else { unreachable!() };
        let mut stdin = p.stdin.as_mut().unwrap();
        stdin.write(&self.buffer[..]).unwrap();
        true
    }
}


pub enum ASink { AddSink(AddSink), RemoveSink(RemoveSink), HeadSink(HeadSink), CountSink(CountSink), HashSink(HashSink), SumSink(SumSink), AndSink(AndSink), ACTSink(ACTSink),
    #[cfg(feature = "wasm")]
    WASMSink(WASMSink),
    #[cfg(feature = "grounding")]
    PureSink(PureSink),
    #[cfg(feature = "z3")]
    Z3Sink(Z3Sink),
    AUSink(AUSink),
    USink(USink),
    CompatSink(CompatSink)
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
        }
    }
}
