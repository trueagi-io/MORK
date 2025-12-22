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
use pathmap::PathMap;
use eval::EvalScope;
use eval_ffi::ExprSource;
use crate::space::ACT_PATH;

pub(crate) enum WriteResourceRequest {
    BTM(&'static [u8]),
    ACT(&'static str)
}

pub(crate) enum WriteResource<'w, 'a, 'k> {
    BTM(&'w mut WriteZipperTracked<'a, 'k, ()>),
    ACT(())
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

mod pure {
    use log::trace;
    use std::io::Write;
    use eval::*;
    use eval_ffi::{ExprSink, ExprSource, SinkItem, SourceItem, EvalError, Tag};

    macro_rules! op {
        (num nary $name:ident($initial:expr, $t:ident: $tt:ty, $x:ident: $tx:ty) => $e:expr) => {
            pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
                let expr = unsafe { &mut *expr };
                let sink = unsafe { &mut *sink };
                let items = expr.consume_head_check(stringify!($name).as_bytes())?;
                let mut $t: $tt = $initial;
                for _ in 0..items {
                    let $x = expr.consume::<$tx>()?;
                    $t = $e;
                }
                sink.write(SinkItem::Symbol(($t).to_be_bytes()[..].into()))?;
                Ok(())
            }
        };
        (num ternary $name:ident($x:ident: $tx:ty, $y:ident: $ty:ty, $z:ident: $tz:ty) => $e:expr) => {
            pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
                let expr = unsafe { &mut *expr };
                let sink = unsafe { &mut *sink };
                let items = expr.consume_head_check(stringify!($name).as_bytes())?;
                if items != 3 { return Err(EvalError::from(concat!(stringify!($name), " takes three arguments"))) }
                let $x = expr.consume::<$tx>()?;
                let $y = expr.consume::<$ty>()?;
                let $z = expr.consume::<$tz>()?;
                sink.write(SinkItem::Symbol(($e).to_be_bytes()[..].into()))?;
                Ok(())
            }
        };
        (num binary $name:ident($x:ident: $tx:ty, $y:ident: $ty:ty) => $e:expr) => {
            pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
                let expr = unsafe { &mut *expr };
                let sink = unsafe { &mut *sink };
                let items = expr.consume_head_check(stringify!($name).as_bytes())?;
                if items != 2 { return Err(EvalError::from(concat!(stringify!($name), " takes two arguments"))) }
                let $x = expr.consume::<$tx>()?;
                let $y = expr.consume::<$ty>()?;
                sink.write(SinkItem::Symbol(($e).to_be_bytes()[..].into()))?;
                Ok(())
            }
        };
        (num unary $name:ident($x:ident: $tx:ty) => $e:expr) => {
            pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
                let expr = unsafe { &mut *expr };
                let sink = unsafe { &mut *sink };
                let items = expr.consume_head_check(stringify!($name).as_bytes())?;
                if items != 1 { return Err(EvalError::from(concat!(stringify!($name), " takes one argument"))) }
                let $x = expr.consume::<$tx>()?;
                sink.write(SinkItem::Symbol(($e).to_be_bytes()[..].into()))?;
                Ok(())
            }
        };
        (num nulary $name:ident() => $e:expr) => {
            pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
                let expr = unsafe { &mut *expr };
                let sink = unsafe { &mut *sink };
                let items = expr.consume_head_check(stringify!($name).as_bytes())?;
                if items != 0 { return Err(EvalError::from(concat!(stringify!($name), " takes no arguments"))) }
                sink.write(SinkItem::Symbol(($e).to_be_bytes()[..].into()))?;
                Ok(())
            }
        };
        (num from_string $name:ident<$t:ty>) => {
            pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
                let expr = unsafe { &mut *expr };
                let sink = unsafe { &mut *sink };
                let items = expr.consume_head_check(stringify!($name).as_bytes())?;
                if items != 1 { return Err(EvalError::from("only takes one argument")) }
                let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only parses symbols")) };
                let result: $t = str::from_utf8(symbol).map_err(|_| EvalError::from(concat!(stringify!($name), " parsing string not utf8")))?.parse().map_err(|_| EvalError::from(concat!("string not a valid type", stringify!($name))))?;
                sink.write(SinkItem::Symbol(result.to_be_bytes()[..].into()))?;
                Ok(())
            }
        };
        (num to_string $name:ident<$t:ty>) => {
            pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
                let expr = unsafe { &mut *expr };
                let sink = unsafe { &mut *sink };
                let items = expr.consume_head_check(stringify!($name).as_bytes())?;
                if items != 1 { return Err(EvalError::from("only takes one argument")) }
                let x = expr.consume::<$t>()?;
                let mut buf = [0u8; 64];
                let mut cur = std::io::Cursor::new(&mut buf[..]);
                write!(&mut cur, "{}", x).unwrap();
                let pos = cur.position() as usize;
                sink.write(SinkItem::Symbol(&buf[..pos]))?;
                Ok(())
            }
        };
    }

    op!(num unary i8_as_i16(x: i8) => x as i16);
    op!(num unary i8_as_i32(x: i8) => x as i32);
    op!(num unary i8_as_i64(x: i8) => x as i64);
    op!(num unary i8_as_f32(x: i8) => x as f32);
    op!(num unary i8_as_f64(x: i8) => x as f64);
    op!(num unary neg_i8(x: i8) => -x);
    op!(num unary abs_i8(x: i8) => x.abs());
    op!(num unary signum_i8(x: i8) => x.signum());
    op!(num binary sub_i8(x: i8, y: i8) => x - y);
    op!(num binary div_i8(x: i8, y: i8) => x / y);
    op!(num binary mod_i8(x: i8, y: i8) => x % y);
    op!(num binary pow_i8(x: i8, exp: i8) => x.pow(exp as u32));
    op!(num ternary clamp_i8(x: i8, y: i8, z: i8) => x.clamp(y, z));
    op!(num nary sum_i8(0i8, t: i8, x: i8) => t + x);
    op!(num nary product_i8(1i8, t: i8, x: i8) => t * x);
    op!(num nary max_i8(i8::MIN, t: i8, x: i8) => t.max(x));
    op!(num nary min_i8(i8::MAX, t: i8, x: i8) => t.min(x));
    op!(num from_string i8_from_string<i8>);
    op!(num to_string i8_to_string<i8>);

    op!(num unary i16_as_i8(x: i16) => x as i8);
    op!(num unary i16_as_i32(x: i16) => x as i32);
    op!(num unary i16_as_i64(x: i16) => x as i64);
    op!(num unary i16_as_f32(x: i16) => x as f32);
    op!(num unary i16_as_f64(x: i16) => x as f64);
    op!(num unary neg_i16(x: i16) => -x);
    op!(num unary abs_i16(x: i16) => x.abs());
    op!(num unary signum_i16(x: i16) => x.signum());
    op!(num binary sub_i16(x: i16, y: i16) => x - y);
    op!(num binary div_i16(x: i16, y: i16) => x / y);
    op!(num binary mod_i16(x: i16, y: i16) => x % y);
    op!(num binary pow_i16(x: i16, exp: i16) => x.pow(exp as u32));
    op!(num ternary clamp_i16(x: i16, y: i16, z: i16) => x.clamp(y, z));
    op!(num nary sum_i16(0i16, t: i16, x: i16) => t + x);
    op!(num nary product_i16(1i16, t: i16, x: i16) => t * x);
    op!(num nary max_i16(i16::MIN, t: i16, x: i16) => t.max(x));
    op!(num nary min_i16(i16::MAX, t: i16, x: i16) => t.min(x));
    op!(num from_string i16_from_string<i16>);
    op!(num to_string i16_to_string<i16>);

    op!(num unary i32_as_i8(x: i32) => x as i8);
    op!(num unary i32_as_i16(x: i32) => x as i16);
    op!(num unary i32_as_i64(x: i32) => x as i64);
    op!(num unary i32_as_f32(x: i32) => x as f32);
    op!(num unary i32_as_f64(x: i32) => x as f64);
    op!(num unary neg_i32(x: i32) => -x);
    op!(num unary abs_i32(x: i32) => x.abs());
    op!(num unary signum_i32(x: i32) => x.signum());
    op!(num binary sub_i32(x: i32, y: i32) => x - y);
    op!(num binary div_i32(x: i32, y: i32) => x / y);
    op!(num binary mod_i32(x: i32, y: i32) => x % y);
    op!(num binary pow_i32(x: i32, exp: i32) => x.pow(exp as u32));
    op!(num ternary clamp_i32(x: i32, y: i32, z: i32) => x.clamp(y, z));
    op!(num nary sum_i32(0i32, t: i32, x: i32) => t + x);
    op!(num nary product_i32(1i32, t: i32, x: i32) => t * x);
    op!(num nary max_i32(i32::MIN, t: i32, x: i32) => t.max(x));
    op!(num nary min_i32(i32::MAX, t: i32, x: i32) => t.min(x));
    op!(num from_string i32_from_string<i32>);
    op!(num to_string i32_to_string<i32>);

    op!(num unary i64_as_i8(x: i64) => x as i8);
    op!(num unary i64_as_i16(x: i64) => x as i16);
    op!(num unary i64_as_i32(x: i64) => x as i32);
    op!(num unary i64_as_f32(x: i64) => x as f32);
    op!(num unary i64_as_f64(x: i64) => x as f64);
    op!(num unary neg_i64(x: i64) => -x);
    op!(num unary abs_i64(x: i64) => x.abs());
    op!(num unary signum_i64(x: i64) => x.signum());
    op!(num binary sub_i64(x: i64, y: i64) => x - y);
    op!(num binary div_i64(x: i64, y: i64) => x / y);
    op!(num binary mod_i64(x: i64, y: i64) => x % y);
    op!(num binary pow_i64(x: i64, exp: i64) => x.pow(exp as u32));
    op!(num ternary clamp_i64(x: i64, y: i64, z: i64) => x.clamp(y, z));
    op!(num nary sum_i64(0i64, t: i64, x: i64) => t + x);
    op!(num nary product_i64(1i64, t: i64, x: i64) => t * x);
    op!(num nary max_i64(i64::MIN, t: i64, x: i64) => t.max(x));
    op!(num nary min_i64(i64::MAX, t: i64, x: i64) => t.min(x));
    op!(num from_string i64_from_string<i64>);
    op!(num to_string i64_to_string<i64>);

    op!(num unary f64_as_i8(x: f64) => x as i8);
    op!(num unary f64_as_i16(x: f64) => x as i16);
    op!(num unary f64_as_i32(x: f64) => x as i32);
    op!(num unary f64_as_i64(x: f64) => x as i64);
    op!(num unary f64_as_f32(x: f64) => x as f32);
    op!(num nulary inf_f64() => f64::INFINITY);
    op!(num nulary neginf_f64() => f64::NEG_INFINITY);
    op!(num nulary e_f64() => std::f64::consts::E);
    op!(num nulary pi_f64() => std::f64::consts::PI);
    op!(num nulary tau_f64() => std::f64::consts::TAU);
    op!(num nulary phi_f64() => std::f64::consts::PHI);
    op!(num unary to_radians_f64(x: f64) => x.to_radians());
    op!(num unary to_degrees_f64(x: f64) => x.to_degrees());
    op!(num unary sin_f64(x: f64) => x.sin());
    op!(num unary cos_f64(x: f64) => x.cos());
    op!(num unary tan_f64(x: f64) => x.tan());
    op!(num unary asin_f64(x: f64) => x.asin());
    op!(num unary acos_f64(x: f64) => x.acos());
    op!(num unary atan_f64(x: f64) => x.atan());
    op!(num unary sinh_f64(x: f64) => x.sinh());
    op!(num unary cosh_f64(x: f64) => x.cosh());
    op!(num unary tanh_f64(x: f64) => x.tanh());
    op!(num unary asinh_f64(x: f64) => x.asinh());
    op!(num unary acosh_f64(x: f64) => x.acosh());
    op!(num unary atanh_f64(x: f64) => x.atanh());
    op!(num unary neg_f64(x: f64) => -x);
    op!(num unary abs_f64(x: f64) => x.abs());
    op!(num unary floor_f64(x: f64) => x.floor());
    op!(num unary ceil_f64(x: f64) => x.ceil());
    op!(num unary round_f64(x: f64) => x.round());
    op!(num unary sqrt_f64(x: f64) => x.sqrt());
    op!(num unary cbrt_f64(x: f64) => x.cbrt());
    op!(num unary exp_f64(x: f64) => x.exp());
    op!(num unary exp2_f64(x: f64) => x.exp2());
    op!(num unary ln_f64(x: f64) => x.ln());
    op!(num unary log2_f64(x: f64) => x.log2());
    op!(num unary log10_f64(x: f64) => x.log10());
    op!(num unary trunc_f64(x: f64) => x.trunc());
    op!(num unary recip_f64(x: f64) => x.recip());
    op!(num unary fract_f64(x: f64) => x.fract());
    op!(num unary signum_f64(x: f64) => x.signum());
    op!(num binary copysign_f64(x: f64, s: f64) => x.copysign(s));
    op!(num binary powf_f64(x: f64, exp: f64) => x.powf(exp));
    op!(num binary powi_f64(x: f64, exp: i32) => x.powi(exp));
    op!(num binary sub_f64(x: f64, y: f64) => x - y);
    op!(num binary div_f64(x: f64, y: f64) => x / y);
    op!(num binary atan2_f64(x: f64, y: f64) => x.atan2(y));
    op!(num binary hypot_f64(x: f64, y: f64) => x.hypot(y));
    op!(num ternary clamp_f64(x: f64, y: f64, z: f64) => x.clamp(y, z));
    op!(num nary sum_f64(0f64, t: f64, x: f64) => t + x);
    op!(num nary product_f64(1f64, t: f64, x: f64) => t * x);
    op!(num nary max_f64(f64::NEG_INFINITY, t: f64, x: f64) => t.max(x));
    op!(num nary min_f64(f64::INFINITY, t: f64, x: f64) => t.min(x));
    op!(num from_string f64_from_string<f64>);
    op!(num to_string f64_to_string<f64>);

    op!(num unary f32_as_i8(x: f32) => x as i8);
    op!(num unary f32_as_i16(x: f32) => x as i16);
    op!(num unary f32_as_i32(x: f32) => x as i32);
    op!(num unary f32_as_i64(x: f32) => x as i64);
    op!(num unary f32_as_f64(x: f32) => x as f64);
    op!(num nulary inf_f32() => f32::INFINITY);
    op!(num nulary neginf_f32() => f32::NEG_INFINITY);
    op!(num nulary e_f32() => std::f32::consts::E);
    op!(num nulary pi_f32() => std::f32::consts::PI);
    op!(num nulary tau_f32() => std::f32::consts::TAU);
    op!(num nulary phi_f32() => std::f32::consts::PHI);
    op!(num unary to_radians_f32(x: f32) => x.to_radians());
    op!(num unary to_degrees_f32(x: f32) => x.to_degrees());
    op!(num unary sin_f32(x: f32) => x.sin());
    op!(num unary cos_f32(x: f32) => x.cos());
    op!(num unary tan_f32(x: f32) => x.tan());
    op!(num unary asin_f32(x: f32) => x.asin());
    op!(num unary acos_f32(x: f32) => x.acos());
    op!(num unary atan_f32(x: f32) => x.atan());
    op!(num unary sinh_f32(x: f32) => x.sinh());
    op!(num unary cosh_f32(x: f32) => x.cosh());
    op!(num unary tanh_f32(x: f32) => x.tanh());
    op!(num unary asinh_f32(x: f32) => x.asinh());
    op!(num unary acosh_f32(x: f32) => x.acosh());
    op!(num unary atanh_f32(x: f32) => x.atanh());
    op!(num unary neg_f32(x: f32) => -x);
    op!(num unary abs_f32(x: f32) => x.abs());
    op!(num unary floor_f32(x: f32) => x.floor());
    op!(num unary ceil_f32(x: f32) => x.ceil());
    op!(num unary round_f32(x: f32) => x.round());
    op!(num unary sqrt_f32(x: f32) => x.sqrt());
    op!(num unary cbrt_f32(x: f32) => x.cbrt());
    op!(num unary exp_f32(x: f32) => x.exp());
    op!(num unary exp2_f32(x: f32) => x.exp2());
    op!(num unary ln_f32(x: f32) => x.ln());
    op!(num unary log2_f32(x: f32) => x.log2());
    op!(num unary log10_f32(x: f32) => x.log10());
    op!(num unary trunc_f32(x: f32) => x.trunc());
    op!(num unary recip_f32(x: f32) => x.recip());
    op!(num unary fract_f32(x: f32) => x.fract());
    op!(num unary signum_f32(x: f32) => x.signum());
    op!(num binary copysign_f32(x: f32, s: f32) => x.copysign(s));
    op!(num binary powf_f32(x: f32, exp: f32) => x.powf(exp));
    op!(num binary powi_f32(x: f32, exp: i32) => x.powi(exp));
    op!(num binary sub_f32(x: f32, y: f32) => x - y);
    op!(num binary div_f32(x: f32, y: f32) => x / y);
    op!(num binary atan2_f32(x: f32, y: f32) => x.atan2(y));
    op!(num binary hypot_f32(x: f32, y: f32) => x.hypot(y));
    op!(num ternary clamp_f32(x: f32, y: f32, z: f32) => x.clamp(y, z));
    op!(num nary sum_f32(0f32, t: f32, x: f32) => t + x);
    op!(num nary product_f32(1f32, t: f32, x: f32) => t * x);
    op!(num nary max_f32(f32::NEG_INFINITY, t: f32, x: f32) => t.max(x));
    op!(num nary min_f32(f32::INFINITY, t: f32, x: f32) => t.min(x));
    op!(num from_string f32_from_string<f32>);
    op!(num to_string f32_to_string<f32>);

    pub extern "C" fn reverse_symbol(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
        let expr = unsafe { &mut *expr };
        let sink = unsafe { &mut *sink };
        let items = expr.consume_head_check(b"reverse_symbol")?;
        if items != 1 { return Err(EvalError::from("only takes one argument")) }
        trace!(target: "ground", "reverse_symbol consumed {:?}", items);
        let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only reverses symbols")) };
        let mut buf = [0u8; 64];
        buf[..symbol.len()].clone_from_slice(symbol);
        buf[..symbol.len()].reverse();
        sink.write(SinkItem::Symbol(&buf[..symbol.len()]))?;
        Ok(())
    }
}

// (pure (result $x) $x (f32_from_string 0.2))
#[cfg(feature = "grounding")]
pub struct PureSink { e: Expr, unique: PathMap<()> , scope: EvalScope }
impl Sink for PureSink {
    fn new(e: Expr) -> Self {
        let mut scope = EvalScope::new();

        scope.add_func("reverse_symbol", pure::reverse_symbol, eval::FuncType::Pure);
        
        // GENERATED from the above
        // op!\(num \w+ (\w+)\W.+
        // scope.add_func("$1", pure::$1, eval::FuncType::Pure);
        scope.add_func("i8_as_i16", pure::i8_as_i16, eval::FuncType::Pure);
        scope.add_func("i8_as_i32", pure::i8_as_i32, eval::FuncType::Pure);
        scope.add_func("i8_as_i64", pure::i8_as_i64, eval::FuncType::Pure);
        scope.add_func("i8_as_f32", pure::i8_as_f32, eval::FuncType::Pure);
        scope.add_func("i8_as_f64", pure::i8_as_f64, eval::FuncType::Pure);
        scope.add_func("neg_i8", pure::neg_i8, eval::FuncType::Pure);
        scope.add_func("abs_i8", pure::abs_i8, eval::FuncType::Pure);
        scope.add_func("signum_i8", pure::signum_i8, eval::FuncType::Pure);
        scope.add_func("sub_i8", pure::sub_i8, eval::FuncType::Pure);
        scope.add_func("div_i8", pure::div_i8, eval::FuncType::Pure);
        scope.add_func("mod_i8", pure::mod_i8, eval::FuncType::Pure);
        scope.add_func("pow_i8", pure::pow_i8, eval::FuncType::Pure);
        scope.add_func("clamp_i8", pure::clamp_i8, eval::FuncType::Pure);
        scope.add_func("sum_i8", pure::sum_i8, eval::FuncType::Pure);
        scope.add_func("product_i8", pure::product_i8, eval::FuncType::Pure);
        scope.add_func("max_i8", pure::max_i8, eval::FuncType::Pure);
        scope.add_func("min_i8", pure::min_i8, eval::FuncType::Pure);
        scope.add_func("i8_from_string", pure::i8_from_string, eval::FuncType::Pure);
        scope.add_func("i8_to_string", pure::i8_to_string, eval::FuncType::Pure);

        scope.add_func("i16_as_i8", pure::i16_as_i8, eval::FuncType::Pure);
        scope.add_func("i16_as_i32", pure::i16_as_i32, eval::FuncType::Pure);
        scope.add_func("i16_as_i64", pure::i16_as_i64, eval::FuncType::Pure);
        scope.add_func("i16_as_f32", pure::i16_as_f32, eval::FuncType::Pure);
        scope.add_func("i16_as_f64", pure::i16_as_f64, eval::FuncType::Pure);
        scope.add_func("neg_i16", pure::neg_i16, eval::FuncType::Pure);
        scope.add_func("abs_i16", pure::abs_i16, eval::FuncType::Pure);
        scope.add_func("signum_i16", pure::signum_i16, eval::FuncType::Pure);
        scope.add_func("sub_i16", pure::sub_i16, eval::FuncType::Pure);
        scope.add_func("div_i16", pure::div_i16, eval::FuncType::Pure);
        scope.add_func("mod_i16", pure::mod_i16, eval::FuncType::Pure);
        scope.add_func("pow_i16", pure::pow_i16, eval::FuncType::Pure);
        scope.add_func("clamp_i16", pure::clamp_i16, eval::FuncType::Pure);
        scope.add_func("sum_i16", pure::sum_i16, eval::FuncType::Pure);
        scope.add_func("product_i16", pure::product_i16, eval::FuncType::Pure);
        scope.add_func("max_i16", pure::max_i16, eval::FuncType::Pure);
        scope.add_func("min_i16", pure::min_i16, eval::FuncType::Pure);
        scope.add_func("i16_from_string", pure::i16_from_string, eval::FuncType::Pure);
        scope.add_func("i16_to_string", pure::i16_to_string, eval::FuncType::Pure);

        scope.add_func("i32_as_i8", pure::i32_as_i8, eval::FuncType::Pure);
        scope.add_func("i32_as_i16", pure::i32_as_i16, eval::FuncType::Pure);
        scope.add_func("i32_as_i64", pure::i32_as_i64, eval::FuncType::Pure);
        scope.add_func("i32_as_f32", pure::i32_as_f32, eval::FuncType::Pure);
        scope.add_func("i32_as_f64", pure::i32_as_f64, eval::FuncType::Pure);
        scope.add_func("neg_i32", pure::neg_i32, eval::FuncType::Pure);
        scope.add_func("abs_i32", pure::abs_i32, eval::FuncType::Pure);
        scope.add_func("signum_i32", pure::signum_i32, eval::FuncType::Pure);
        scope.add_func("sub_i32", pure::sub_i32, eval::FuncType::Pure);
        scope.add_func("div_i32", pure::div_i32, eval::FuncType::Pure);
        scope.add_func("mod_i32", pure::mod_i32, eval::FuncType::Pure);
        scope.add_func("pow_i32", pure::pow_i32, eval::FuncType::Pure);
        scope.add_func("clamp_i32", pure::clamp_i32, eval::FuncType::Pure);
        scope.add_func("sum_i32", pure::sum_i32, eval::FuncType::Pure);
        scope.add_func("product_i32", pure::product_i32, eval::FuncType::Pure);
        scope.add_func("max_i32", pure::max_i32, eval::FuncType::Pure);
        scope.add_func("min_i32", pure::min_i32, eval::FuncType::Pure);
        scope.add_func("i32_from_string", pure::i32_from_string, eval::FuncType::Pure);
        scope.add_func("i32_to_string", pure::i32_to_string, eval::FuncType::Pure);

        scope.add_func("i64_as_i8", pure::i64_as_i8, eval::FuncType::Pure);
        scope.add_func("i64_as_i16", pure::i64_as_i16, eval::FuncType::Pure);
        scope.add_func("i64_as_i32", pure::i64_as_i32, eval::FuncType::Pure);
        scope.add_func("i64_as_f32", pure::i64_as_f32, eval::FuncType::Pure);
        scope.add_func("i64_as_f64", pure::i64_as_f64, eval::FuncType::Pure);
        scope.add_func("neg_i64", pure::neg_i64, eval::FuncType::Pure);
        scope.add_func("abs_i64", pure::abs_i64, eval::FuncType::Pure);
        scope.add_func("signum_i64", pure::signum_i64, eval::FuncType::Pure);
        scope.add_func("sub_i64", pure::sub_i64, eval::FuncType::Pure);
        scope.add_func("div_i64", pure::div_i64, eval::FuncType::Pure);
        scope.add_func("mod_i64", pure::mod_i64, eval::FuncType::Pure);
        scope.add_func("pow_i64", pure::pow_i64, eval::FuncType::Pure);
        scope.add_func("clamp_i64", pure::clamp_i64, eval::FuncType::Pure);
        scope.add_func("sum_i64", pure::sum_i64, eval::FuncType::Pure);
        scope.add_func("product_i64", pure::product_i64, eval::FuncType::Pure);
        scope.add_func("max_i64", pure::max_i64, eval::FuncType::Pure);
        scope.add_func("min_i64", pure::min_i64, eval::FuncType::Pure);
        scope.add_func("i64_from_string", pure::i64_from_string, eval::FuncType::Pure);
        scope.add_func("i64_to_string", pure::i64_to_string, eval::FuncType::Pure);

        scope.add_func("f64_as_i8", pure::f64_as_i8, eval::FuncType::Pure);
        scope.add_func("f64_as_i16", pure::f64_as_i16, eval::FuncType::Pure);
        scope.add_func("f64_as_i32", pure::f64_as_i32, eval::FuncType::Pure);
        scope.add_func("f64_as_i64", pure::f64_as_i64, eval::FuncType::Pure);
        scope.add_func("f64_as_f32", pure::f64_as_f32, eval::FuncType::Pure);
        scope.add_func("inf_f64", pure::inf_f64, eval::FuncType::Pure);
        scope.add_func("neginf_f64", pure::neginf_f64, eval::FuncType::Pure);
        scope.add_func("e_f64", pure::e_f64, eval::FuncType::Pure);
        scope.add_func("pi_f64", pure::pi_f64, eval::FuncType::Pure);
        scope.add_func("tau_f64", pure::tau_f64, eval::FuncType::Pure);
        scope.add_func("phi_f64", pure::phi_f64, eval::FuncType::Pure);
        scope.add_func("to_radians_f64", pure::to_radians_f64, eval::FuncType::Pure);
        scope.add_func("to_degrees_f64", pure::to_degrees_f64, eval::FuncType::Pure);
        scope.add_func("sin_f64", pure::sin_f64, eval::FuncType::Pure);
        scope.add_func("cos_f64", pure::cos_f64, eval::FuncType::Pure);
        scope.add_func("tan_f64", pure::tan_f64, eval::FuncType::Pure);
        scope.add_func("asin_f64", pure::asin_f64, eval::FuncType::Pure);
        scope.add_func("acos_f64", pure::acos_f64, eval::FuncType::Pure);
        scope.add_func("atan_f64", pure::atan_f64, eval::FuncType::Pure);
        scope.add_func("sinh_f64", pure::sinh_f64, eval::FuncType::Pure);
        scope.add_func("cosh_f64", pure::cosh_f64, eval::FuncType::Pure);
        scope.add_func("tanh_f64", pure::tanh_f64, eval::FuncType::Pure);
        scope.add_func("asinh_f64", pure::asinh_f64, eval::FuncType::Pure);
        scope.add_func("acosh_f64", pure::acosh_f64, eval::FuncType::Pure);
        scope.add_func("atanh_f64", pure::atanh_f64, eval::FuncType::Pure);
        scope.add_func("neg_f64", pure::neg_f64, eval::FuncType::Pure);
        scope.add_func("abs_f64", pure::abs_f64, eval::FuncType::Pure);
        scope.add_func("floor_f64", pure::floor_f64, eval::FuncType::Pure);
        scope.add_func("ceil_f64", pure::ceil_f64, eval::FuncType::Pure);
        scope.add_func("round_f64", pure::round_f64, eval::FuncType::Pure);
        scope.add_func("sqrt_f64", pure::sqrt_f64, eval::FuncType::Pure);
        scope.add_func("cbrt_f64", pure::cbrt_f64, eval::FuncType::Pure);
        scope.add_func("exp_f64", pure::exp_f64, eval::FuncType::Pure);
        scope.add_func("exp2_f64", pure::exp2_f64, eval::FuncType::Pure);
        scope.add_func("ln_f64", pure::ln_f64, eval::FuncType::Pure);
        scope.add_func("log2_f64", pure::log2_f64, eval::FuncType::Pure);
        scope.add_func("log10_f64", pure::log10_f64, eval::FuncType::Pure);
        scope.add_func("trunc_f64", pure::trunc_f64, eval::FuncType::Pure);
        scope.add_func("recip_f64", pure::recip_f64, eval::FuncType::Pure);
        scope.add_func("fract_f64", pure::fract_f64, eval::FuncType::Pure);
        scope.add_func("signum_f64", pure::signum_f64, eval::FuncType::Pure);
        scope.add_func("copysign_f64", pure::copysign_f64, eval::FuncType::Pure);
        scope.add_func("powf_f64", pure::powf_f64, eval::FuncType::Pure);
        scope.add_func("powi_f64", pure::powi_f64, eval::FuncType::Pure);
        scope.add_func("sub_f64", pure::sub_f64, eval::FuncType::Pure);
        scope.add_func("div_f64", pure::div_f64, eval::FuncType::Pure);
        scope.add_func("atan2_f64", pure::atan2_f64, eval::FuncType::Pure);
        scope.add_func("hypot_f64", pure::hypot_f64, eval::FuncType::Pure);
        scope.add_func("clamp_f64", pure::clamp_f64, eval::FuncType::Pure);
        scope.add_func("sum_f64", pure::sum_f64, eval::FuncType::Pure);
        scope.add_func("product_f64", pure::product_f64, eval::FuncType::Pure);
        scope.add_func("max_f64", pure::max_f64, eval::FuncType::Pure);
        scope.add_func("min_f64", pure::min_f64, eval::FuncType::Pure);
        scope.add_func("f64_from_string", pure::f64_from_string, eval::FuncType::Pure);
        scope.add_func("f64_to_string", pure::f64_to_string, eval::FuncType::Pure);

        scope.add_func("f32_as_i8", pure::f32_as_i8, eval::FuncType::Pure);
        scope.add_func("f32_as_i16", pure::f32_as_i16, eval::FuncType::Pure);
        scope.add_func("f32_as_i32", pure::f32_as_i32, eval::FuncType::Pure);
        scope.add_func("f32_as_i64", pure::f32_as_i64, eval::FuncType::Pure);
        scope.add_func("f32_as_f64", pure::f32_as_f64, eval::FuncType::Pure);
        scope.add_func("inf_f32", pure::inf_f32, eval::FuncType::Pure);
        scope.add_func("neginf_f32", pure::neginf_f32, eval::FuncType::Pure);
        scope.add_func("e_f32", pure::e_f32, eval::FuncType::Pure);
        scope.add_func("pi_f32", pure::pi_f32, eval::FuncType::Pure);
        scope.add_func("tau_f32", pure::tau_f32, eval::FuncType::Pure);
        scope.add_func("phi_f32", pure::phi_f32, eval::FuncType::Pure);
        scope.add_func("to_radians_f32", pure::to_radians_f32, eval::FuncType::Pure);
        scope.add_func("to_degrees_f32", pure::to_degrees_f32, eval::FuncType::Pure);
        scope.add_func("sin_f32", pure::sin_f32, eval::FuncType::Pure);
        scope.add_func("cos_f32", pure::cos_f32, eval::FuncType::Pure);
        scope.add_func("tan_f32", pure::tan_f32, eval::FuncType::Pure);
        scope.add_func("asin_f32", pure::asin_f32, eval::FuncType::Pure);
        scope.add_func("acos_f32", pure::acos_f32, eval::FuncType::Pure);
        scope.add_func("atan_f32", pure::atan_f32, eval::FuncType::Pure);
        scope.add_func("sinh_f32", pure::sinh_f32, eval::FuncType::Pure);
        scope.add_func("cosh_f32", pure::cosh_f32, eval::FuncType::Pure);
        scope.add_func("tanh_f32", pure::tanh_f32, eval::FuncType::Pure);
        scope.add_func("asinh_f32", pure::asinh_f32, eval::FuncType::Pure);
        scope.add_func("acosh_f32", pure::acosh_f32, eval::FuncType::Pure);
        scope.add_func("atanh_f32", pure::atanh_f32, eval::FuncType::Pure);
        scope.add_func("neg_f32", pure::neg_f32, eval::FuncType::Pure);
        scope.add_func("abs_f32", pure::abs_f32, eval::FuncType::Pure);
        scope.add_func("floor_f32", pure::floor_f32, eval::FuncType::Pure);
        scope.add_func("ceil_f32", pure::ceil_f32, eval::FuncType::Pure);
        scope.add_func("round_f32", pure::round_f32, eval::FuncType::Pure);
        scope.add_func("sqrt_f32", pure::sqrt_f32, eval::FuncType::Pure);
        scope.add_func("cbrt_f32", pure::cbrt_f32, eval::FuncType::Pure);
        scope.add_func("exp_f32", pure::exp_f32, eval::FuncType::Pure);
        scope.add_func("exp2_f32", pure::exp2_f32, eval::FuncType::Pure);
        scope.add_func("ln_f32", pure::ln_f32, eval::FuncType::Pure);
        scope.add_func("log2_f32", pure::log2_f32, eval::FuncType::Pure);
        scope.add_func("log10_f32", pure::log10_f32, eval::FuncType::Pure);
        scope.add_func("trunc_f32", pure::trunc_f32, eval::FuncType::Pure);
        scope.add_func("recip_f32", pure::recip_f32, eval::FuncType::Pure);
        scope.add_func("fract_f32", pure::fract_f32, eval::FuncType::Pure);
        scope.add_func("signum_f32", pure::signum_f32, eval::FuncType::Pure);
        scope.add_func("copysign_f32", pure::copysign_f32, eval::FuncType::Pure);
        scope.add_func("powf_f32", pure::powf_f32, eval::FuncType::Pure);
        scope.add_func("powi_f32", pure::powi_f32, eval::FuncType::Pure);
        scope.add_func("sub_f32", pure::sub_f32, eval::FuncType::Pure);
        scope.add_func("div_f32", pure::div_f32, eval::FuncType::Pure);
        scope.add_func("atan2_f32", pure::atan2_f32, eval::FuncType::Pure);
        scope.add_func("hypot_f32", pure::hypot_f32, eval::FuncType::Pure);
        scope.add_func("clamp_f32", pure::clamp_f32, eval::FuncType::Pure);
        scope.add_func("sum_f32", pure::sum_f32, eval::FuncType::Pure);
        scope.add_func("product_f32", pure::product_f32, eval::FuncType::Pure);
        scope.add_func("max_f32", pure::max_f32, eval::FuncType::Pure);
        scope.add_func("min_f32", pure::min_f32, eval::FuncType::Pure);
        scope.add_func("f32_from_string", pure::f32_from_string, eval::FuncType::Pure);
        scope.add_func("f32_to_string", pure::f32_to_string, eval::FuncType::Pure);
        
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
                            Err(er) => { trace!(target: "sink", "err {}", er); continue 'vals }
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


pub enum ASink { AddSink(AddSink), RemoveSink(RemoveSink), HeadSink(HeadSink), CountSink(CountSink), SumSink(SumSink), ACTSink(ACTSink),
    #[cfg(feature = "wasm")]
    WASMSink(WASMSink),
    #[cfg(feature = "grounding")]
    PureSink(PureSink)
}

impl Sink for ASink {
    fn new(e: Expr) -> Self {
        if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1)) && *e.ptr.offset(2) == b'-' } {
            ASink::RemoveSink(RemoveSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(2)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(1)) && *e.ptr.offset(2) == b'+' } {
            ASink::AddSink(AddSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(3)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(4)) &&
            *e.ptr.offset(2) == b'h' && *e.ptr.offset(3) == b'e' && *e.ptr.offset(4) == b'a' && *e.ptr.offset(5) == b'd' } {
            ASink::HeadSink(HeadSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(5)) &&
            *e.ptr.offset(2) == b'c' && *e.ptr.offset(3) == b'o' && *e.ptr.offset(4) == b'u' && *e.ptr.offset(5) == b'n' && *e.ptr.offset(6) == b't' } {
            ASink::CountSink(CountSink::new(e))
        } else if unsafe { *e.ptr == item_byte(Tag::Arity(4)) && *e.ptr.offset(1) == item_byte(Tag::SymbolSize(3)) &&
            *e.ptr.offset(2) == b's' && *e.ptr.offset(3) == b'u' && *e.ptr.offset(4) == b'm' } {
            return ASink::SumSink(SumSink::new(e));
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
        } else {
            unreachable!()
        }
    }

    fn request(&self) ->  impl Iterator<Item=WriteResourceRequest> {
        gen move {
            match self {
                ASink::AddSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::RemoveSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::HeadSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::CountSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::SumSink(s) => { for i in s.request().into_iter() { yield i } }
                ASink::ACTSink(s) => { for i in s.request().into_iter() { yield i } }
                #[cfg(feature = "wasm")]
                ASink::WASMSink(s) => { for i in s.request().into_iter() { yield i } }
                #[cfg(feature = "grounding")]
                ASink::PureSink(s) => { for i in s.request().into_iter() { yield i } }
            }
        }
    }
    fn sink<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It, path: &[u8]) where 'a : 'w, 'k : 'w {
        match self {
            ASink::AddSink(s) => { s.sink(it, path) }
            ASink::RemoveSink(s) => { s.sink(it, path) }
            ASink::HeadSink(s) => { s.sink(it, path) }
            ASink::CountSink(s) => { s.sink(it, path) }
            ASink::SumSink(s) => { s.sink(it, path) }
            ASink::ACTSink(s) => { s.sink(it, path) }
            #[cfg(feature = "wasm")]
            ASink::WASMSink(s) => { s.sink(it, path) }
            #[cfg(feature = "grounding")]
            ASink::PureSink(s) => { s.sink(it, path) }
        }
    }

    fn finalize<'w, 'a, 'k, It : Iterator<Item=WriteResource<'w, 'a, 'k>>>(&mut self, it: It) -> bool where 'a : 'w, 'k : 'w {
        match self {
            ASink::AddSink(s) => { s.finalize(it) }
            ASink::RemoveSink(s) => { s.finalize(it) }
            ASink::HeadSink(s) => { s.finalize(it) }
            ASink::CountSink(s) => { s.finalize(it) }
            ASink::SumSink(s) => { s.finalize(it) }
            ASink::ACTSink(s) => { s.finalize(it) }
            #[cfg(feature = "wasm")]
            ASink::WASMSink(s) => { s.finalize(it) }
            #[cfg(feature = "grounding")]
            ASink::PureSink(s) => { s.finalize(it) }
        }
    }
}
