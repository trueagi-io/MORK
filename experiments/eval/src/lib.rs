#![feature(coroutine_trait)]
#![feature(coroutines)]

use std::collections::HashMap;
use std::ops::{Coroutine, CoroutineState};
use mork_expr::{item_source, SourceItem};
use eval_ffi::{EvalError, ExprSink, ExprSource, FuncPtr, Tag};
use log::trace;

extern "C" fn nothing(src: *mut ExprSource, snk: *mut ExprSink) -> Result<(), EvalError> {
    Ok(())
}

extern "C" fn quote(src: *mut ExprSource, snk: *mut ExprSink) -> Result<(), EvalError> {
    unreachable!()
}

pub struct StackFrame {
    sink: ExprSink,
    // sink: SinkCoro,
    rest: usize,
    func: FuncPtr
}

pub enum FuncType { Macro, Pure }

pub struct Func {
    func: FuncPtr,
    ty: FuncType,
}

pub struct EvalScope {
    fns: HashMap<Vec<u8>, Func>,
    expr: ExprSource,
    stack: Vec<StackFrame>,
    /// Re-used buffer allocation pool.
    /// These are used to create ExprSinks for stack frames.
    /// This avoids repeated allocations during evaluation.
    alloc_pool: Vec<Vec<u8>>,
}

macro_rules! alloc {
    (get $es:ident) => {
        if let Some(mut rv) = $es.alloc_pool.pop() { rv.clear(); rv } else { Vec::with_capacity(EXPR_SIZE) }
    };
    (ret $es:ident $buf:ident) => {
        $buf.clear();
        self.alloc_pool.push($buf);
    };
}

const EXPR_SIZE: usize = 1024 * 1024;
impl EvalScope {
    pub fn new() -> Self {
        let mut hm = HashMap::new();
        hm.insert(b"'".to_vec(), Func{ func: quote, ty: FuncType::Pure });
        Self {
            fns: hm,
            stack: Vec::new(),
            alloc_pool: Vec::new(),
            expr: ExprSource::new(core::ptr::null()),
        }
    }
    pub fn add_func(&mut self, name: &str, func: FuncPtr, ty: FuncType) {
        self.fns.insert(name.as_bytes().to_vec(), Func { func, ty });
    }
    #[inline]
    fn get_alloc(&mut self) -> Vec<u8> {
        if let Some(mut rv) = self.alloc_pool.pop() {
            rv.clear();
            return rv;
        }
        Vec::with_capacity(EXPR_SIZE)
    }
    #[inline]
    pub fn return_alloc(&mut self, mut buf: Vec<u8>) {
        buf.clear();
        self.alloc_pool.push(buf);
    }
    pub fn eval(&mut self, expr: ExprSource) -> Result<Vec<u8>, EvalError> {
        self.expr = expr;
        self.stack.clear();
        // self.alloc_pool.clear();
        let sink = ExprSink::new(self.get_alloc());
        self.stack.push(StackFrame { sink, rest: 1, func: nothing });
        self.push_eval()?;
        self.eval_impl()?;
        let top = self.stack.pop().unwrap();
        let rv = top.sink.finish();
        Ok(rv)
    }
    fn push_eval(&mut self) -> Result<(), EvalError> {
        // take current expr item, and push a new frame to evaluate it.
        match self.expr.read() {
            SourceItem::Tag(Tag::Arity(arity)) => {
                let SourceItem::Symbol(fn_name) = self.expr.read() else { return Err(EvalError::from("expected function symbol on the left")) };
                let func = self.fns.get(fn_name).ok_or_else(|| {
                    trace!(target: "pure", "{:?} not in function registry", std::str::from_utf8(fn_name));
                    "unknown function"
                })?.func;
                if func == quote {
                    let top_frame = self.stack.last_mut().unwrap();
                    let e = mork_expr::Expr { ptr: unsafe { self.expr.ptr.cast_mut().add(self.expr.position) } };
                    let mut src = item_source(e);
                    while let CoroutineState::Yielded(i) = std::pin::pin!(&mut src).resume(()) {
                        top_frame.sink.write(i)?;
                    }
                } else {
                    let mut frame = StackFrame {
                        // yes this is just get_alloc but Rust is stupid
                        sink: ExprSink::new(if let Some(mut rv) = self.alloc_pool.pop() { rv.clear(); rv } else { Vec::with_capacity(EXPR_SIZE) }),
                        rest: arity as usize - 1,
                        func: func
                    };
                    frame.sink.write(SourceItem::Tag(Tag::Arity(arity)))?;
                    frame.sink.write(SourceItem::Symbol(fn_name))?;
                    self.stack.push(frame);
                }
            }
            SourceItem::Symbol(symbol) => {
                let top_frame = self.stack.last_mut().unwrap();
                top_frame.sink.write(SourceItem::Symbol(symbol))?;
            }
            _ => return Err(EvalError::from("not a list")),
        }
        Ok(())
    }
    fn eval_impl(&mut self) -> Result<(), EvalError> {
        // evaluation process:
        // stack frames contain expressions to evaluate into sinks.
        while self.stack.len() > 1 {
            let (top_frame, parent_frames) = self.stack.split_last_mut().unwrap();
            let idx = parent_frames.len();
            // if the top frame is done, move its result into the parent frame.
            if top_frame.rest == 0 {
                let prev_frame = parent_frames.last_mut().unwrap();
                let mut data = core::mem::take(&mut top_frame.sink).finish();
                let offset = prev_frame.sink.as_ref().len();
                (top_frame.func)(&mut ExprSource::new(data.as_ptr()), &mut prev_frame.sink)?;
                trace!(target: "eval", "{:?} ==> {:?}", mork_expr::serialize(&data[..]), mork_expr::serialize(&prev_frame.sink.as_ref()[offset..]));
                let top = self.stack.pop().unwrap();
                // return buffer to pool
                self.return_alloc(data);
                continue;
            }
            self.push_eval()?;
            self.stack[idx].rest -= 1;
        }
        Ok(())
    }
}
