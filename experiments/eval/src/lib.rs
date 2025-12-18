#![feature(coroutine_trait)]
#![feature(coroutines)]

use std::collections::HashMap;

use eval_ffi::{EvalError, ExprSink, SinkItem, ExprSource, SourceItem, FuncPtr, Tag};

pub struct StackFrame {
    sink: ExprSink,
    // sink: SinkCoro,
    rest: usize,
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

const EXPR_SIZE: usize = 1024 * 1024;
impl EvalScope {
    pub fn new() -> Self {
        Self {
            fns: HashMap::new(),
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
        self.stack.push(StackFrame { sink, rest: 1 });
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
                let mut frame = StackFrame {
                    sink: ExprSink::new(self.get_alloc()),
                    rest: arity as usize,
                };
                frame.sink.write(SinkItem::Tag(Tag::Arity(arity)))?;
                self.stack.push(frame);
            }
            SourceItem::Symbol(symbol) => {
                let top_frame = self.stack.last_mut().unwrap();
                top_frame.sink.write(SinkItem::from(symbol))?;
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
                let mut expr = ExprSource::new(data.as_ptr());
                // eprintln!("top frame done, expr: {:?}", data);
                let (_items, fn_name) = expr.consume_head()?;
                let func = self.fns.get(fn_name)
                    .ok_or_else(|| "unknown function")?;
                (func.func)(&mut ExprSource::new(data.as_ptr()), &mut prev_frame.sink)?;
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
