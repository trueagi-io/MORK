#![feature(coroutine_trait)]
#![feature(coroutines)]

use mork_expr::{construct};

use std::pin::Pin;
use std::ops::{Coroutine, CoroutineState, ControlFlow};
use std::convert::Infallible;
use std::collections::HashMap;

use eval_ffi::{EvalError, ExprSink, SinkItem, ExprSource, SourceItem, FuncPtr, Tag};

struct StackFrame {
    sink: ExprSink,
    // sink: SinkCoro,
    rest: usize,
    expr: ExprSource,
}

enum FuncType { Macro, Pure }

struct Func {
    func: FuncPtr,
    ty: FuncType,
}

struct EvalScope {
    fns: HashMap<Vec<u8>, Func>,
    stack: Vec<StackFrame>,
    // expr: SrcCoro<'a>,
    // expr: Expr,
    bufs: Vec<Vec<u8>>,
}

const EXPR_SIZE: usize = 1024 * 1024;
impl EvalScope {
    pub fn new() -> Self {
        Self {
            fns: HashMap::new(),
            stack: Vec::new(),
            bufs: Vec::new(),
            // expr: Expr { ptr: core::ptr::null_mut() },
        }
    }
    pub fn add_func(&mut self, name: &str, func: FuncPtr, ty: FuncType) {
        self.fns.insert(name.as_bytes().to_vec(), Func { func, ty });
    }
    fn eval(&mut self, expr: ExprSource) -> Result<Vec<u8>, EvalError> {
        self.stack.clear();
        self.bufs.clear();
        let sink = ExprSink::new(Vec::with_capacity(EXPR_SIZE));
        self.stack.push(StackFrame { sink, rest: 1, expr: expr });
        self.push_eval()?;
        self.eval_impl()?;
        let top = self.stack.pop().unwrap();
        let rv = top.sink.finish();
        Ok(rv)
    }
    fn push_eval(&mut self) -> Result<(), EvalError> {
        let mut expr = self.stack.last().unwrap().expr.clone();
        // take current expr item, and push a new frame to evaluate it.
        match expr.read() {
            SourceItem::Tag(Tag::Arity(arity)) => {
                let buf = self.bufs.pop().unwrap_or_else(||
                    Vec::with_capacity(EXPR_SIZE));
                let mut frame = StackFrame {
                    sink: ExprSink::new(buf),
                    rest: arity as usize,
                    expr: expr.clone(),
                };
                frame.sink.write(SinkItem::Tag(Tag::Arity(arity)))?;
                self.stack.push(frame);
            }
            SourceItem::Symbol(symbol) => {
                let top_frame = self.stack.last_mut().unwrap();
                top_frame.sink.write(SinkItem::from(symbol))?;
                top_frame.expr = expr.clone();
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
                self.bufs.push(data);
                continue;
            }
            self.push_eval()?;
            self.stack[idx].rest -= 1;
        }
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut scope = EvalScope::new();
    unsafe {
        // build the dynamically loaded library
        std::process::Command::new("cargo")
            .args(&["build", "--release", "-p", "eval-examples"])
            .status()
            .expect("failed to build eval-examples");

        #[cfg(target_os = "macos")]
        const LIB_SUFFIX: &str = ".dylib";
        #[cfg(target_os = "linux")]
        const LIB_SUFFIX: &str = ".so";
        #[cfg(target_os = "windows")]
        const LIB_SUFFIX: &str = ".dll";

        let lib_path = format!("../../target/release/libeval_examples{}", LIB_SUFFIX);
        let lib = libloading::Library::new(lib_path)?;

        let ground_sum: libloading::Symbol<FuncPtr> = lib.get(b"ground_sum")?;
        scope.add_func("+", *ground_sum, FuncType::Pure);
        let ground_mul: libloading::Symbol<FuncPtr> = lib.get(b"ground_mul")?;
        scope.add_func("*", *ground_mul, FuncType::Pure);
    }
    let mut expr = construct!("+" 2 ("*" 3 4)).unwrap();
    // let mut expr = construct!("+" 42 69).unwrap();
    let expr = ExprSource::new(expr.as_ptr());
    println!("{}", expr.print());
    let mut rv = scope.eval(expr).unwrap();
    let mut rv = ExprSource::new(rv.as_ptr());
    let result = rv.consume_i32().unwrap();
    println!("result: {}", result);
    Ok(())
}
