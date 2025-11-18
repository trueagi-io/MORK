use mork_expr::{maybe_byte_item, construct, Tag, Expr, ExprZipper};
use std::collections::HashMap;

type EvalError = String;
type FuncPtr = fn(Expr, &mut ExprZipper) -> Result<(), EvalError>;
enum FuncType { Macro, Pure }
struct Func {
    func: FuncPtr,
    ty: FuncType,
}

struct StackFrame {
    sink: ExprZipper,
    rest: usize,
    expr: Expr,
}

struct EvalScope {
    fns: HashMap<Vec<u8>, Func>,
    stack: Vec<StackFrame>,
    expr: Expr,
    bufs: Vec<Vec<u8>>,
}
const EXPR_SIZE: usize = 1024 * 1024;
impl EvalScope {
    pub fn new() -> Self {
        Self {
            fns: HashMap::new(),
            stack: Vec::new(),
            bufs: Vec::new(),
            expr: Expr { ptr: core::ptr::null_mut() },
        }
    }
    pub fn add_func(&mut self, name: &str, func: FuncPtr, ty: FuncType) {
        self.fns.insert(name.as_bytes().to_vec(), Func { func, ty });
    }
    fn eval(&mut self, expr: Expr) -> Result<Vec<u8>, EvalError> {
        self.stack.clear();
        self.bufs.clear();
        let mut sink_buf = vec![0_u8; EXPR_SIZE];
        let ptr = sink_buf.as_mut_ptr();
        let sink = ExprZipper::new( Expr { ptr } );
        self.bufs.push(sink_buf);
        self.stack.push(StackFrame { sink, rest: 1, expr: expr });
        self.push_eval()?;
        self.eval_impl()?;
        let mut rv = core::mem::take(&mut self.bufs[0]);
        rv.truncate(self.stack[0].sink.loc);
        Ok(rv)
    }
    fn push_eval(&mut self) -> Result<(), EvalError> {
        let expr = self.stack.last().unwrap().expr;
        // take current expr item, and push a new frame to evaluate it.
        match maybe_byte_item(unsafe { *expr.ptr }) {
            Ok(Tag::Arity(arity)) => {
                // let mut expr2 = expr;
                // let is_macros =
                //     if let Ok((_items, fun)) = consume_head(&mut expr2) {
                //         matches!(self.fns.get(fun).map(|f| &f.ty), Some(FuncType::Macro))
                //     } else {
                //         false
                //     };
                // function application
                while self.stack.len() >= self.bufs.len() {
                    self.bufs.push(vec![0_u8; EXPR_SIZE]);
                }
                let ptr = self.bufs.last_mut().unwrap().as_mut_ptr();
                let mut frame = StackFrame {
                    sink: ExprZipper::new(Expr { ptr }),
                    rest: arity as usize,
                    expr: Expr { ptr: unsafe { expr.ptr.add(1) } },
                };
                frame.sink.write_arity(arity);
                frame.sink.loc += 1;
                self.stack.push(frame);
            }
            Ok(Tag::SymbolSize(len)) => {
                let top_frame = self.stack.last_mut().unwrap();
                // symbol
                let symbol = unsafe { std::slice::from_raw_parts(expr.ptr.add(1), len as usize) };
                top_frame.expr.ptr = unsafe { expr.ptr.add(1 + len as usize) };
                top_frame.sink.write_symbol(symbol);
                top_frame.sink.loc += 1 + len as usize;
            }
            _ => return Err(format!("not a list"))
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
                let mut expr = Expr { ptr: top_frame.sink.root.ptr };
                // eprintln!("top frame done, expr: {:?}", expr.ptr);
                let (_items, fn_name) = consume_head(&mut expr)?;
                let func = self.fns.get(fn_name)
                    .ok_or_else(|| format!("unknown function: {:?}", String::from_utf8_lossy(fn_name)))?;
                (func.func)(Expr { ptr: top_frame.sink.root.ptr }, &mut prev_frame.sink)?;
                let slice = unsafe { std::slice::from_raw_parts(prev_frame.sink.root.ptr, 16) };
                // eprintln!("after func call, parent frame slice: {:?} loc: {}", slice, prev_frame.sink.loc);
                self.stack.pop();
                continue;
            }
            // otherwise, evaluate the next item in the top frame.
            self.push_eval()?;
            self.stack[idx].rest -= 1;
        }
        Ok(())
    }
}

fn consume_head(expr: &mut Expr) -> Result<(usize, &[u8]), EvalError> {
    // TODO(igorm): ExprZipper is likely better for these kinds of manipulations,
    // instead of manual pointer operations. just getting this to work.
    let mut ptr = expr.ptr;
    let mut items;
    match maybe_byte_item(unsafe { *ptr }) {
        Ok(Tag::Arity(arity)) => {
            ptr = unsafe { ptr.add(1) };
            items = arity as usize;
        }
        _ => return Err(format!("not a list2"))
    }
    let head;
    match maybe_byte_item(unsafe { *ptr }) {
        Ok(Tag::SymbolSize(len)) => {
            head = unsafe { std::slice::from_raw_parts(ptr.add(1), len as usize) };
            ptr = unsafe { ptr.add(1 + len as usize) };
            items -= 1;
        }
        _ => return Err(format!("head is not a symbol")),
    }
    expr.ptr = ptr;
    Ok((items, head))
}

fn consume_head_ck(expr: &mut Expr, symbol: &[u8]) -> Result<usize, EvalError> {
    let mut expr2 = Expr { ptr: expr.ptr };
    let (items, head) = consume_head(&mut expr2)?;
    if head != symbol {
        return Err(format!("incorrect symbol provided, expected: {symbol:?}, got: {head:?}"));
    }
    expr.ptr = expr2.ptr;

    Ok(items)
}

fn consume_i32(mut expr: &mut Expr) -> Result<i32, EvalError> {
    let mut ptr = expr.ptr;
    let array;
    const SIZE: usize = core::mem::size_of::<i32>();
    match maybe_byte_item(unsafe { *ptr }) {
        Ok(Tag::SymbolSize(len)) if len as usize == SIZE => {
            array = unsafe { ptr.add(1).cast::<[u8; SIZE]>().read() };
            ptr = unsafe { ptr.add(1 + SIZE) };
        }
        Ok(Tag::SymbolSize(len)) => {
            return Err(format!("invalid symbol size of i32: {len}"));
        }
        _ => return Err(format!("trying to read i32 from not a symbol"))
    }
    expr.ptr = ptr;
    Ok(i32::from_be_bytes(array))
}

fn ground_mul(mut expr: Expr, sink: &mut ExprZipper) -> Result<(), EvalError> {
    let items = consume_head_ck(&mut expr, b"*")?;
    let mut result: i32 = 1;
    for _ in 0..items {
        let item = consume_i32(&mut expr)?;
        result = result.checked_mul(item)
            .ok_or_else(|| format!("overflow in *"))?
    }
    sink.write_symbol(&result.to_be_bytes());
    sink.loc += core::mem::size_of::<i32>();
    Ok(())
}

fn ground_sum(mut expr: Expr, sink: &mut ExprZipper) -> Result<(), EvalError> {
    let items = consume_head_ck(&mut expr, b"+")?;
    let mut result: i32 = 0;
    for _ in 0..items {
        let item = consume_i32(&mut expr)?;
        result = result.checked_add(item)
            .ok_or_else(|| format!("overflow in +"))?
    }
    sink.write_symbol(&result.to_be_bytes());
    sink.loc += core::mem::size_of::<i32>();
    Ok(())
}

fn main() {
    /*
    let mut buf = vec![0_u8; 5];
    let mut sink = ExprZipper::new( Expr { ptr: buf.as_mut_ptr() } );
    let mut expr = construct!("*" 3_i32 4_i32).unwrap();
    eprintln!("{expr:?}");
    ground_mul(Expr { ptr: expr.as_mut_ptr() }, &mut sink).unwrap();
    eprintln!("{buf:?}");
    */
    let mut scope = EvalScope::new();
    scope.add_func("+", ground_sum, FuncType::Pure);
    scope.add_func("*", ground_mul, FuncType::Pure);
    let mut expr = construct!("+" 2 ("*" 3 4)).unwrap();
    // let mut expr = construct!("+" 42 69).unwrap();
    let expr = Expr { ptr: expr.as_mut_ptr() };
    println!("{:?}", expr);
    let mut rv = scope.eval(expr).unwrap();
    let result = consume_i32(&mut Expr { ptr: rv.as_mut_ptr() }).unwrap();
    println!("result: {}", result);
}
