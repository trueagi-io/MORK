use eval_ffi::{ExprSink, ExprSource, SinkItem, SourceItem, EvalError, Tag};

#[unsafe(no_mangle)]
pub extern "C" fn ground_mul(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"*")?;
    let mut result: i32 = 1;
    for _ in 0..items {
        let item = expr.consume_i32()?;
        result = result.checked_mul(item)
            .ok_or_else(|| EvalError::from("overflow in *"))?
    }
    sink.write(result.to_be_bytes()[..].into())?;
    Ok(())
}

#[unsafe(no_mangle)]
pub extern "C" fn ground_sum(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"+")?;
    let mut result: i32 = 0;
    for _ in 0..items {
        let item = expr.consume_i32()?;
        result = result.checked_add(item)
            .ok_or_else(|| EvalError::from("overflow in +"))?
    }
    sink.write(result.to_be_bytes()[..].into())?;
    Ok(())
}
