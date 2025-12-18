#![feature(coroutine_trait)]
#![feature(coroutines)]

use eval::{EvalScope, FuncType};
use mork_expr::{construct};

use std::pin::Pin;
use std::ops::{Coroutine, CoroutineState, ControlFlow};
use std::convert::Infallible;
use std::collections::HashMap;

use eval_ffi::{EvalError, ExprSink, SinkItem, ExprSource, SourceItem, FuncPtr, Tag};

mod alloc;


fn main() -> Result<(), Box<dyn std::error::Error>> {
    const TRACE_ALLOC: bool = false;
    let _ = tracking_allocator::AllocationRegistry::set_global_tracker(alloc::StdoutTracker)
        .expect("no other global tracker should be set yet");
    if TRACE_ALLOC {
        tracking_allocator::AllocationRegistry::enable_tracking();
    }
    let mut local_token =
        tracking_allocator::AllocationGroupToken::register()
        .expect("failed to register allocation group");


    let mut scope = EvalScope::new();
    let lib;
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

        use std::path::PathBuf;
        let target_dir = format!("{}/{}",
            env!("CARGO_MANIFEST_DIR"),
            "../../target/release",
        );
        let lib_path = format!("{target_dir}/libeval_examples{LIB_SUFFIX}");
        lib = libloading::Library::new(lib_path)?;

        let ground_sum: libloading::Symbol<FuncPtr> = lib.get(b"ground_sum")?;
        scope.add_func("+", *ground_sum, FuncType::Pure);
        let ground_mul: libloading::Symbol<FuncPtr> = lib.get(b"ground_mul")?;
        scope.add_func("*", *ground_mul, FuncType::Pure);
    }

    // Now, get an allocation guard from our token.  This guard ensures the allocation group is marked as the current
    // allocation group, so that our allocations are properly associated.
    let local_guard = local_token.enter();

    let mut expr = construct!("+" ("*" 1 2) ("*" 3 4)).unwrap();
    // let mut expr = construct!("+" 42 69).unwrap();
    // println!("{}", expr.print());
    println!("eval...");
    let expr_src = ExprSource::new(expr.as_ptr());
    let mut rv_buf = scope.eval(expr_src).unwrap();
    let mut rv_expr = ExprSource::new(rv_buf.as_ptr());
    let result = rv_expr.consume_i32().unwrap();
    println!("result: {}", result);
    drop(rv_expr);
    scope.return_alloc(rv_buf);
    println!("eval...");
    let expr_src = ExprSource::new(expr.as_ptr());
    let mut rv_buf = scope.eval(expr_src).unwrap();
    let mut rv_expr = ExprSource::new(rv_buf.as_ptr());
    println!("result: {}", result);
    drop(rv_expr);
    scope.return_alloc(rv_buf);
    drop(local_guard);

    Ok(())
}
