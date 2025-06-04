
use reqwest::Error;

mod common;
use common::*;

#[tokio::test]
async fn metta_thread_basic_works_with_substitution() -> Result<(), Error> {
    decl_lit!{def_expr!()           => "(def $loc $step $p $t)"        }
    decl_lit!{in_expr!()             => "((metta_thread_basic in)  $v)"}
    decl_lit!{out_expr!()            => "((metta_thread_basic out) $v)"}
    decl_lit!{id_pattern_template!() => "$v"                           }

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", id_pattern_template!(),
        "/", in_expr!(),
    );
    const UPLOAD_PAYLOAD : &str = concat!(""
        , "\n(val a b)"
        , "\n(val c d)"
        , "\n(val e f)"
        , "\n(val g h)"
    );
    const UPLOAD_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", in_expr!(),
    );

    const DEF_UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", def_expr!(),
        "/", def_expr!(),
    );
    const DEF_UPLOAD_PAYLOAD : &str = concat!(""
    , "\n(def metta_thread_basic 0"
    , "\n     (, ((metta_thread_basic in) (val $x $y))"
    , "\n        (def metta_thread_basic 1 $p $t)"
    , "\n     )"
    , "\n     (, (exec ((metta_thread_basic state) \"cleanup\") (, (val $y $x)) (,))"
    , "\n        (exec (metta_thread_basic \"asap\") $p $t)"
    , "\n        ((metta_thread_basic out) (val $x $y))"
    , "\n     )"
    , "\n)"

    , "\n(def metta_thread_basic 1"
    , "\n     (, (exec ((metta_thread_basic state) $p) (, (val $u $v)) (,)) "
    , "\n     )"
    , "\n     (, ((metta_thread_basic out) (val $u $v))"
    , "\n     )"
    , "\n)"
    );
    const DEF_UPLOAD_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(def metta_thread_basic $step $p $t)",
    );

    const METTA_THREAD_RUNNER : &str = concat!(
        server_url!(),
        "/",  "metta_thread",
        "/" , "(exec ($t_id \"asap\")   (, (def $t_id 0 $p $t) )   (, (exec ($t_id \"asap\") $p $t) )   )",
        "/?", "location=metta_thread_basic"
    );
    const METTA_THREAD_RUNNER_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec metta_thread_basic)",
    );


    const METTA_THREAD_CLEAR_STATE : &str = concat!(
        server_url!(),
        "/", "metta_thread",
        "/", "(exec ($t_id \"asap\") (,) (,))",
        "/?", "location=(metta_thread_basic state)"
    );
    const METTA_THREAD_STATE_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec (metta_thread_basic state))",
    );

    const EXPORT_URL : &str = concat!(
        server_url!(),
        "/", "export",
        "/", out_expr!(),
        "/", id_pattern_template!(),
    );

    wait_for_server().await.unwrap();

    // upload vals
    let response = reqwest::Client::new().post(UPLOAD_URL).body(UPLOAD_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Upload response: {}", response.text().await.unwrap());


    // defs
    let response = reqwest::Client::new().post(DEF_UPLOAD_URL).body(DEF_UPLOAD_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Def Upload response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(UPLOAD_STATUS,      "pathClear").await.unwrap();
    wait_for_url_eq_status(DEF_UPLOAD_STATUS,  "pathClear").await.unwrap();

    // exec runner
    let response = reqwest::get(METTA_THREAD_RUNNER).await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Runner response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(METTA_THREAD_RUNNER_STATUS, "pathClear").await.unwrap();


    // exec state cleanup
    let response = reqwest::get(METTA_THREAD_CLEAR_STATE).await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Runner response: {}", response.text().await.unwrap());


    wait_for_url_eq_status(METTA_THREAD_STATE_STATUS, "pathClear").await.unwrap();


    tokio::time::sleep(core::time::Duration::from_millis(10)).await;
    // //////////
    // EXPORT //
    // ////////

    let export_response = reqwest::get(EXPORT_URL).await.unwrap();
    if !export_response.status().is_success() {
        panic!("Error response: {} - {}", export_response.status(), export_response.text().await.unwrap())
    }
    let export_response_text = export_response.text().await.unwrap();
    println!("Export response:\n{}", export_response_text);


    const OUT_LIST : &str = concat!(""
    , "(val a b)\n"
    , "(val b a)\n"
    , "(val c d)\n"
    , "(val d c)\n"
    , "(val e f)\n"
    , "(val f e)\n"
    , "(val g h)\n"
    , "(val h g)\n"
    );
    core::assert_eq!(
        OUT_LIST,
        export_response_text
    );

    Ok(())

}

#[tokio::test]
async fn metta_thread_basic_works_without_substitution() -> Result<(), Error> {
    decl_lit!{def_expr!()           => "(def $loc $step $p $t)"        }
    decl_lit!{exec_expr!()           => "(exec $loc $p $t)"            }
    decl_lit!{in_expr!()             => "((metta_thread_basic in)  $v)"}
    decl_lit!{out_expr!()            => "((metta_thread_basic out) $v)"}
    decl_lit!{id_pattern_template!() => "$v"                           }

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", id_pattern_template!(),
        "/", in_expr!(),
    );
    const UPLOAD_PAYLOAD : &str = concat!(""
        , "\n(val a b)"
        , "\n(val c d)"
        , "\n(val e f)"
        , "\n(val g h)"
    );
    const UPLOAD_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", in_expr!(),
    );

    const DEF_UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", def_expr!(),
        "/", def_expr!(),
    );
    const DEF_UPLOAD_PAYLOAD : &str = concat!(""
    , "\n(def metta_thread_basic 0"
    , "\n     (, ((metta_thread_basic in) (val $x $y))"
    , "\n        (def metta_thread_basic 1 $p $t)"
    , "\n     )"
    , "\n     (, (exec (metta_thread_basic state) (, (val $y $x)) (,))"
    , "\n        (exec metta_thread_basic $p $t)"
    , "\n        ((metta_thread_basic out) (val $x $y))"
    , "\n     )"
    , "\n)"

    , "\n(def metta_thread_basic 1"
    , "\n     (, (exec (metta_thread_basic state) (, (val $u $v)) (,)) "
    , "\n     )"
    , "\n     (, ((metta_thread_basic out) (val $u $v))"
    , "\n     )"
    , "\n)"
    );
    const DEF_UPLOAD_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(def metta_thread_basic $step $p $t)",
    );

    const EXEC_UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", exec_expr!(),
        "/", exec_expr!(),
    );
    const EXEC_UPLOAD_PAYLOAD : &str = concat!(""
    , "\n(exec metta_thread_basic (, (def metta_thread_basic 0 $p $t) )"
    , "\n                         (, (exec metta_thread_basic $p $t) )"
    , "\n)"
    );
    const EXEC_UPLOAD_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec metta_thread_basic)",
    );


    const METTA_THREAD_RUNNER : &str = concat!(
        server_url!(),
        "/", "metta_thread",
        "/", "metta_thread_basic"
    );
    const METTA_THREAD_RUNNER_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec metta_thread_basic)",
    );


    const METTA_THREAD_CLEAR_STATE : &str = concat!(
        server_url!(),
        "/", "metta_thread",
        "/", "(metta_thread_basic state)"
    );
    const METTA_THREAD_STATE_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec (metta_thread_basic state))",
    );

    const EXPORT_URL : &str = concat!(
        server_url!(),
        "/", "export",
        "/", out_expr!(),
        // "/", id_pattern_template!(), //dbg
        "/", id_pattern_template!(),
    );

    wait_for_server().await.unwrap();

    // upload vals
    let response = reqwest::Client::new().post(UPLOAD_URL).body(UPLOAD_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Upload response: {}", response.text().await.unwrap());


    // defs
    let response = reqwest::Client::new().post(DEF_UPLOAD_URL).body(DEF_UPLOAD_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Def Upload response: {}", response.text().await.unwrap());

    // upload exec
    let response = reqwest::Client::new().post(EXEC_UPLOAD_URL).body(EXEC_UPLOAD_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Upload response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(UPLOAD_STATUS,      "pathClear").await.unwrap();
    wait_for_url_eq_status(DEF_UPLOAD_STATUS,  "pathClear").await.unwrap();
    wait_for_url_eq_status(EXEC_UPLOAD_STATUS, "pathClear").await.unwrap();

    // exec runner
    let response = reqwest::get(METTA_THREAD_RUNNER).await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Runner response: {}", response.text().await.unwrap());

    // tokio::time::sleep(core::time::Duration::from_millis(5)).await;

    wait_for_url_eq_status(METTA_THREAD_RUNNER_STATUS, "pathClear").await.unwrap();


    // exec state cleanup
    let response = reqwest::get(METTA_THREAD_CLEAR_STATE).await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Runner response: {}", response.text().await.unwrap());


    wait_for_url_eq_status(METTA_THREAD_STATE_STATUS, "pathClear").await.unwrap();


    tokio::time::sleep(core::time::Duration::from_millis(10)).await;
    // //////////
    // EXPORT //
    // ////////

    let export_response = reqwest::get(EXPORT_URL).await.unwrap();
    if !export_response.status().is_success() {
        panic!("Error response: {} - {}", export_response.status(), export_response.text().await.unwrap())
    }
    let export_response_text = export_response.text().await.unwrap();
    println!("Export response:\n{}", export_response_text);


    const OUT_LIST : &str = concat!(""
    , "(val a b)\n"
    , "(val b a)\n"
    , "(val c d)\n"
    , "(val d c)\n"
    , "(val e f)\n"
    , "(val f e)\n"
    , "(val g h)\n"
    , "(val h g)\n"
    );
    core::assert_eq!(
        OUT_LIST,
        export_response_text
    );

    Ok(())

}
