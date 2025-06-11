
use reqwest::Error;

mod common;
use common::*;


#[tokio::test]
async fn metta_thread_without_substitution_adams_hello_world() -> Result<(), Error> {
    decl_lit!{in_expr!()  => "(adams_hw_data $v)"}
    decl_lit!{out_expr!() => "(data $v)"         }
    decl_lit!{data!()     => "adams_hw_data"     }

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", in_expr!(),
        "/", in_expr!(),
    );
    const UPLOAD_PAYLOAD : &str = concat!(""
    , "\n(",data!()," T)"
    , "\n(",data!()," (foo 1))"
    , "\n(",data!()," (foo 2))"
    );
    const UPLOAD_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", in_expr!(),
    );


    const METTA_UPLOAD_EXECS : &str =concat!(""
    , "\n(exec (",data!()," 0)   (, (",data!()," (foo $x)))   (, (",data!()," (bar $x)) )   )"
    , "\n(exec (",data!()," 0)   (, (",data!()," T))          (, (",data!()," ran_exec) )   )" // this won't write anything unless empty pattern always accepts
    );
    const METTA_UPLOAD_EXECS_URL : &str =concat!(
        server_url!(),
        "/", "upload",
        "/", "(exec $l_p $patterns $templates)",
        "/", "(exec $l_p $patterns $templates)",
    );

    const METTA_EXEC_UPLOAD_STATUS: &str = concat!(
        server_url!(),
        "/", "status",
        "/", "(exec (",data!()," $priority) $p $t)",
    );



    const METTA_THREAD_RUNNER : &str = concat!(
        server_url!(),
        "/",  "metta_thread",
        "/?", "location=",data!()
    );
    const METTA_THREAD_RUNNER_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec ",data!(),")",
    );

    const EXPORT_URL : &str = concat!(
        server_url!(),
        "/", "export",
        "/", in_expr!(),
        "/", out_expr!(),
    );

    wait_for_server().await.unwrap();

    // upload vals
    let response = reqwest::Client::new().post(UPLOAD_URL).body(UPLOAD_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Upload response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(UPLOAD_STATUS,      "pathClear").await.unwrap();

    // execs
    let response = reqwest::Client::new().post(METTA_UPLOAD_EXECS_URL).body(METTA_UPLOAD_EXECS).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Upload response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(UPLOAD_STATUS,      "pathClear").await.unwrap();
    wait_for_url_eq_status(METTA_EXEC_UPLOAD_STATUS,  "pathClear").await.unwrap();


    // exec runner
    let response = reqwest::get(METTA_THREAD_RUNNER).await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Runner response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(METTA_THREAD_RUNNER_STATUS, "pathClear").await.unwrap();


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
    , "(data T)\n"
    , "(data ran_exec)\n"
    , "(data (foo 1))\n"
    , "(data (foo 2))\n"
    , "(data (bar 1))\n"
    , "(data (bar 2))\n"
    );
    core::assert_eq!(export_response_text.lines().count(), 6);

    //GOAT, this is a hack until we have symbol-order-independent validation
    const OUT_LIST_ALTERNATE : &str = concat!(""
    , "(data T)\n"
    , "(data ran_exec)\n"
    , "(data (bar 1))\n"
    , "(data (bar 2))\n"
    , "(data (foo 1))\n"
    , "(data (foo 2))\n"
    );

    assert!(export_response_text==OUT_LIST || export_response_text==OUT_LIST_ALTERNATE);

    Ok(())

}

#[tokio::test]
async fn metta_thread_without_substitution_self_reference() -> Result<(), Error> {
    decl_lit!{out_read_expr!()  => "(metta_thread_without_substitution_self_reference $v)"}
    decl_lit!{out_write_expr!() => "(self_reference $v)"         }
    decl_lit!{thread_id!()      => "metta_thread_without_substitution_self_reference"     }

    const METTA_UPLOAD_EXECS : &str =concat!(""
    , "\n(exec (",thread_id!()," 0)   (, (exec (",thread_id!()," 0) $t $p)) (, (",thread_id!()," ran_exec) )   )"
    );
    const METTA_UPLOAD_EXECS_URL : &str =concat!(
        server_url!(),
        "/", "upload",
        "/", "(exec $l_p $patterns $templates)",
        "/", "(exec $l_p $patterns $templates)",
    );
    const METTA_EXEC_UPLOAD_STATUS: &str = concat!(
        server_url!(),
        "/", "status",
        "/", "(exec (",thread_id!()," $priority) $p $t)",
    );



    const METTA_THREAD_RUNNER : &str = concat!(
        server_url!(),
        "/",  "metta_thread",
        "/?", "location=",thread_id!()
    );
    const METTA_THREAD_RUNNER_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec ",thread_id!(),")",
    );

    const EXPORT_URL : &str = concat!(
        server_url!(),
        "/", "export",
        "/", out_read_expr!(),
        "/", out_write_expr!(),
    );

    wait_for_server().await.unwrap();

    // execs
    let response = reqwest::Client::new().post(METTA_UPLOAD_EXECS_URL).body(METTA_UPLOAD_EXECS).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Upload response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(METTA_EXEC_UPLOAD_STATUS,  "pathClear").await.unwrap();

    // exec runner
    let response = reqwest::get(METTA_THREAD_RUNNER).await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Runner response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(METTA_THREAD_RUNNER_STATUS, "pathClear").await.unwrap();


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
    , "(self_reference ran_exec)\n"
    );
    core::assert_eq!(
        OUT_LIST,
        export_response_text
    );

    Ok(())

}

#[tokio::test]
async fn metta_thread_basic_works_without_substitution() -> Result<(), Error> {
    decl_lit!{def_expr!()            => "(def $loc $step $p $t)"       }
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

    const METTA_UPLOAD_INITIAL_EXEC : &str =concat!(""
    , "\n(exec (metta_thread_basic \"asap\")   (, (def metta_thread_basic 0 $p $t) )   (, (exec (metta_thread_basic \"asap\") $p $t) )   )"
    );
    const METTA_UPLOAD_INITIAL_EXEC_URL : &str =concat!(
        server_url!(),
        "/", "upload",
        "/", "(exec ($thread $priority) $patterns $templates)",
        "/", "(exec ($thread $priority) $patterns $templates)",
    );
        const METTA_EXEC_UPLOAD_STATUS: &str = concat!( 
        server_url!(),
        "/", "status",
        "/", "(exec (metta_thread_basic $priority) $p $t)",
    );

    const METTA_THREAD_RUNNER : &str = concat!(
        server_url!(),
        "/",  "metta_thread",
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

    // execs
    let response = reqwest::Client::new().post(METTA_UPLOAD_INITIAL_EXEC_URL).body(METTA_UPLOAD_INITIAL_EXEC).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await.unwrap())
    }
    println!("Exec Upload response: {}", response.text().await.unwrap());

    wait_for_url_eq_status(UPLOAD_STATUS,      "pathClear").await.unwrap();
    wait_for_url_eq_status(DEF_UPLOAD_STATUS,  "pathClear").await.unwrap();
    wait_for_url_eq_status(METTA_EXEC_UPLOAD_STATUS,  "pathClear").await.unwrap();

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
    core::assert_eq!(export_response_text.lines().count(), 8);
    core::assert_eq!(
        OUT_LIST,
        export_response_text
    );

    Ok(())

}