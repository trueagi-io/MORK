
use std::{time::{Duration, Instant}};
use tokio::task;
use reqwest::{Client, Error};
use eventsource_stream::Eventsource;
use tokio_stream::StreamExt;

mod common;
use common::*;

/// Opens one client request
#[tokio::test]
async fn simple_request_test() -> Result<(), Error> {
    const URL: &str = concat!(
        server_url!(),
        "/", "busywait",
        "/", "2000",
    );
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(100)).await;

    let response = reqwest::get(URL).await?;

    if response.status().is_success() {
        let body = response.text().await?;
        println!("Response: {}", body);
    } else {
        println!("Failed to load page: {}", response.status());
    }

    Ok(())
}

/// Tests map access contention using the busywait command
#[tokio::test]
async fn busywait_contention_test() -> Result<(), Error> {
    decl_lit!{top_expr!() => "(busywait_contention_test $v)"}

    const TOP_READER: &str = concat!(
        server_url!(),
        "/", "busywait",
        "/", "500",
        "/?", "expr1=", top_expr!()
    );
    const TOP_WRITER: &str = concat!(
        server_url!(),
        "/", "busywait",
        "/", "500",
        "/?", "expr1=", top_expr!(),
        "&", "writer1"
    );
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(800)).await;

    //Take a reader
    let response = reqwest::get(TOP_READER).await?;
    if response.status().is_success() {
        let body = response.text().await?;
        println!("Response, first top-reader: {}", body);
    } else {
        panic!("Failed to take top-reader: {}", response.status());
    }
    tokio::time::sleep(Duration::from_millis(10)).await; //Just to make sure they don't land in the wrong order

    //Make sure we can't take a writer to the same path
    let response = reqwest::get(TOP_WRITER).await?;
    if response.status().is_success() {
        panic!("Should not be allowed to get top-writer with top-reader outstanding: {}", response.status());
    } else {
        println!("Failed to take top-writer, which is correct: {}", response.status());
    }

    //Now make sure we can take a reader
    let response = reqwest::get(TOP_READER).await?;
    if response.status().is_success() {
        let body = response.text().await?;
        println!("Response, sucessful second top-reader: {}", body);
    } else {
        panic!("Failed to second take top-reader: {}", response.status());
    }

    Ok(())
}

/// Opens many client requests at the same time, saturating the server's capacity very quickly
///
/// Ignored because it interferes with other tests
#[ignore]
#[tokio::test]
async fn many_request_instant_test() -> Result<(), Error> {
    const URL: &str = concat!(
        server_url!(),
        "/", "busywait",
        "/", "2000",
    );
    const NUM_REQUESTS: usize = 100;
    wait_for_server().await.unwrap();

    let client = Client::new();
    let mut handles = vec![];
    let start = Instant::now();

    for _ in 0..NUM_REQUESTS {

        // Spawn an async task for each request
        let client = client.clone();
        let handle = task::spawn(async move {
            match client.get(URL).send().await {
                Ok(response) => {
                    let status = response.status();
                    println!("Response received with status: {}", status);
                }
                Err(err) => {
                    println!("Request failed: {:?}", err);
                }
            }
        });

        handles.push(handle);
    }

    // Wait for all tasks to complete
    for handle in handles {
        let _ = handle.await;
    }

    let duration = start.elapsed();
    println!("Completed {} requests in {:?}", NUM_REQUESTS, duration);

    Ok(())
}

/// Opens many client requests with a short delay between each to simulate high load conditions
/// Tests that some proportion of the queries are rejected because the server is busy
///
/// Ignored because it was interfering with the other tests running simultaneously
#[ignore]
#[tokio::test]
async fn many_request_delayed_test() -> Result<(), Error> {
    const URL: &str = concat!(
        server_url!(),
        "/", "busywait",
        "/", "2000",
    );
    const NUM_REQUESTS: usize = 100;
    wait_for_server().await.unwrap();

    let delay = core::time::Duration::from_millis(100);

    let mut handles = vec![];
    let client = Client::new();

    for _ in 0..NUM_REQUESTS {

        // Spawn an async task for each request
        let client = client.clone();
        let handle = task::spawn(async move {
            let start = Instant::now();
            match client.get(URL).send().await {
                Ok(response) => {
                    let status = response.status();
                    println!("Response received with status: {} - {:?} elapsed", status, start.elapsed());
                }
                Err(err) => {
                    println!("Request failed: {:?} - {:?} elapsed", err, start.elapsed());
                }
            }
        });
        handles.push(handle);

        tokio::time::sleep(delay).await;
    }

    // Wait for all tasks to complete
    for handle in handles {
        let _ = handle.await;
    }

    Ok(())
}

/// Saturates the workers and then issues a stop request, and ensures no more connections are received
/// Also tests that the stop request can get through even if the server is under heavy load
///
/// This test must be run explicitly so it doesn't interfere with the other tests
#[ignore]
#[tokio::test]
async fn zzz_stop_request_test() -> Result<(), Error> {
    const URL: &str = concat!(
        server_url!(),
        "/", "busywait",
        "/", "2000",
    );
    const STOP_URL: &str = concat!(
        server_url!(),
        "/", "stop",
    );
    const NUM_REQUESTS: usize = 100;
    wait_for_server().await.unwrap();

    let delay_between_requests = core::time::Duration::from_millis(1);
    let delay_after_stop = core::time::Duration::from_millis(10);

    let mut handles = vec![];
    let client = Client::new();

    for _ in 0..NUM_REQUESTS {

        // Spawn an async task for each request
        let client = client.clone();
        let handle = task::spawn(async move {
            let _start = Instant::now();
            match client.get(URL).send().await {
                Ok(_response) => {
                    // let _status = _response.status();
                    // println!("Response received with status: {} - {:?} elapsed", _status, _start.elapsed());
                }
                Err(_err) => {
                    // println!("Request failed: {:?} - {:?} elapsed", _err, _start.elapsed());
                }
            }
        });
        handles.push(handle);

        tokio::time::sleep(delay_between_requests).await;
    }

    //Send the stop
    let client_clone = client.clone();
    task::spawn(async move {
        let _start = Instant::now();
        match client_clone.get(STOP_URL).send().await {
            Ok(response) => {
                let _status = response.status();
                println!("Response to stop received with status: {} - {:?} elapsed", _status, _start.elapsed());
            }
            Err(err) => {
                panic!("Request failed: {:?} - {:?} elapsed", err, _start.elapsed())
            }
        }
    });

    // Wait for all tasks to complete
    for handle in handles {
        let _ = handle.await;
    }

    //Give the server a chance to close
    tokio::time::sleep(delay_after_stop).await;

    //Check to make sure connections are now rejected
    let _ = task::spawn(async move {
        let _start = Instant::now();
        match client.get(URL).send().await {
            Ok(_response) => {
                panic!() //Server should no longer be listening
            }
            Err(_err) => {
                println!("Request failed, as it should!\n{:?} - {:?} elapsed", _err, _start.elapsed());
            }
        }
    }).await;

    Ok(())
}

/// Tests the `status_listen` endpoint
#[tokio::test]
async fn simple_listen_request_test() -> Result<(), Error> {
    decl_lit!{space_expr!() => "(simple_listen_request_test $v)"}
    const WAIT_URL: &str = concat!(
        server_url!(),
        "/", "busywait",
        "/", "1000",
        "/?", "expr1=", space_expr!(),
        "&", "writer1"
    );
    const LISTEN_URL: &str = concat!(
        server_url!(),
        "/", "status_stream",
        "/", space_expr!(),
    );
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(900)).await;

    //Open up the status listener stream, to receive Server-Side-Events (SSE)
    let response = reqwest::Client::new().get(LISTEN_URL).send().await?.error_for_status()?;
    let mut stream = response.bytes_stream().eventsource();

    //The first event in the stream should be a `pathClear` status
    if let Some(event) = stream.next().await {
        let event = event.unwrap();
        assert_eq!(event.event, "message");
        let response_json: serde_json::Value = serde_json::from_str(&event.data).unwrap();
        assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "pathClear");
    }

    //Send a busywait command
    let response = reqwest::get(WAIT_URL).await?;
    if !response.status().is_success() {
        panic!("Failed to open busy-wait connection: {}", response.status());
    }

    //Now the stream ought to have gotten an updated status, so test to make sure the status change
    // came over the channel, and the new status is `pathForbiddenTemporary`
    if let Some(event) = stream.next().await {
        let event = event.unwrap();
        assert_eq!(event.event, "message");
        let response_json: serde_json::Value = serde_json::from_str(&event.data).unwrap();
        assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "pathForbiddenTemporary");
    }

    //Wait until we get the message that the status has changed
    let start_time = Instant::now();
    while let Some(event) = stream.next().await {
        let event = event.unwrap();
        assert_eq!(event.event, "message");
        let response_json: serde_json::Value = serde_json::from_str(&event.data).unwrap();
        let new_status = response_json.get("status").unwrap().as_str().unwrap();

        //If we finally got a "pathClear" status, make sure at least 800ms have passed (we are sleeping for 1s)
        if new_status == "pathClear" {
            let duration = start_time.elapsed();
            assert!(duration > Duration::from_millis(800));
            break;
        }
    }

    Ok(())
}

/// Tests the "import" command
#[tokio::test]
async fn import_request_test() -> Result<(), Error> {
    decl_lit!{space_expr!() => "(import_test $v)"}
    decl_lit!{file_expr!() => "$v"}

    //GOAT: Should host the content on a local server with predictable delays, to cut down
    // on spurious failures from external servers behaving erratically.)
    const IMPORT_URL: &str = concat!(
        server_url!(),
        "/", "import",
        "/", file_expr!(),
        "/", space_expr!(),
        "/?", "uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta",
    );
    const STATUS_URL: &str = concat!(
        server_url!(),
        "/", "status",
        "/", space_expr!(),
    );
    const COUNT_URL: &str = concat!(
        server_url!(),
        "/", "count",
        "/", space_expr!(),
    );
    // A file that doesn't exist, fails to fetch
    const BOGUS_URL: &str = concat!(
        server_url!(),
        "/", "import",
        "/", file_expr!(),
        "/", space_expr!(),
        "/?", "uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/no_such_file.metta",
    );
    // A file that exists, but fails to parse
    const BAD_FILE_URL: &str = concat!(
        server_url!(),
        "/", "import",
        "/", file_expr!(),
        "/", space_expr!(),
        "/?", "uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/README.md",
    );
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(200)).await;

    //1. First test an end-to-end sucessful fetch and parse
    let response = reqwest::get(IMPORT_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Response: {}", response.text().await?);

    // Check the path immediately; we should get a "pathInUse" response
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    // let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    // assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "pathForbiddenTemporary"); // we need to ensure tests simulate latency somehow for this to be deterministic

    //Now spin until we get a "pathClear" status
    let status = wait_for_url_ne_status(STATUS_URL, "pathForbiddenTemporary").await.unwrap();
    assert_eq!(status, "pathClear");
    println!("Finished loading space");

    //Finally, check that we got the right data in the path by using the count command
    let response = reqwest::get(COUNT_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "countResult");
    assert_eq!(response_json.get("count").unwrap().as_i64().unwrap(), 13);

    //2. Now test a bogus URL, to make sure we can get the error back
    let response = reqwest::get(BOGUS_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    assert!(response_text.starts_with("ACK"));

    //Spin until the status isn't "pathForbiddenTemporary".  Ie. the operation is complete
    wait_for_url_ne_status(STATUS_URL, "pathForbiddenTemporary").await.unwrap();

    //And check that the path contains the correct error
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "fetchError");

    //3. Try with a file that we don't know how to load
    let response = reqwest::get(BAD_FILE_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    assert!(response_text.starts_with("ACK"));

    //Spin until the status isn't "pathForbiddenTemporary".  Ie. the operation is complete
    wait_for_url_ne_status(STATUS_URL, "pathForbiddenTemporary").await.unwrap();

    //And check that the path contains the correct error
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "parseError");

    Ok(())
}

/// Tests both the "upload" and the "export" command
#[tokio::test]
async fn export_request_test() -> Result<(), Error> {
    decl_lit!{space_expr!() => "(export_test $v)"}
    decl_lit!{file_expr!() => "$v"}

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", file_expr!(),
        "/", space_expr!(),
    );
    const PAYLOAD: &str = "(female Liz)\
                            \n(male Tom)\
                            \n(male Bob)\
                            \n(parent Tom Liz)\
                            \n(parent Tom Bob)\
    \n";
    const STATUS_URL: &str = concat!(
        server_url!(),
        "/", "status",
        "/", space_expr!(),
    );
    const EXPORT_URL: &str = concat!(
        server_url!(),
        "/", "export",
        "/", space_expr!(),
        "/", file_expr!(),
        // "/?", "uri=file:///tmp/mork.metta"
    );
    const EXPORT_RAW_URL: &str = concat!(
        server_url!(),
        "/", "export",
        "/", space_expr!(),
        "/", file_expr!(),
        "/?", "format=raw",
        // "&", "uri=file:///tmp/mork.raw"
    );
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(300)).await;

    //First upload a space
    let response = reqwest::Client::new().post(UPLOAD_URL).body(PAYLOAD).send().await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Upload response: {}", response.text().await?);

    // Wait until the server has finished import
    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();
    println!("Finished loading space");

    // Export the data in raw form
    let response = reqwest::get(EXPORT_RAW_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Export Raw response:\n{}", response.text().await?);

    // Export the data in MeTTa form
    let response = reqwest::get(EXPORT_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.text().await?;
    println!("Export MeTTa response:\n{}", response_text);

    let mut sorted_results: Vec<&str> = response_text.lines().collect();
    let mut sorted_payload: Vec<&str> = PAYLOAD.lines().collect();
    sorted_results.sort();
    sorted_payload.sort();
    core::assert_eq!(sorted_results, sorted_payload);

    Ok(())
}

/// Tests the "copy" command
#[tokio::test]
async fn copy_request_test() -> Result<(), Error> {
    decl_lit!{in_expr!() => "(copy_test_royals $v)"}
    decl_lit!{alt_expr!() => "(copy_test_commoners $v)"}
    decl_lit!{file_expr!() => "$v"}

    //GOAT: Should host the content on a local server with predictable delays, to cut down
    // on spurious failures from external servers behaving erratically.)
    const IMPORT_URL: &str = concat!(
        server_url!(),
        "/", "import",
        "/", file_expr!(),
        "/", in_expr!(),
        "/?", "uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta",
    );
    const STATUS_URL: &str = concat!(
        server_url!(),
        "/", "status",
        "/", in_expr!(),
    );
    const COPY_URL: &str = concat!(
        server_url!(),
        "/", "copy",
        "/", in_expr!(),
        "/", alt_expr!(),
    );
    const EXPORT_URL: &str = concat!(
        server_url!(),
        "/", "export",
        "/", alt_expr!(),
        "/", file_expr!(),
    );
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(400)).await;

    //First import a space from a remote
    let response = reqwest::get(IMPORT_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Import response: {}", response.text().await?);

    // Wait until the server has finished import
    let status = wait_for_url_ne_status(STATUS_URL, "pathForbiddenTemporary").await.unwrap();
    assert_eq!(status, "pathClear");
    println!("Finished loading space");

    // Copy the data from `royals` to `commoners`
    let response = reqwest::get(COPY_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Copy response:\n{}", response.text().await?);

    // Export the data commoners
    let response = reqwest::get(EXPORT_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Export response:\n{}", response.text().await?);

    Ok(())
}

/// Tests the "clear" command
#[tokio::test]
async fn clear_request_test() -> Result<(), Error> {
    decl_lit!{space_expr!() => "(clear_test $v)"}
    decl_lit!{file_expr!() => "$v"}

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", file_expr!(),
        "/", space_expr!(),
    );
    const CLEAR_URL: &str = concat!(
        server_url!(),
        "/", "clear",
        "/", space_expr!(),
    );
    const EXPORT_URL: &str = concat!(
        server_url!(),
        "/", "export",
        "/", space_expr!(),
        "/", file_expr!(),
    );
    const PAYLOAD: &str = "(male Bob)";
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(600)).await;

    //Upload the data so we have something to clear
    let response = reqwest::Client::new().post(UPLOAD_URL).body(PAYLOAD).send().await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Upload response: {}", response.text().await?);

    // Clear the data
    let response = reqwest::get(CLEAR_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Clear response:\n{}", response.text().await?);

    // Export the data to confirm nothing is there
    let response = reqwest::get(EXPORT_URL).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_buf = response.text().await?;
    println!("Export response:\n{}", response_buf);
    assert_eq!(response_buf.len(), 0);

    Ok(())
}

/// Tests the "explore" command
#[tokio::test]
async fn explore_request_test() -> Result<(), Error> {
    decl_lit!{space_expr!() => "(explore_test $v)"}
    decl_lit!{file_expr!() => "$v"}
    // decl_lit!{test_expr!() => "(explore_test (parent $a $b))"}
    decl_lit!{test_expr!() => "(explore_test $)"}

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", file_expr!(),
        "/", space_expr!(),
    );
    const PAYLOAD: &str = "(female Liz)\
                            \n(male Tom)\
                            \n(male Bob)\
                            \n(parent Tom Liz)\
                            \n(parent Tom Bob)\
    \n";
    const STATUS_URL: &str = concat!(
        server_url!(),
        "/", "status",
        "/", space_expr!(),
    );
    const EXPLORE_URL: &str = concat!(
        server_url!(),
        "/", "explore",
        "/", test_expr!(),
        "/", // Add a trailing '/' to delineate zero-length token, to begin exploration
    );
    wait_for_server().await.unwrap();

    #[cfg(feature = "serialize_tests")]
    tokio::time::sleep(Duration::from_millis(700)).await;

    //First upload a space
    let response = reqwest::Client::new().post(UPLOAD_URL).body(PAYLOAD).send().await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Upload response: {}", response.text().await?);

    // Wait until the server has finished import
    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();
    println!("Finished loading space");

    // Test the "explore" command
    let response = reqwest::get(format!("{EXPLORE_URL}/")).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.bytes().await?;
    println!("0.0 Explore response:\n{:?}", response_text);

    let response = reqwest::get(format!("{EXPLORE_URL}\x02/")).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.bytes().await?;
    println!("1.0 Explore response:\n{:?}", response_text);

    let response = reqwest::get(format!("{EXPLORE_URL}\x03/")).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.bytes().await?;
    println!("1.1 Explore response:\n{:?}", response_text);

    let response = reqwest::get(format!("{EXPLORE_URL}{}/", urlencoding::encode_binary(b"\x02\xc8\0\0\0\0\0\0\0\x07"))).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.bytes().await?;
    println!("2.0 Explore response:\n{:?}", response_text);

    let response = reqwest::get(format!("{EXPLORE_URL}{}/", urlencoding::encode_binary(b"\x02\xc8\0\0\0\0\0\0\0\x05"))).await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    let response_text = response.bytes().await?;
    println!("2.1 Explore response:\n{:?}", response_text);

    //TODO: it would be nice to parse these responses and feed them forward rather than just inputting the known paths

    Ok(())
}

/// Tests the "transform" command
#[tokio::test]
async fn transform_basic_request_test() -> Result<(), Error> {
    decl_lit!{space_in_expr!() => "(transform_basic_test in $v)"}
    decl_lit!{space_out_expr!() => "(transform_basic_test out $v)"}
    decl_lit!{id_pattern_template!() => "$v"}

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", id_pattern_template!(),
        "/", space_in_expr!(),
    );
    const PAYLOAD : &str = "(a b)\
                           \n(x (y z))\
                           \n";

    const TRANSFORM_REQUEST_URL: &str =
        concat!(
            server_url!(),
            "/", "transform",
        );

    const TRANSFORM_PAYLOAD: &str = concat!(
        "(transform ",
        "    (, ", space_in_expr!(), ")",
        "    (, ", space_out_expr!(), ")",
        ")");

    const EXPORT_ORIGINAL_RAW: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", space_in_expr!(),
            "/", id_pattern_template!(),
            "/?", "format=raw"
        );
    const EXPORT_ORIGINAL_URL: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", space_in_expr!(),
            "/", id_pattern_template!(),
        );

    const EXPORT_TRANSFORMED_URL_RAW: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", space_out_expr!(),
            "/", id_pattern_template!(),
            "/?", "format=raw"
        );
    const EXPORT_TRANSFORMED_URL: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", space_out_expr!(),
            "/", id_pattern_template!(),
        );
    wait_for_server().await.unwrap();

    //First import a space from a remote
    let response = reqwest::Client::new().post(UPLOAD_URL).body(PAYLOAD).send().await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Import response: {}", response.text().await.unwrap());

    // invoke a Transform
    let response = reqwest::Client::new().post(TRANSFORM_REQUEST_URL).body(TRANSFORM_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Transform Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Transform response: {}", response.text().await.unwrap());

    // Export the pre-transformed data in RAW form
    let response_src = reqwest::get(EXPORT_ORIGINAL_RAW).await.unwrap();
    if !response_src.status().is_success() {
        panic!("Error response: {} - {}", response_src.status(), response_src.text().await.unwrap())
    }
    let response_src_text = response_src.text().await.unwrap();
    println!("(out ?) Pre-transformed response:\n{}", response_src_text);

    // Export the pre-transformed data in MeTTa form
    let response_src = reqwest::get(EXPORT_ORIGINAL_URL).await.unwrap();
    if !response_src.status().is_success() {
        panic!("Error response: {} - {}", response_src.status(), response_src.text().await.unwrap())
    }
    let response_src_text = response_src.text().await.unwrap();
    println!("(out ?) Pre-transformed response:\n{}", response_src_text);

    // Export the transformed data in RAW form
    let response_src_id_transform = reqwest::get(EXPORT_TRANSFORMED_URL_RAW).await.unwrap();
    if !response_src_id_transform.status().is_success() {
        panic!("Error response: {} - {}", response_src_id_transform.status(), response_src_id_transform.text().await.unwrap())
    }
    let response_src_id_transform_text = response_src_id_transform.text().await.unwrap();
    println!("(out ?) Post-transformed response:\n{}", response_src_id_transform_text);

    // Export the transformed data in MeTTa form
    let response_src_id_transform = reqwest::get(EXPORT_TRANSFORMED_URL).await.unwrap();
    if !response_src_id_transform.status().is_success() {
        panic!("Error response: {} - {}", response_src_id_transform.status(), response_src_id_transform.text().await.unwrap())
    }
    let response_src_id_transform_text = response_src_id_transform.text().await.unwrap();
    println!("(out ?) Post-transformed response:\n{}", response_src_id_transform_text);

    core::assert_eq!(response_src_text, PAYLOAD);
    core::assert_eq!(response_src_text, response_src_id_transform_text);

    Ok(())
}

#[tokio::test]
async fn transform_ooga_booga_regression_test() -> Result<(), Error> {
    decl_lit!{space_in_expr!() => "(transform_ooga_booga_regression_test in $v)"}
    decl_lit!{space_out_expr!() => "(transform_ooga_booga_regression_test out $v)"}
    decl_lit!{id_pattern_template!() => "$v"}

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", id_pattern_template!(),
        "/", space_in_expr!(),
    );
    const UPLOAD_PAYLOAD : &str = "(Sound (caveman (OOGA BOOGA)))";

    const TRANSFORM_REQUEST_URL: &str =
        concat!(
            server_url!(),
            "/", "transform",
        );

    const TRANSFORM_PAYLOAD : &str =
     "(transform\
    \n    (, (transform_ooga_booga_regression_test in (Sound ($n $s)) ))\
    \n    (, (transform_ooga_booga_regression_test out (The $n is a creature that makes the following sound: $s) ))\
    \n)\
    ";

    const EXPORT_TRANSFORMED_URL_RAW: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", space_out_expr!(),
            "/", id_pattern_template!(),
            "/?", "format=raw"
        );
    const EXPORT_TRANSFORMED_URL: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", space_out_expr!(),
            "/", id_pattern_template!(),
        );
    wait_for_server().await.unwrap();

    //First import a space from a remote
    let response = reqwest::Client::new().post(UPLOAD_URL).body(UPLOAD_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Import response: {}", response.text().await.unwrap());

    // invoke a Transform
    let response = reqwest::Client::new().post(TRANSFORM_REQUEST_URL).body(TRANSFORM_PAYLOAD).send().await.unwrap();
    if !response.status().is_success() {
        panic!("Transform Error response: {} - {}", response.status(), response.text().await?)
    }
    println!("Transform response: {}", response.text().await.unwrap());

    // Export the transformed data in RAW form
    let response_src_id_transform = reqwest::get(EXPORT_TRANSFORMED_URL_RAW).await.unwrap();
    if !response_src_id_transform.status().is_success() {
        panic!("Error response: {} - {}", response_src_id_transform.status(), response_src_id_transform.text().await.unwrap())
    }
    let response_src_id_transform_text = response_src_id_transform.text().await.unwrap();
    println!("transformed response:\n{}", response_src_id_transform_text);

    // Export the transformed data in MeTTa form
    let response_src_transform = reqwest::get(EXPORT_TRANSFORMED_URL).await.unwrap();
    if !response_src_transform.status().is_success() {
        panic!("Error response: {} - {}", response_src_transform.status(), response_src_transform.text().await.unwrap())
    }
    let response_src_transform_text = response_src_transform.text().await.unwrap();
    println!("transformed response:\n{}", response_src_transform_text);


    core::assert_eq!(
        "(The caveman is a creature that makes the following sound: (OOGA BOOGA))\n".to_string(),
        response_src_transform_text
    );

    Ok(())
}


#[cfg(not(feature="interning"))]
#[tokio::test]
async fn upload_export_paths() -> Result<(), Error> {
    use std::io::BufRead;

    decl_lit!{io_expr!() =>  "(upload_export_paths $v)"}
    decl_lit!{id_pattern_template!() => "$v"}


    const SEXPR_UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", id_pattern_template!(),
        "/", io_expr!(),
    );
    const SEXPR_PAYLOAD : &str = concat!(
       "(a b c d)\n",
       "(a b c)\n",
       "(a b)\n",
       "(a)",
    )
    ;
    const EXPORT_PATHS_URL: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", io_expr!(),
            "/", id_pattern_template!(),
            "/?", "format=paths"
        );
    const CLEAR_URL : &str = concat!(
        server_url!(),
        "/", "clear",
        "/", io_expr!(),
    );
    const STATUS_URL : &str = concat!(
        server_url!(),
        "/", "status",
        "/", io_expr!(),
    );
    const PATHS_UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", id_pattern_template!(),
        "/", io_expr!(),
        "/?", "format=paths"
    );
    const EXPORT_SEXPR_URL: &str =
        concat!(
            server_url!(),
            "/", "export",
            "/", io_expr!(),
            "/", id_pattern_template!(),
        );

    wait_for_server().await.unwrap();

    // upload Sexprs
    let response = reqwest::Client::new().post(SEXPR_UPLOAD_URL).body(SEXPR_PAYLOAD).send().await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }

    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();

    // export as `paths`
    let response = reqwest::Client::new().get(EXPORT_PATHS_URL).send().await?;
    let status = response.status();
    if !status.is_success() {
        panic!("Error response: {} - {}", status, response.text().await?)
    }
    let path_bytes   = response.bytes().await.unwrap();

    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();

    // clear

    let response = reqwest::Client::new().get(CLEAR_URL).send().await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }

    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();
    let response_ = reqwest::Client::new().get(EXPORT_PATHS_URL).send().await?;
    // let response_ = reqwest::Client::new().get(EXPORT_SEXPR_URL).send().await?;
    let status = response_.status();
    if !status.is_success() {
        panic!("Error response: {} - {}", status, response_.text().await?)
    }
    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();


    // upload as `paths``

    let response = reqwest::Client::new().post(PATHS_UPLOAD_URL).body(path_bytes).send().await?;
    if !response.status().is_success() {
        panic!("Error response: {} - {}", response.status(), response.text().await?)
    }

    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();

    // export as Sexprs
        wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();
    // let response_ = reqwest::Client::new().get(EXPORT_PATHS_URL).send().await?;
    let response_ = reqwest::Client::new().get(EXPORT_SEXPR_URL).send().await?;
    let status = response_.status();
    if !status.is_success() {
        panic!("Error response: {} - {}", status, response_.text().await?)
    }
    let sexpr_bytes   = response_.bytes().await.unwrap();

    wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();


    let mut map = pathmap::PathMap::new();
    for each in SEXPR_PAYLOAD.lines() {
        map.set_val_at(each, ());
    }
    for each_ in sexpr_bytes.lines() {
        let each = each_.unwrap();
        let Some(_) = map.set_val_at(
            each, ())
            else { panic!() };
    }


    Ok(())
}

/// Tests that it's at least possible to write to the root of the space
///
/// This test is ignored because it pollutes the root of the space with crap and holds a lock that
/// interferes with the rest of the tests.
#[ignore]
#[tokio::test]
async fn root_writer_test() -> Result<(), Error> {
    decl_lit!{space_in_expr!() => "$v"}
    decl_lit!{id_pattern_template!() => "$v"}

    const UPLOAD_URL: &str = concat!(
        server_url!(),
        "/", "upload",
        "/", id_pattern_template!(),
        "/", space_in_expr!(),
    );
    const UPLOAD_PAYLOAD : &str = "(just a list)";
    const STATUS_URL: &str = concat!(
        server_url!(),
        "/", "status",
        "/", space_in_expr!(),
    );

    wait_for_server().await.unwrap();

    //First import a space from a remote
    for _ in 0..100000 {
        let response = reqwest::Client::new().post(UPLOAD_URL).body(UPLOAD_PAYLOAD).send().await.unwrap();
        if !response.status().is_success() {
            wait_for_url_eq_status(STATUS_URL, "pathClear").await.unwrap();
        } else {
            return Ok(());
        }
    }

    panic!()
}
