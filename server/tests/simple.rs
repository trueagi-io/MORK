
use std::time::Instant;
use hyper::StatusCode;
use tokio::task;
use reqwest::{Client, Error};

/// Opens one client request
#[tokio::test]
async fn simple_request_test() -> Result<(), Error> {
    const URL: &str = "http://127.0.0.1:8000/busywait/2000";

    let response = reqwest::get(URL).await?;

    if response.status().is_success() {
        let body = response.text().await?;
        println!("Response: {}", body);
    } else {
        println!("Failed to load page: {}", response.status());
    }

    Ok(())
}

/// Opens many client requests at the same time
#[tokio::test]
async fn many_request_instant_test() -> Result<(), Error> {
    const URL: &str = "http://127.0.0.1:8000/busywait/2000";
    const NUM_REQUESTS: usize = 100;

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

/// Opens many client requests with a short delay between each
#[tokio::test]
async fn many_request_delayed_test() -> Result<(), Error> {
    const URL: &str = "http://127.0.0.1:8000/busywait/2000";
    const NUM_REQUESTS: usize = 100;
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
#[tokio::test]
async fn zzz_stop_request_test() -> Result<(), Error> {
    const URL: &str = "http://127.0.0.1:8000/busywait/2000";
    const STOP_URL: &str = "http://127.0.0.1:8000/stop/";
    const NUM_REQUESTS: usize = 100;
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
            Err(_err) => {
                // eprintln!("Request failed: {:?} - {:?} elapsed", _err, _start.elapsed());
                panic!()
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

/// Tests the "import" command
#[tokio::test]
async fn import_request_test() -> Result<(), Error> {
    //GOAT: Should host the content on a local server with predictable delays, to cut down
    // on spurious failures from external servers behaving erratically.)
    const IMPORT_URL: &str = "http://127.0.0.1:8000/import/royals/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta";
    const STATUS_URL: &str = "http://127.0.0.1:8000/status/royals/";

    //1. First test an end-to-end sucessful fetch and parse
    let response = reqwest::get(IMPORT_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {}", response.text().await?);
        panic!()
    }
    println!("Response: {}", response.text().await?);

    // Check the path immediately; we should get a "pathInUse" response
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "pathForbiddenTemporary");

    //Now sleep for a bit (600ms), and then check that we can inspect the path.
    std::thread::sleep(std::time::Duration::from_millis(600)); //GOAT, put this back to 600ms
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "pathClear");

    //Finally, check that we got the right data in the path by using the count command
    const COUNT_URL: &str = "http://127.0.0.1:8000/count/royals/";
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
    const BOGUS_URL: &str = "http://127.0.0.1:8000/import/royals/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/no_such_file.metta";
    let response = reqwest::get(BOGUS_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {}", response.text().await?);
        panic!()
    }
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    assert!(response_text.starts_with("ACK"));

    //Now sleep for a bit (600ms), and check that the path contains the correct error
    std::thread::sleep(std::time::Duration::from_millis(600));
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "fetchError");

    //3. Try with a file that we don't know how to load
    const BAD_FILE_URL: &str = "http://127.0.0.1:8000/import/royals/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/README.md";
    let response = reqwest::get(BAD_FILE_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {}", response.text().await?);
        panic!()
    }
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    assert!(response_text.starts_with("ACK"));

    //Now sleep for a bit (600ms), and check that the path contains the correct error
    std::thread::sleep(std::time::Duration::from_millis(600));
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "parseError");

    //4. Now test a situation where we make a request for the same file at two different paths
    // Since the file caching works on a per-resource basis, the second request should be denied
    let response = reqwest::get(IMPORT_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {}", response.text().await?);
        panic!()
    }
    println!("Response: {}", response.text().await?);

    //Ensure the second request gets rejected immediately with the right status
    const ALT_PATH_URL: &str = "http://127.0.0.1:8000/import/royal-with-cheese/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta";
    const ALT_STATUS_URL: &str = "http://127.0.0.1:8000/status/royal-with-cheese/";
    let response = reqwest::get(ALT_PATH_URL).await?;
    assert_eq!(response.status(), StatusCode::TOO_EARLY);

    //Check that the path to the failed resource is clear and available
    let response = reqwest::get(ALT_STATUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    assert_eq!(response_json.get("status").unwrap().as_str().unwrap(), "pathClear");

    //Now sleep for a bit (600ms), and check that everything got cleaned up and the re-fetch will succeed
    //GOAT

    Ok(())
}

/// Tests the "export" command
#[tokio::test]
async fn export_request_test() -> Result<(), Error> {

    //GOAT: Should host the content on a local server with predictable delays, to cut down
    // on spurious failures from external servers behaving erratically.)
    const IMPORT_URL: &str = "http://127.0.0.1:8000/import/royals/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta";
    const STATUS_URL: &str = "http://127.0.0.1:8000/status/royals/";
    const EXPORT_URL: &str = "http://127.0.0.1:8000/export/royals/";
    const EXPORT_RAW_URL: &str = "http://127.0.0.1:8000/export/royals/?format=raw";

    //First import a space from a remote
    let response = reqwest::get(IMPORT_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {}", response.text().await?);
        panic!()
    }
    println!("Import response: {}", response.text().await?);

    // Wait until the server has finished import
    loop {
        std::thread::sleep(std::time::Duration::from_millis(10));
        let response = reqwest::get(STATUS_URL).await?;
        assert!(response.status().is_success());
        let response_text = response.text().await?;
        println!("Status (polling) response: {}", response_text);
        let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
        if response_json.get("status").unwrap().as_str().unwrap() == "pathClear" {
            break
        }
    }
    println!("Finished loading space");

    // Export the data in raw form
    let response = reqwest::get(EXPORT_RAW_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {} - {}", response.status(), response.text().await?);
        panic!()
    }
    println!("Export Raw response:\n{}", response.text().await?);

    // Export the data in MeTTa form
    let response = reqwest::get(EXPORT_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {} - {}", response.status(), response.text().await?);
        panic!()
    }
    println!("Export MeTTa response:\n{}", response.text().await?);

    Ok(())
}

/// Tests the "copy" command
#[tokio::test]
async fn copy_request_test() -> Result<(), Error> {

    //GOAT: Should host the content on a local server with predictable delays, to cut down
    // on spurious failures from external servers behaving erratically.)
    const IMPORT_URL: &str = "http://127.0.0.1:8000/import/royals/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta";
    const STATUS_URL: &str = "http://127.0.0.1:8000/status/royals/";
    const COPY_URL: &str = "http://127.0.0.1:8000/copy/royals/commoners/";
    const EXPORT_URL: &str = "http://127.0.0.1:8000/export/commoners/";

    //First import a space from a remote
    let response = reqwest::get(IMPORT_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {}", response.text().await?);
        panic!()
    }
    println!("Import response: {}", response.text().await?);

    // Wait until the server has finished import
    loop {
        std::thread::sleep(std::time::Duration::from_millis(10));
        let response = reqwest::get(STATUS_URL).await?;
        assert!(response.status().is_success());
        let response_text = response.text().await?;
        println!("Status (polling) response: {}", response_text);
        let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
        if response_json.get("status").unwrap().as_str().unwrap() == "pathClear" {
            break
        }
    }
    println!("Finished loading space");

    // Copy the data from `royals` to `commoners`
    let response = reqwest::get(COPY_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {} - {}", response.status(), response.text().await?);
        panic!()
    }
    println!("Copy response:\n{}", response.text().await?);

    // Export the data commoners
    let response = reqwest::get(EXPORT_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {} - {}", response.status(), response.text().await?);
        panic!()
    }
    println!("Export response:\n{}", response.text().await?);

    Ok(())
}

/// Tests the "upload" command
#[tokio::test]
async fn upload_request_test() -> Result<(), Error> {

    //GOAT: Should host the content on a local server with predictable delays, to cut down
    // on spurious failures from external servers behaving erratically.)
    const UPLOAD_URL: &str = "http://127.0.0.1:8000/upload/royals/";
    const EXPORT_URL: &str = "http://127.0.0.1:8000/export/royals/";
    const PAYLOAD: &str = r#"
        (female Liz)
        (male Tom)
        (male Bob)
        (parent Tom Bob)
        (parent Tom Liz)
    "#;

    //First import a space from a remote
    let response = reqwest::Client::new().post(UPLOAD_URL).body(PAYLOAD).send().await?;
    if !response.status().is_success() {
        println!("Error response: {}", response.text().await?);
        panic!()
    }
    println!("Upload response: {}", response.text().await?);

    // Export the data back out
    let response = reqwest::get(EXPORT_URL).await?;
    if !response.status().is_success() {
        println!("Error response: {} - {}", response.status(), response.text().await?);
        panic!()
    }
    println!("Export response:\n{}", response.text().await?);

    Ok(())
}


// /// Tests the "export" command
// #[tokio::test]
// async fn id_transform_request_test() -> Result<(), Error> {
//     todo!("WIP");

//     //GOAT: Should host the content on a local server with predictable delays, to cut down
//     // on spurious failures from external servers behaving erratically.)
//     const IMPORT_URL: &str = "http://127.0.0.1:8000/import/royals/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta";
//     const STATUS_URL: &str = "http://127.0.0.1:8000/status/royals/";




//     const TRANSFORM_REQUEST_URL: &str = concat!("http://127.0.0.1:8000",
//                                                 "/transform",
//                                                 "/royals",                          // from_space
//                                                 "/royals_id_transform/",            // to_space
//                                                 "/", url_percent_encode!("$"), "x", // pattern
//                                                 "/", url_percent_encode!("$"), "x", // template
//                                         );

//     const EXPORT_URL: &str = "http://127.0.0.1:8000/export/royals/";
//     const EXPORT_RAW_URL: &str = "http://127.0.0.1:8000/export/royals/?format=raw";

//     const EXPORT_ID_TRANSFORM_URL: &str = "http://127.0.0.1:8000/export/royals_/";
//     const EXPORT_ID_TRANSFORM_RAW_URL: &str = "http://127.0.0.1:8000/export/royals/?format=raw";

//     //First import a space from a remote
//     let response = reqwest::get(IMPORT_URL).await?;
//     if !response.status().is_success() {
//         println!("Error response: {}", response.text().await?);
//         panic!()
//     }
//     println!("Import response: {}", response.text().await?);

//     // Wait until the server has finished import
//     loop {
//         std::thread::sleep(std::time::Duration::from_millis(10));
//         let response = reqwest::get(STATUS_URL).await?;
//         assert!(response.status().is_success());
//         let response_text = response.text().await?;
//         println!("Status (polling) response: {}", response_text);
//         let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
//         if response_json.get("status").unwrap().as_str().unwrap() == "pathClear" {
//             break
//         }
//     }
//     println!("Finished loading space");




//     // Export the data in raw form
//     let response = reqwest::get(EXPORT_RAW_URL).await?;
//     if !response.status().is_success() {
//         println!("Error response: {} - {}", response.status(), response.text().await?);
//         panic!()
//     }
//     println!("Export Raw response:\n{}", response.text().await?);

//     // Export the data in MeTTa form
//     let response = reqwest::get(EXPORT_URL).await?;
//     if !response.status().is_success() {
//         println!("Error response: {} - {}", response.status(), response.text().await?);
//         panic!()
//     }
//     println!("Export MeTTa response:\n{}", response.text().await?);

//     Ok(())
// }

