
use std::time::Instant;
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
                    eprintln!("Request failed: {:?}", err);
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
                    eprintln!("Request failed: {:?} - {:?} elapsed", err, start.elapsed());
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
async fn stop_request_test() -> Result<(), Error> {
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
                    // eprintln!("Request failed: {:?} - {:?} elapsed", _err, _start.elapsed());
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

//GOAT, put this back
    // //1. First test an end-to-end sucessful fetch and parse
    // let response = reqwest::get(IMPORT_URL).await?;
    // assert!(response.status().is_success());
    // println!("Response: {}", response.text().await?);

    // // Check the path immediately; we should get a "path busy" response
    // let response = reqwest::get(STATUS_URL).await?;
    // assert!(response.status().is_success());
    // println!("Response: {}", response.text().await?);
    // // assert!() GOAT, Should we serialize the response as JSON?

    // //GOAT, sleep for 1s, and then check that we can inspect the path.


    //2. Now test a bogus URL, to make sure we can get the error back
    const BOGUS_URL: &str = "http://127.0.0.1:8000/import/royals/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/no_such_file.metta";
    let response = reqwest::get(BOGUS_URL).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    println!("Response: {}", response_text);
    assert!(response_text.starts_with("ACK"));

    //Now sleep for a second, and check that the path contains the correct error
    std::thread::sleep(std::time::Duration::from_secs(1));
    let response = reqwest::get(STATUS_URL).await?;
    assert!(response.status().is_success());
    println!("Response: {}", response.text().await?);
    // assert!() GOAT, Should we serialize the response as JSON?


    //3. Now test a situation where we make a request for the same file at a different path, while the
    // previous download is still in process
    //GOAT

    Ok(())
}


