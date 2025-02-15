
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
    const FETCH_URL: &str = "http://127.0.0.1:8000/fetch/%7Eroyals.toy.metta/?uri=https://raw.githubusercontent.com/trueagi-io/metta-examples/refs/heads/main/aunt-kg/toy.metta";
    const IMPORT_URL: &str = "http://127.0.0.1:8000/import/royals/%7Eroyals.toy%7E.metta";

    let response = reqwest::get(FETCH_URL).await?;
    if response.status().is_success() {
        let body = response.text().await?;
        println!("Response: {}", body);
    } else {
        println!("Failed to load page: {}", response.status());
    }

    let response = reqwest::get(IMPORT_URL).await?;

    if response.status().is_success() {
        let body = response.text().await?;
        println!("Response: {}", body);
    } else {
        println!("Failed to load page: {}", response.status());
    }

    Ok(())
}


