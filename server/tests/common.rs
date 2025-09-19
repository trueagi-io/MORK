
//! ===================================================================================
//! *****************       READ THIS BEFORE ADDING NEW TESTS         *****************
//! ===================================================================================
//! The `aaa_start_stop_test` test is responsible for starting and stopping the
//! server, and the rest of the tests will wait until they confirm the server is alive
//! ===================================================================================

use std::time::Duration;
use reqwest::Error;

/// Convenience to declare a literal to use like a constant
#[macro_export]
macro_rules! decl_lit { ($NAME:ident!() => $LIT:tt) => { macro_rules! $NAME { () => { $LIT }; } }; }

#[macro_export]
macro_rules! server_url { () => { "http://127.0.0.1:8000" }; }

/// Waits for the server to become available
pub async fn wait_for_server() -> Result<(), Error> {
    //TODO: Do we want a new command that returns the server status, as opposed to a path status?
    const URL: &str = concat!(
        server_url!(),
        "/", "status",
        "/", "-"
    );
    loop {
        match reqwest::get(URL).await {
            Ok(response) => {
                if response.status().is_success() {
                    return Ok(())
                }
            },
            Err(_) => {}
        }
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

#[allow(dead_code)]
pub async fn wait_for_url_eq_status(url : &str, expected_status : &str) -> Result<(), reqwest::Error> {
    loop {
        let status = get_url_status(url).await?;
        if status == expected_status {
            return Ok(())
        } else {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
    }
}
#[allow(dead_code)]
pub async fn wait_for_url_ne_status(url : &str, expected_status : &str) -> Result<String, reqwest::Error> {
    loop {
        let status = get_url_status(url).await?;
        if status != expected_status {
            return Ok(status)
        } else {
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
    }
}
pub async fn get_url_status(url : &str) -> Result<String, reqwest::Error> {
    let response = reqwest::get(url).await?;
    assert!(response.status().is_success());
    let response_text = response.text().await?;
    // println!("Status (polling) response: {}", response_text);
    let response_json: serde_json::Value = serde_json::from_str(&response_text).unwrap();
    Ok(response_json.get("status").unwrap().as_str().unwrap().to_string())
}

/// Starts the server, and then dispatches a `stop?wait_for_idle` request
#[tokio::test]
async fn aaa_start_stop_test() -> Result<(), Error> {

    //Start the server
    let mut server_proc = std::process::Command::new(env!("CARGO_BIN_EXE_mork-server")).spawn().unwrap();
    // println!("start_stop_test: Server start initiated");

    //Give the server time to start, and give the other tests a chance to start using the server
    tokio::time::sleep(std::time::Duration::from_secs(1)).await;

    // println!("start_stop_test: Sending stop request");
    const STOP_URL: &str = concat!( 
        server_url!(),
        "/", "stop",
        "/?", "wait_for_idle",
    );
    let response = reqwest::get(STOP_URL).await?;
    if response.status().is_success() {
        // println!("start_stop_test: Received response: {}", response.text().await?);
    } else {
        panic!("start_stop_test: Failed to send stop request: {}", response.status());
    }

    //Wait for the server to exit
    // println!("start_stop_test: Waiting for server to stop");
    server_proc.wait().unwrap();

    // println!("start_stop_test: Server stopped");
    Ok(())
}
