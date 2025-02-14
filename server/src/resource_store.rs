
//! The primary function of this module is to support the import functionality
//!
//! This module is designed around the ability to reconstruct exactly the same database if we have to start
//! over from a previous snapshot.  We have to assume the outside world is liable to change at any moment,
//! so we can never rely on re-downloading a file.
//!
//! All files in the `ResourceStore` have 2 components: The `source_hash` and the `timestamp`.  The final
//! timestamp is assigned after the import operation has completed (including all loading and parsing).
//!

use std::path::{Path, PathBuf};
use std::fs::{self, File};
use std::io::{self, ErrorKind};

use super::BoxedErr;

const HASH_SEED: i64 = 1234;
const IN_PROGRESS_TIMESTAMP: &'static str = "0000000000000000";

/// Responsible for caching and cataloging versioned resources on disk
pub struct ResourceStore {
    dir_path: PathBuf,
}

impl ResourceStore {
    /// Creates a new `ResourceStore`, using a directory specified by `path`
    pub fn new_with_dir_path<P: AsRef<Path>>(path: P) -> Result<Self, BoxedErr> {
        let dir_path: PathBuf = path.as_ref().into();

        //Create the resource storage dir, if it doesn't exist
        if dir_path.exists() && !dir_path.is_dir() {
            return Err(io::Error::new(ErrorKind::AlreadyExists, format!("Resource path exists but is not a directory: {:?}", dir_path)).into());
        } else {
            fs::create_dir_all(&dir_path)?;
        }

        Ok(Self {
            dir_path
        })
    }
    /// Constructs the file path of a new file for a given resource identifier (e.g. a uri), and creates
    /// a zero-length file at the path so the same file isn't downloaded multiple times in parallel 
    ///
    /// Returns an error if the file already exists
    pub fn new_path_for_resource(&self, res_identifier: &str) -> Result<PathBuf, BoxedErr> {
        let file_name = format!("{IN_PROGRESS_TIMESTAMP}-{:16x}", gxhash::gxhash64(res_identifier.as_bytes(), HASH_SEED));
        let path: PathBuf = self.dir_path.join(Path::new(&file_name));
        let _file = File::create_new(&path)?;
        Ok(path)
    }
    /// Updates an existing in-progress resource with a timestamp, marking it as finalized
    ///
    /// This method should be called when the parsing and loading of a resource has finished
    pub fn set_timestamp_for_resource(&self, res_identifier: &str, new_timestamp: u64) -> Result<(), BoxedErr> {
        let old_file_name = format!("{IN_PROGRESS_TIMESTAMP}-{:16x}", gxhash::gxhash64(res_identifier.as_bytes(), HASH_SEED));
        let new_file_name = format!("{new_timestamp:16x}-{:16x}", gxhash::gxhash64(res_identifier.as_bytes(), HASH_SEED));
        let old_path: PathBuf = self.dir_path.join(Path::new(&old_file_name));
        let new_path: PathBuf = self.dir_path.join(Path::new(&new_file_name));
        fs::rename(old_path, new_path)?;
        Ok(())
    }
    /// Removes a specific resource from the store
    ///
    /// This method should be called when an error occurred during download, parsing, or loading
    pub fn purge_in_progress_resource(&self, res_identifier: &str) -> Result<(), BoxedErr> {
        let file_name = format!("{IN_PROGRESS_TIMESTAMP}-{:16x}", gxhash::gxhash64(res_identifier.as_bytes(), HASH_SEED));
        let path: PathBuf = self.dir_path.join(Path::new(&file_name));
        fs::remove_file(path)?;
        Ok(())
    }
    /// Removes all files in the store
    ///
    /// This method should be called after syncing the server with the log, before accepting new connections
    pub fn reset(&self) -> Result<(), BoxedErr> {
        fs::remove_dir_all(&self.dir_path)?;
        fs::create_dir_all(&self.dir_path)?;
        Ok(())
    }
    /// Removes all files in the store that are time-stamped before the specified value
    ///
    /// This method should be called after a server snap-shotted to remove files already integrated
    /// into the frozen version of the database
    pub fn purge_before_timestamp(&self, threshold_timestamp: u64) -> Result<(), BoxedErr> {
        for entry in fs::read_dir(&self.dir_path)? {
            let entry = entry?; // Get DirEntry
            let path = entry.path();

            let file_timestamp = timestamp_from_path(&path)?;
            if file_timestamp < threshold_timestamp {
                fs::remove_file(path)?;
            }
        }
        Ok(())
    }
}

/// Returns the timestamp for a given file path
fn timestamp_from_path<P: AsRef<Path>>(path: P) -> Result<u64, BoxedErr> {
    let path = path.as_ref();
    let name_str = path.file_name().ok_or_else(|| "unrecognized file in resources dir")?
        .to_str().ok_or_else(|| "file name contained invalid characters")?;
    if name_str.len() < 33 {
        return Err(format!("Unrecognized file in resources dir: {name_str}").into())
    }
    let timestamp = u64::from_str_radix(&name_str[0..16], 10)?;
    Ok(timestamp)
}