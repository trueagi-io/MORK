
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
use tokio::fs::{self, File};
use std::io::{self, ErrorKind};

use super::{CommandError, StatusCode};

const HASH_SEED: i64 = 1234;
const IN_PROGRESS_TIMESTAMP: &'static str = "0000000000000000";

/// Responsible for caching and cataloging versioned resources on disk
pub struct ResourceStore {
    dir_path: PathBuf,
}

/// Represents a resource that is in-use by a command
pub struct ResourceHandle {
    cmd_id: u64,
    identifier: String,
    path: Option<PathBuf>,
}

impl Drop for ResourceHandle {
    fn drop(&mut self) {
        let path = core::mem::take(&mut self.path);
        match path {
            Some(path) => {
                tokio::task::spawn(async move {
                    let _ = fs::remove_file(path).await;
                });
            },
            None => {}
        }
    }
}

impl ResourceHandle {
    /// Returns the filesystem path to the resource
    pub fn path(&self) -> Result<&Path, CommandError> {
        self.path.as_ref().map(|path| path.as_ref()).ok_or_else(|| self.resource_err())
    }

    /// Updates an existing in-progress resource with a timestamp, marking it as finalized
    ///
    /// This method should be called when the parsing and loading of a resource has finished
    pub async fn finalize(&mut self, new_timestamp: u64) -> Result<(), CommandError> {
        let old_path = self.path.as_ref().ok_or_else(|| self.resource_err())?;
        let new_file_name = format!("{new_timestamp:0>16x}-{:0>16x}-{:16x}", self.cmd_id, gxhash::gxhash64(self.identifier.as_bytes(), HASH_SEED));
        let dir_path: &Path = old_path.parent().ok_or_else(|| self.resource_err())?;
        let new_path: PathBuf = dir_path.join(Path::new(&new_file_name));
        fs::rename(old_path, new_path).await?;
        self.path = None;
        Ok(())
    }

    /// Internal method to make a `ResourceHandle` from an existing file
    fn new(path: PathBuf, identifier: impl Into<String>, cmd_id: u64) -> Self {
        Self { cmd_id, path: Some(path), identifier: identifier.into() }
    }

    /// Internal method to compose an internal resource error
    fn resource_err(&self) -> CommandError {
        CommandError::internal(format!("Error accessing resource at path: {:?}", self.path))
    }
}

impl ResourceStore {
    /// Creates a new `ResourceStore`, using a directory specified by `path`
    pub async fn new_with_dir_path<P: AsRef<Path>>(path: P) -> Result<Self, CommandError> {
        let dir_path: PathBuf = path.as_ref().into();

        //Create the resource storage dir, if it doesn't exist
        if dir_path.exists() && !dir_path.is_dir() {
            return Err(io::Error::new(ErrorKind::AlreadyExists, format!("Resource path exists but is not a directory: {:?}", dir_path)).into());
        } else {
            fs::create_dir_all(&dir_path).await?;
        }

        Ok(Self {
            dir_path
        })
    }
    /// Constructs the file path of a new file for a given resource identifier (e.g. a uri), and creates
    /// a zero-length file at the path so the same file isn't downloaded multiple times in parallel 
    ///
    /// Returns an error if the file already exists
    pub async fn new_resource(&self, res_identifier: &str, cmd_id: u64) -> Result<ResourceHandle, CommandError> {
        let file_name = format!("{IN_PROGRESS_TIMESTAMP}-{cmd_id:0>16x}-{:16x}", gxhash::gxhash64(res_identifier.as_bytes(), HASH_SEED));
        let path: PathBuf = self.dir_path.join(Path::new(&file_name));
        let _file = File::create_new(&path).await.map_err(|err| {
            if err.kind() == std::io::ErrorKind::AlreadyExists {
                CommandError::external(StatusCode::TOO_EARLY, "File requested while a download of the same file was in-progress")
            } else {
                err.into() //Another (Internal) Errror
            }
        })?;
        Ok(ResourceHandle::new(path, res_identifier, cmd_id))
    }
    /// Removes all files in the store
    ///
    /// This method should be called after syncing the server with the log, before accepting new connections
    pub async fn reset(&self) -> Result<(), CommandError> {
        fs::remove_dir_all(&self.dir_path).await?;
        fs::create_dir_all(&self.dir_path).await?;
        Ok(())
    }
    //GOAT, working but currently unused.  WILL BE USED after restoring from a backup
    #[allow(unused)]
    /// Removes all files in the store that are time-stamped before the specified value
    ///
    /// This method should be called after a server snap-shotted to remove files already integrated
    /// into the frozen version of the database
    pub async fn purge_before_timestamp(&self, threshold_timestamp: u64) -> Result<(), CommandError> {
        let mut dir = fs::read_dir(&self.dir_path).await?;
        while let Some(entry) = dir.next_entry().await? {
            let path = entry.path();

            let file_timestamp = timestamp_from_path(&path)?;
            if file_timestamp < threshold_timestamp {
                fs::remove_file(path).await?;
            }
        }
        Ok(())
    }
}

/// Returns the timestamp for a given file path
fn timestamp_from_path<P: AsRef<Path>>(path: P) -> Result<u64, CommandError> {
    let path = path.as_ref();
    let name_str = path.file_name().ok_or_else(|| CommandError::internal("unrecognized file in resources dir"))?
        .to_str().ok_or_else(|| CommandError::internal("file name contained invalid characters"))?;
    if name_str.len() < 33 {
        return Err(CommandError::internal(format!("Unrecognized file in resources dir: {name_str}")).into())
    }
    let timestamp = u64::from_str_radix(&name_str[0..16], 10)?;
    Ok(timestamp)
}
