
use std::sync::RwLock;
use serde::{Serialize, Serializer};

use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{ZipperWriting, ZipperMoving};
use pathmap::zipper_tracking::{PathStatus, SharedTrackerPaths, ZipperTracker, TrackingRead, TrackingWrite};

use hyper::StatusCode;

use crate::BoxedErr;

/// A status associated with a specific path
///
/// The status map tracks the results of commands that execute asynchronously from the user's perspective.
/// The results of a user's command, and errors in particular, will be written to the status map so the
/// user can check them, and so future commands don't proceed if their required resources are in a bad
/// or unready state.
#[derive(Clone, Debug, Default, Serialize, PartialEq, Eq)]
#[serde(tag = "status")]
#[serde(rename_all = "camelCase")]
pub enum StatusRecord {
    #[default]
    PathClear,
    PathReadOnly,
    PathReadOnlyTemporary,
    PathForbidden,
    PathForbiddenTemporary,
    CountResult(CountResult),
    FetchError(FetchError),
    ParseError(ParseError),
    ExecSyntaxError(String)
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct CountResult {
    count: usize
}

impl From<usize> for CountResult {
    fn from(count: usize) -> Self {
        Self{ count }
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct FetchError {
    pub(crate) log_message: String,
    #[serde(serialize_with = "serialize_status_code")]
    pub(crate) status_code: StatusCode,
}
fn serialize_status_code<S: Serializer>(status_code: &StatusCode, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_u16((*status_code).into())
}

impl FetchError {
    pub fn new<M: Into<String>>(status_code: StatusCode, log_message: M) -> Self {
        Self { status_code, log_message: log_message.into() }
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct ParseError {
    //TODO, Eventually we probably want specific parse errors, such as line number / byte offset, etc.
    pub(crate) log_message: String,
}

impl ParseError {
    pub fn new<M: Into<String>>(log_message: M) -> Self {
        Self { log_message: log_message.into() }
    }
}

impl StatusRecord {
    /// Returns `true` if the status can block the creation of a writer at that path
    fn blocks_writer(&self) -> bool {
        match self {
            Self::PathClear => false,
            Self::CountResult(_) => false,
            Self::PathReadOnly => true,
            Self::PathReadOnlyTemporary => true,
            Self::PathForbidden => true,
            Self::PathForbiddenTemporary => true,
            Self::FetchError(_) => false,
            Self::ParseError(_) => false,
            Self::ExecSyntaxError(_) => false,
        }
    }
    /// Returns `true` if the status can block the creation of a reader at that path
    fn blocks_reader(&self) -> bool {
        match self {
            Self::PathClear => false,
            Self::CountResult(_) => false,
            Self::PathReadOnly => true,
            Self::PathReadOnlyTemporary => true,
            Self::PathForbidden => true,
            Self::PathForbiddenTemporary => true,
            Self::FetchError(_) => true,
            Self::ParseError(_) => true,
            Self::ExecSyntaxError(_) => false,
        }
    }
}

/// Permission to read from a path
pub struct ReadPermission(Vec<u8>, #[allow(dead_code)]ZipperTracker<TrackingRead>);

impl ReadPermission {
    /// Returns the path associated with the permission
    pub fn path(&self) -> &[u8] {
        &self.0
    }
}

/// Permission to write to a path
pub struct WritePermission(Vec<u8>, #[allow(dead_code)]ZipperTracker<TrackingWrite>);

impl WritePermission {
    /// Returns the path associated with the permission
    pub fn path(&self) -> &[u8] {
        &self.0
    }
}

/// A map to track statuses associated with all paths in the primary map.  See [StatusRecord]
pub struct StatusMap {
    trackers: SharedTrackerPaths,
    user_status: RwLock<BytesTrieMap<StatusRecord>>,
}

impl StatusMap {
    pub fn new() -> Self {

        //GOAT, Load the map from a file, so it persists across server starts.  Which also means
        // filtering out the temporary statuses, but leaving the permanant ones
        let user_status = BytesTrieMap::<StatusRecord>::new();

        Self {
            trackers: SharedTrackerPaths::default(),
            user_status: RwLock::new(user_status),
        }
    }

    /// Returns the status associated with a path or [StatusRecord::PathClear] if the path is not affected by any status
    pub fn get_status(&self, path: &[u8]) -> StatusRecord {
        match self.trackers.path_status(path) {
            PathStatus::Unavailable => {
                return StatusRecord::PathForbiddenTemporary
            },
            PathStatus::AvailableForReading => {
                return StatusRecord::PathReadOnlyTemporary
            },
            PathStatus::Available => {}
        }
        self.get_user_status(path)
    }

    /// Returns a [WritePermission] for the requested path and removes any a associated user
    /// statuses
    ///
    /// If an existign status cannot be removed then this method will fail.
    pub fn get_write_permission(&self, path: &[u8]) -> Result<WritePermission, BoxedErr> {
        let user_status = self.get_user_status(path);
        if user_status.blocks_writer() {
            return Err(format!("get_write_permission: encountered blocking status {user_status:?} at path {path:?}.").into())
        }
        self.clear_user_status(path)?;
        let tracker = ZipperTracker::<TrackingWrite>::new(self.trackers.clone(), path)?;
        Ok(WritePermission(path.to_vec(), tracker))
    }

    /// Returns a [WritePermission] for the requested path
    ///
    /// If an existign status cannot be removed then this method will fail.
    pub fn get_read_permission(&self, path: &[u8]) -> Result<ReadPermission, BoxedErr> {
        let user_status = self.get_user_status(path);
        if user_status.blocks_reader() {
            return Err(format!("get_read_permission: encountered blocking status {user_status:?} at path {path:?}.").into())
        }
        let tracker = ZipperTracker::<TrackingRead>::new(self.trackers.clone(), path)?;
        Ok(ReadPermission(path.to_vec(), tracker))
    }

    /// Attempts to set `new_status` at `path`.  Returns `Ok(())` if the status was sucessfully set, or
    /// `Err(old_status)` if an existing status affects the path
    pub fn try_set_user_status(&self, path: &[u8], new_status: StatusRecord) -> Result<(), StatusRecord> {

        //GOAT, Need a status priority lattice, and need to scan for conflicting statuses above and below the current path
        // let mut wz = self.zh.write_zipper_at_exclusive_path(path).map_err(|_conflict| StatusRecord::PathInUseForWrite)?;
        // let mut rz = wz.fork_read_zipper();
        // match self.find_status(&mut rz) {
        //     Some(old_status) => {
        //         if reset_path && old_status.can_reset() {
        //             //GOAT, this path copy could be avoided if / when I implement `ZipperIteration` on `WriteZipper` types
        //             let old_status_path = rz.path().to_vec();
        //             drop(rz);
        //             debug_assert!(wz.descend_to(old_status_path));
        //             wz.remove_value();
        //             drop(wz);
        //             return self.try_set_status(path, reset_path, new_status)
        //         } else {
        //             return Err(old_status)
        //         }
        //     },
        //     None => {
        //         drop(rz);
        //     }
        // }

        // wz.set_value(new_status);
        // Ok(())

        let mut user_map = self.user_status.write().unwrap();
        let mut zipper = user_map.write_zipper_at_path(path);
        zipper.set_value(new_status);
        Ok(())
    }

    /// Internal method. Returns the value from the user status map at the path
    fn get_user_status(&self, path: &[u8]) -> StatusRecord {
        let user_map = self.user_status.read().unwrap();
        user_map.get(path).cloned().unwrap_or(StatusRecord::PathClear)
    }

    /// Internal method. Clears the user status at the path
    fn clear_user_status(&self, path: &[u8]) -> Result<(), BoxedErr> {
        let mut user_map = self.user_status.write().unwrap();
        let mut zipper = user_map.write_zipper();
        zipper.descend_to(path);
        zipper.remove_branches();
        zipper.remove_value();
        Ok(())
    }
}
