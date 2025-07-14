
use std::sync::{RwLock, Arc};
use serde::{Serialize, Serializer};

use pathmap::PathMap;
use pathmap::zipper::{ZipperWriting, ZipperMoving};
use pathmap::zipper_tracking::{PathStatus, SharedTrackerPaths, ZipperTracker, TrackingRead, TrackingWrite};

use hyper::StatusCode;

use crate::ServerPermissionErr;

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
    ExecError(String)
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
            Self::ExecError(_) => false,
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
            Self::FetchError(_) => false,
            Self::ParseError(_) => false,
            Self::ExecError(_) => false,
        }
    }
}

/// Permission to read from a path
pub struct ReadPermission(Vec<u8>, StatusMap, Option<ZipperTracker<TrackingRead>>);

impl ReadPermission {
    /// Returns the path associated with the permission
    pub fn path(&self) -> &[u8] {
        &self.0
    }
}

impl Drop for ReadPermission {
    fn drop(&mut self) {
        let tracker = core::mem::take(&mut self.2);
        drop(tracker);
        self.1.send_new_status(&self.0);
    }
}

/// Permission to write to a path
pub struct WritePermission(Vec<u8>, StatusMap, Option<ZipperTracker<TrackingWrite>>);

impl WritePermission {
    /// Returns the path associated with the permission
    pub fn path(&self) -> &[u8] {
        &self.0
    }
}

impl Drop for WritePermission {
    fn drop(&mut self) {
        let tracker = core::mem::take(&mut self.2);
        drop(tracker);
        self.1.send_new_status(&self.0);
    }
}

/// A map to track statuses associated with all paths in the primary map.  See [StatusRecord]
#[derive(Clone)]
pub struct StatusMap(Arc<StatusMapFields>);

/// Fields within the [StatusMap]
struct StatusMapFields {
    trackers: SharedTrackerPaths,
    user_status: RwLock<PathMap<StatusRecord>>,
    streams: RwLock<PathMap<Vec<(u64, tokio::sync::mpsc::Sender<StatusRecord>)>>>,
}

impl StatusMap {
    pub fn new() -> Self {

        //GOAT, Load the map from a file, so it persists across server starts.  Which also means
        // filtering out the temporary statuses, but leaving the permanant ones
        let user_status = PathMap::<StatusRecord>::new();

        let steams = PathMap::new();

        let fields = StatusMapFields {
            trackers: SharedTrackerPaths::default(),
            user_status: RwLock::new(user_status),
            streams: RwLock::new(steams),
        };
        Self(Arc::new(fields))
    }

    /// Returns the status associated with a path or [StatusRecord::PathClear] if the path is not affected by any status
    pub fn get_status(&self, path: &[u8]) -> StatusRecord {
        match self.0.trackers.path_status(path) {
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

    /// Adds the sender end of a stream's channel to the `StatusMap`'s streams table
    pub fn add_stream(&self, path: &[u8], stream_id: u64, sender: tokio::sync::mpsc::Sender<StatusRecord>) {
        let mut guard = self.0.streams.write().unwrap();
        let senders_vec = guard.get_value_mut_or_set_with(path, || vec![]);
        senders_vec.push((stream_id, sender));
    }

    /// Removes the stream from the `StatusMap`'s streams table
    pub fn remove_stream(&self, path: &[u8], stream_id: u64) {
        let mut guard = self.0.streams.write().unwrap();
        let senders_vec = guard.get_val_mut_at(path).unwrap();
        if let Some(pos) = senders_vec.iter().position(|(map_stream_id, _)| *map_stream_id == stream_id) {
            senders_vec.remove(pos);
        }
    }

    /// Sends the new status to all streams listening for it.  If a stream is closed, then it is immediately
    /// removed from the streams table
    fn send_new_status(&self, path: &[u8]) {
        let mut should_remove = vec![];
        let guard = self.0.streams.read().unwrap();
        if let Some(streams_vec) = guard.get_val_at(path) {
            let new_status = self.get_status(path);

            for (stream_id, stream_tx) in streams_vec.iter() {
                match stream_tx.try_send(new_status.clone()) {
                    Ok(()) => {},
                    Err(err) => {
                        if matches!(err, tokio::sync::mpsc::error::TrySendError::Closed(_)) {
                            should_remove.push(*stream_id);
                        }
                    }
                }
            }
        }
        drop(guard);

        //See if we need to remove any streams because they were closed
        for stream_id in should_remove {
            self.remove_stream(path, stream_id);
        }
    }

    /// Returns a [WritePermission] for the requested path and removes any associated user
    /// statuses
    ///
    /// If an existign status cannot be removed then this method will fail.
    pub fn get_write_permission(&self, path: &[u8]) -> Result<WritePermission, ServerPermissionErr> {
        let user_status = self.get_user_status(path);
        if user_status.blocks_writer() {
            return Err(ServerPermissionErr::new(path, format!("get_write_permission: encountered blocking status {user_status:?} at path {path:?}.")))
        }
        self.clear_user_status(path)?;
        let tracker = ZipperTracker::<TrackingWrite>::new(self.0.trackers.clone(), path)
            .map_err(|conflict| ServerPermissionErr::from_conflict(conflict, path))?;

        //Send the status to any streams monitoring this path
        self.send_new_status(path);

        Ok(WritePermission(path.to_vec(), self.clone(), Some(tracker)))
    }

    /// Returns a [WritePermission] for the requested path
    ///
    /// If an existign status cannot be removed then this method will fail.
    pub fn get_read_permission(&self, path: &[u8]) -> Result<ReadPermission, ServerPermissionErr> {
        let user_status = self.get_user_status(path);
        if user_status.blocks_reader() {
            return Err(ServerPermissionErr::new(path, format!("get_read_permission: encountered blocking status {user_status:?} at path {path:?}.")))
        }
        let tracker = ZipperTracker::<TrackingRead>::new(self.0.trackers.clone(), path)
            .map_err(|conflict| ServerPermissionErr::from_conflict(conflict, path))?;

        //Send the status to any streams monitoring this path
        self.send_new_status(path);

        Ok(ReadPermission(path.to_vec(), self.clone(), Some(tracker)))
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

        let mut user_map = self.0.user_status.write().unwrap();
        let mut zipper = user_map.write_zipper_at_path(path);
        zipper.set_value(new_status);

        //Send the status to any streams monitoring this path
        self.send_new_status(path);

        Ok(())
    }

    /// Internal method. Returns the value from the user status map at the path
    fn get_user_status(&self, path: &[u8]) -> StatusRecord {
        let user_map = self.0.user_status.read().unwrap();
        user_map.get_val_at(path).cloned().unwrap_or(StatusRecord::PathClear)
    }

    /// Internal method. Clears the user status at the path
    fn clear_user_status(&self, path: &[u8]) -> Result<(), ServerPermissionErr> {
        let mut user_map = self.0.user_status.write().unwrap();
        let mut zipper = user_map.write_zipper();
        zipper.descend_to(path);
        zipper.remove_branches();
        zipper.remove_value();
        Ok(())
    }
}
