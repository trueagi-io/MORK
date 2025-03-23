
use serde::{Serialize, Serializer};

use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{ZipperAccess, ZipperWriting, ZipperMoving, ZipperCreation, ZipperHeadOwned, ZipperIteration};

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
    CountResult(CountResult),
    // PathInUseForRead,
    // PathInUseForWrite,
    PathInUse, //GOAT, need to track read and write separately so two commands reading the same path don't conflict!!, and make sure we actually do correct exclusivity checking
    AccessForbidden,
    FetchError(FetchError),
    ParseError(ParseError),
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
    /// Some status types can be reset by some operations; others can't.
    ///
    /// For example, a `PriorError` on a path can be overwritten by another operation that is going to
    /// write to that path, but not by an operation that is going to read from that path.
    fn can_reset(&self) -> bool {
        match self {
            Self::PathClear => true,
            Self::CountResult(_) => true,
            // Self::PathInUseForRead => false,
            // Self::PathInUseForWrite => false,
            Self::PathInUse => false,
            Self::AccessForbidden => false,
            Self::FetchError(_) => true,
            Self::ParseError(_) => true,
        }
    }
}

/// A map to track statuses associated with all paths in the primary map.  See [StatusRecord]
pub struct StatusMap {
    zh: ZipperHeadOwned<StatusRecord>
}

impl StatusMap {
    pub fn new() -> Self {

        //GOAT, Load the map from a file, so it persists across server starts.  Which also means
        // filtering out the temporary statuses, but leaving the permanant ones
        let map = BytesTrieMap::<StatusRecord>::new();

        Self {
            zh: map.into_zipper_head([])
        }
    }

    /// Returns the status associated with a path or `None` if the path is not affected by any status
    pub fn get_status(&self, path: &[u8]) -> StatusRecord {
        match self.zh.read_zipper_at_borrowed_path(path) {
            Ok(mut z) => self.find_status(&mut z).unwrap_or(StatusRecord::PathClear),
            Err(_conflict) => StatusRecord::PathInUse,
        }
    }

    /// Attempts to set `new_status` at `path`.  Returns `Ok(())` if the status was sucessfully set, or
    /// `Err(old_status)` if an existing status affects the path
    pub fn try_set_status(&self, path: &[u8], reset_path: bool, new_status: StatusRecord) -> Result<(), StatusRecord> {

        let mut wz = self.zh.write_zipper_at_exclusive_path(path).map_err(|_conflict| StatusRecord::PathInUse)?;
        let mut rz = wz.fork_read_zipper();
        match self.find_status(&mut rz) {
            Some(old_status) => {
                if reset_path && old_status.can_reset() {
                    //GOAT, this path copy could be avoided if / when I implement `ZipperIteration` on `WriteZipper` types
                    let old_status_path = rz.path().to_vec();
                    drop(rz);
                    debug_assert!(wz.descend_to(old_status_path));
                    wz.remove_value();
                    drop(wz);
                    return self.try_set_status(path, reset_path, new_status)
                } else {
                    return Err(old_status)
                }
            },
            None => {
                drop(rz);
            }
        }

        wz.set_value(new_status);
        Ok(())
    }

    /// Sets the status in the map to affect a future operation
    pub fn set_status(&self, path: &[u8], new_status: StatusRecord, expected_status: StatusRecord) -> Result<(), BoxedErr> {
        let mut wz = self.zh.write_zipper_at_exclusive_path(path)?;
        match wz.set_value(new_status) {
            Some(old_status) => {
                if old_status != expected_status {
                    return Err(format!("set_status: expected {expected_status:?} but found {old_status:?}.  path: {path:?}").into())
                }
            },
            None => {}
        }
        Ok(())
    }

    /// Clears the status at the path
    pub fn clear_status(&self, path: &[u8]) -> Result<(), BoxedErr> {
        let mut wz = self.zh.write_zipper_at_exclusive_path(path)?;
        match wz.remove_value() {
            Some(_) => Ok(()),
            None => Err(format!("clear_status: expected status record but found nothing at path: {path:?}").into())
        }
    }

    /// Internal method to Scan upwards from the zipper looking for the first [StatusRecord].  If `None`
    /// is returned then the path below the zipper is unencumbered
    fn find_status<'a, Z: ZipperIteration<'a, StatusRecord> + ZipperAccess<StatusRecord>>(&self, z: &mut Z) -> Option<StatusRecord> {
        if let Some(val) = z.value() {
            return Some(val.clone())
        }
        if let Some(val) = z.to_next_val() {
            return Some(val.clone())
        }
        None
    }
}
