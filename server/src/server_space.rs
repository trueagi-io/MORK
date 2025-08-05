
use std::time::Duration;
use std::sync::Mutex;

use hyper::StatusCode;

use pathmap::{PathMap, zipper::ZipperHeadOwned};
use pathmap::zipper_tracking::Conflict;
use pathmap::zipper::*;

use mork::{PermissionArb, PathPermissionErr, Space, SpaceReaderZipper, SpaceWriterZipper};

use crate::status_map::*;
use crate::commands::*;

/// The time to wait before rejecting a request with a conflicted path
const SETTLE_TIME: Duration = Duration::from_millis(5);

pub struct ServerSpace {
    /// The global symbol table used by the primary map
    global_symbol_table: bucket_map::SharedMappingHandle,
    /// ZipperHead for accessing the primary map
    primary_map: ZipperHeadOwned<()>,
    /// ZipperHead for accessing status and permissions associated with paths
    pub(crate) status_map: StatusMap,
    /// Guard to ensure high-level operations can be atomic
    permission_guard: Mutex<()>,
}

/// PermissionHead object for [ServerSpace]
pub struct ServerPermissionHead<'space>(&'space ServerSpace);

impl ServerSpace {
    /// Make a new `ServerSpace`, loading it from the snapshot
    pub fn new() -> Self {

        // Load the PathMap from the last snapshot
        //GOAT, ACTually load it!!
        let primary_map = PathMap::<()>::new();
        let primary_map = primary_map.into_zipper_head([]);

        // Load the status map also
        //GOAT, Load this from the snapshot
        let status_map = StatusMap::new();

        // init symbol table
        //GOAT, Load this from the snapshot
        let global_symbol_table = bucket_map::SharedMapping::new();

        Self {
            global_symbol_table,
            primary_map,
            status_map: status_map,
            permission_guard: Mutex::new(()),
        }
    }
    pub fn get_status<P: AsRef<[u8]>>(&self, path: P) -> StatusRecord {
        self.status_map.get_status(path.as_ref())
    }
    pub fn set_user_status<P: AsRef<[u8]>>(&self, path: P, new_status: StatusRecord) -> Result<(), CommandError> {
        let path = path.as_ref();
        self.status_map.try_set_user_status(path, new_status)
            .map_err(|err_status_rec| CommandError::External(ExternalError::new(StatusCode::UNAUTHORIZED, format!("Conflicting status: {err_status_rec:?} at path: {path:?} when attempting to set new status"))))
    }
    /// Wrapper around direct method to acquire WritePermission, waiting SETTLE_TIME for previous requests to
    /// settle before rejecting the request
    pub async fn new_writer_async<'space>(&'space self, path: &[u8], auth: &()) -> Result<WritePermission, ServerPermissionErr> {
        match self.new_writer(path, auth) {
            Ok(perm) => Ok(perm),
            Err(_) => {
                tokio::time::sleep(SETTLE_TIME).await;
                self.new_writer(path, auth)
            }
        }
    }
    /// See `new_writer_async`
    pub async fn new_reader_async<'space>(&'space self, path: &[u8], auth: &()) -> Result<ReadPermission, ServerPermissionErr> {
        match self.new_reader(path, auth) {
            Ok(perm) => Ok(perm),
            Err(_) => {
                tokio::time::sleep(SETTLE_TIME).await;
                self.new_reader(path, auth)
            }
        }
    }
}

impl<'space> PermissionArb<'space, ServerSpace> for ServerPermissionHead<'space> {
    fn new_reader(&self, path: &[u8], _auth: &()) -> Result<ReadPermission, ServerPermissionErr> {
        self.0.status_map.get_read_permission(&path)
    }

    /// Requests a new [Space::Writer] from the `Space`
    fn new_writer(&self, path: &[u8], _auth: &()) -> Result<WritePermission, ServerPermissionErr> {
        self.0.status_map.get_write_permission(&path)
    }
}

/// [PathPermissionErr] in a [ServerSpace]
#[derive(Debug)]
pub struct ServerPermissionErr {
    path: Vec<u8>,
    message: String,
}

impl ServerPermissionErr {
    pub fn new(path: &[u8], message: String) -> Self {
        Self {path: path.to_vec(), message}
    }
    pub fn from_conflict(conflict: Conflict, path: &[u8]) -> Self {
        let nice_path = mork_bytestring::serialize(path);
        let nice_existing_path = mork_bytestring::serialize(conflict.path());
        Self {
            path: path.to_vec(),
            message: format!("{conflict} trying to take path: `{nice_path}` while `{nice_existing_path}` was already taken")
        }
    }
}

impl From<ServerPermissionErr> for CommandError {
    fn from(perm_err: ServerPermissionErr) -> Self {
        CommandError::External(ExternalError::new(StatusCode::UNAUTHORIZED, format!("Permission error accessing path: {perm_err:?}")))
    }
}

impl PathPermissionErr for ServerPermissionErr {
    fn path(&self) -> &[u8] {
        &self.path
    }
}

impl core::fmt::Display for ServerPermissionErr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        self.message.fmt(f)
    }
}

impl Space for ServerSpace {
    type Auth = ();
    type Reader<'space> = ReadPermission;
    type Writer<'space> = WritePermission;
    type PermissionHead<'space> = ServerPermissionHead<'space>;
    type PermissionErr = ServerPermissionErr;

    fn new_multiple<'space, F: FnOnce(&Self::PermissionHead<'space>)->Result<(), Self::PermissionErr>>(&'space self, f: F) -> Result<(), Self::PermissionErr> {
        let guard = self.permission_guard.lock().unwrap();
        let perm_head = ServerPermissionHead(self);
        f(&perm_head)?;
        drop(guard);
        Ok(())
    }
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl SpaceReaderZipper<'s> {
        unsafe{ self.primary_map.read_zipper_at_borrowed_path_unchecked(reader.path()) }
    }
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl SpaceWriterZipper + 'w {
        unsafe{ self.primary_map.write_zipper_at_exclusive_path_unchecked(writer.path()) }
    }
    fn cleanup_write_zipper(&self, wz: impl SpaceWriterZipper) {
        self.primary_map.cleanup_write_zipper(wz);
    }
    fn symbol_table(&self) -> &bucket_map::SharedMappingHandle {
        &self.global_symbol_table
    }

}