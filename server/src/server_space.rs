
use hyper::StatusCode;

use pathmap::{trie_map::BytesTrieMap, zipper::ZipperHeadOwned};
use pathmap::zipper::*;

use mork::{Space, path_as_bytes, Path};

use crate::status_map::*;
use crate::commands::*;

pub struct ServerSpace {
    /// The global symbol table used by the primary map
    global_symbol_table: bucket_map::SharedMappingHandle,
    /// ZipperHead for accessing the primary map
    primary_map: ZipperHeadOwned<()>,
    /// ZipperHead for accessing status and permissions associated with paths
    status_map: StatusMap,
}

impl ServerSpace {
    /// Make a new `ServerSpace`, loading it from the snapshot
    pub fn new() -> Self {

        // Load the PathMap from the last snapshot
        //GOAT, ACTually load it!!
        let primary_map = BytesTrieMap::<()>::new();
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
            status_map: status_map
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
}


impl Space for ServerSpace {
    type Auth = ();
    type Reader<'space> = ReadPermission;
    type Writer<'space> = WritePermission;
    type PermissionErr = CommandError;

    fn new_reader<'space>(&'space self, path: &Path, _auth: &Self::Auth) -> Result<Self::Reader<'space>, Self::PermissionErr> {
        let path = path_as_bytes(path);
        self.status_map.get_read_permission(&path).map_err(|e| CommandError::External(ExternalError::new(StatusCode::UNAUTHORIZED, format!("Error accessing path: {e:?}"))))
    }
    fn new_writer<'space>(&'space self, path: &Path, _auth: &Self::Auth) -> Result<Self::Writer<'space>, Self::PermissionErr> {
        let path = path_as_bytes(path);
        self.status_map.get_write_permission(&path).map_err(|e| CommandError::External(ExternalError::new(StatusCode::UNAUTHORIZED, format!("Error accessing path: {e:?}"))))
    }
    fn read_zipper<'r, 's: 'r>(&'s self, reader: &'r mut Self::Reader<'s>) -> impl  ZipperMoving + ZipperReadOnly<'s, ()> + ZipperIteration<'s, ()> + ZipperAbsolutePath + 'r {
        unsafe{ self.primary_map.read_zipper_at_borrowed_path_unchecked(reader.path()) }
    }
    fn write_zipper<'w, 's: 'w>(&'s self, writer: &'w mut Self::Writer<'s>) -> impl ZipperMoving + ZipperWriting<()> + 'w {
        unsafe{ self.primary_map.write_zipper_at_exclusive_path_unchecked(writer.path()) }
    }
    fn symbol_table(&self) -> &bucket_map::SharedMappingHandle {
        &self.global_symbol_table
    }

}