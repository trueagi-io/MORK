use crate::GetPathmap;
use pathmap::{
    arena_compact::{ACTMmapZipper, ACTVecZipper},
    zipper::{
        PolyZipper,
        PrefixZipper,
        ReadZipperTracked,
        ReadZipperUntracked,
        ZipperForking,
    },
};

#[derive(PolyZipper)]
pub enum MultiZipper<'trie, V: Clone + Send + Sync + Unpin = ()> {
    /// Tracked PathMap read zipper
    PathMap(ReadZipperTracked<'trie, 'trie, V>),
    /// Unracked PathMap read zipper.
    /// The reason this exists is to allow forking the zipper.
    /// Forking a Tracked read zipper return an Untracked read zipper.
    PathMapU(ReadZipperUntracked<'trie, 'trie, V>),
    /// Memory-mapped ACT.
    /// Prefix is necessary here such that MORK can see ACT under a specific path
    ACTMmapPrefix(PrefixZipper<'trie, ACTMmapZipper<'trie, V>>),
    /// `Vec<u8>` based ACT
    /// Prefix is necessary here such that MORK can see ACT under a specific path
    ACTVecPrefix(PrefixZipper<'trie, ACTVecZipper<'trie, V>>),
}

impl<'trie> ZipperForking<()> for MultiZipper<'trie, ()>
{
    type ReadZipperT<'a> = MultiZipper<'a, ()> where Self: 'a;
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a>
    {
        match self {
            Self::PathMap(pm) => MultiZipper::PathMapU(pm.fork_read_zipper()),
            Self::PathMapU(pm) => MultiZipper::PathMapU(pm.fork_read_zipper()),
            Self::ACTMmapPrefix(act) => MultiZipper::ACTMmapPrefix(act.fork_read_zipper()),
            Self::ACTVecPrefix(act) => MultiZipper::ACTVecPrefix(act.fork_read_zipper()),
        }
    }
}

impl<'trie> GetPathmap<'trie> for &mut MultiZipper<'trie> {
    fn get_pathmap(&self) -> Option<&ReadZipperTracked<'trie, 'trie, ()>> {
        <MultiZipper as GetPathmap>::get_pathmap(self)
    }
}

impl<'trie> GetPathmap<'trie> for MultiZipper<'trie> {
    fn get_pathmap(&self) -> Option<&ReadZipperTracked<'trie, 'trie, ()>> {
        match self {
            Self::PathMap(pm) => Some(pm),
            _ => None,
        }
    }
}
