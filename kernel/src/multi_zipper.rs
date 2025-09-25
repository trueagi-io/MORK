use crate::GetPathmap;
use pathmap::{
    arena_compact::{ACTMmapZipper, ACTVecZipper},
    utils::ByteMask,
    zipper::{
        PrefixZipper,
        ReadZipperTracked,
        ReadZipperUntracked,
        Zipper,
        ZipperAbsolutePath,
        ZipperConcrete,
        ZipperConcretePriv,
        ZipperForking,
        ZipperIteration,
        ZipperMoving,
        ZipperPathBuffer,
        ZipperReadOnlyConditionalValues,
        ZipperReadOnlyConditionalIteration,
        ZipperReadOnlyValues,
        ZipperValues,
    },
};

/// A combination of multiple kinds of zippers
///
/// Allows MORK space to do queries on heterogenous sources.
pub enum MultiZipper<'trie> {
    PathMap(ReadZipperTracked<'trie, 'trie, ()>),
    PathMapU(ReadZipperUntracked<'trie, 'trie, ()>),
    ACTMmap(PrefixZipper<'trie, ACTMmapZipper<'trie, ()>>),
    ACTVec(PrefixZipper<'trie, ACTVecZipper<'trie, ()>>),
}

impl<'trie> core::convert::Into<MultiZipper<'trie>> for ReadZipperTracked<'trie, 'trie, ()> {
    fn into(self) -> MultiZipper<'trie> {
        MultiZipper::PathMap(self)
    }
}

// impl<'trie> core::convert::Into<MultiZipper<'trie>> for ACTMmapZipper<'trie, ()> {
//     fn into(self) -> MultiZipper<'trie> {
//         MultiZipper::ACTMmap(self)
//     }
// }

// impl<'trie> core::convert::Into<MultiZipper<'trie>> for ACTVecZipper<'trie, ()> {
//     fn into(self) -> MultiZipper<'trie> {
//         MultiZipper::ACTVec(self)
//     }
// }

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

type WitnessOf<'trie, T> = <T as ZipperReadOnlyConditionalValues<'trie, ()>>::WitnessT;

pub enum MultiZipperWitness<'trie> {
    PathMap(WitnessOf<'trie, ReadZipperTracked<'trie, 'trie, ()>>),
    PathMapU(WitnessOf<'trie, ReadZipperUntracked<'trie, 'trie, ()>>),
    ACTMmap(WitnessOf<'trie, ACTMmapZipper<'trie, ()>>),
    ACTVec(WitnessOf<'trie, ACTVecZipper<'trie, ()>>),
}

impl<'trie> ZipperReadOnlyConditionalValues<'trie, ()> for MultiZipper<'trie> {
    type WitnessT = MultiZipperWitness<'trie>;
    fn witness<'w>(&self) -> Self::WitnessT {
        match self {
            Self::PathMap(pm) => MultiZipperWitness::PathMap(pm.witness()),
            Self::PathMapU(pm) => MultiZipperWitness::PathMapU(pm.witness()),
            Self::ACTMmap(act) => MultiZipperWitness::ACTMmap(act.witness()),
            Self::ACTVec(act) => MultiZipperWitness::ACTVec(act.witness()),
        }
    }
    fn get_val_with_witness<'w>(&self, witness: &'w Self::WitnessT) -> Option<&'w ()> where 'trie: 'w {
        match (self, witness) {
            (Self::PathMap(pm), MultiZipperWitness::PathMap(w)) => pm.get_val_with_witness(w),
            (Self::PathMapU(pm), MultiZipperWitness::PathMapU(w)) => pm.get_val_with_witness(w),
            (Self::ACTMmap(act), MultiZipperWitness::ACTMmap(w)) => act.get_val_with_witness(w),
            (Self::ACTVec(act), MultiZipperWitness::ACTVec(w)) => act.get_val_with_witness(w),
            _ => None,
        }
    }
}

impl<'trie> ZipperValues<()> for MultiZipper<'trie> {
    fn val(&self) -> Option<&()> {
        match self {
            Self::PathMap(pm) => pm.val(),
            Self::PathMapU(pm) => pm.val(),
            Self::ACTMmap(act) => act.val(),
            Self::ACTVec(act) => act.val(),
        }
    }
}

impl<'trie> ZipperReadOnlyValues<'trie, ()> for MultiZipper<'trie> {
    fn get_val(&self) -> Option<&'trie ()> {
        match self {
            Self::PathMap(pm) => pm.get_val(),
            Self::PathMapU(pm) => pm.get_val(),
            Self::ACTMmap(act) => act.get_val(),
            Self::ACTVec(act) => act.get_val(),
        }
    }
}

impl<'trie> ZipperConcretePriv for MultiZipper<'trie> {
    fn shared_node_id(&self) -> Option<u64> {
        match self {
            Self::PathMap(pm) => pm.shared_node_id(),
            Self::PathMapU(pm) => pm.shared_node_id(),
            Self::ACTMmap(act) => act.shared_node_id(),
            Self::ACTVec(act) => act.shared_node_id(),
        }
    }
}

impl<'trie> Zipper for MultiZipper<'trie> {
    fn path_exists(&self) -> bool {
        match self {
            Self::PathMap(pm) => pm.path_exists(),
            Self::PathMapU(pm) => pm.path_exists(),
            Self::ACTMmap(act) => act.path_exists(),
            Self::ACTVec(act) => act.path_exists(),
        }
    }
    fn is_val(&self) -> bool {
        match self {
            Self::PathMap(pm) => pm.is_val(),
            Self::PathMapU(pm) => pm.is_val(),
            Self::ACTMmap(act) => act.is_val(),
            Self::ACTVec(act) => act.is_val(),
        }
    }
    fn child_count(&self) -> usize {
        match self {
            Self::PathMap(pm) => pm.child_count(),
            Self::PathMapU(pm) => pm.child_count(),
            Self::ACTMmap(act) => act.child_count(),
            Self::ACTVec(act) => act.child_count(),
        }
    }
    fn child_mask(&self) -> ByteMask {
        match self {
            Self::PathMap(pm) => pm.child_mask(),
            Self::PathMapU(pm) => pm.child_mask(),
            Self::ACTMmap(act) => act.child_mask(),
            Self::ACTVec(act) => act.child_mask(),
        }
    }
}

impl<'trie> ZipperConcrete for MultiZipper<'trie> {
    fn is_shared(&self) -> bool {
        match self {
            Self::PathMap(pm) => pm.is_shared(),
            Self::PathMapU(pm) => pm.is_shared(),
            Self::ACTMmap(act) => act.is_shared(),
            Self::ACTVec(act) => act.is_shared(),
        }
    }
}

impl<'trie> ZipperMoving for MultiZipper<'trie> {
    fn val_count(&self) -> usize {
        match self {
            Self::PathMap(pm) => pm.val_count(),
            Self::PathMapU(pm) => pm.val_count(),
            Self::ACTMmap(act) => act.val_count(),
            Self::ACTVec(act) => act.val_count(),
        }
    }
    fn path(&self) -> &[u8] {
        match self {
            Self::PathMap(pm) => pm.path(),
            Self::PathMapU(pm) => pm.path(),
            Self::ACTMmap(act) => act.path(),
            Self::ACTVec(act) => act.path(),
        }
    }
    fn descend_to<K: AsRef<[u8]>>(&mut self, path: K) -> bool {
        match self {
            Self::PathMap(pm) => pm.descend_to(path),
            Self::PathMapU(pm) => pm.descend_to(path),
            Self::ACTMmap(act) => act.descend_to(path),
            Self::ACTVec(act) => act.descend_to(path),
        }
    }
    fn ascend(&mut self, n: usize) -> bool {
        match self {
            Self::PathMap(pm) => pm.ascend(n),
            Self::PathMapU(pm) => pm.ascend(n),
            Self::ACTMmap(act) => act.ascend(n),
            Self::ACTVec(act) => act.ascend(n),
        }
    }
    fn ascend_until(&mut self) -> bool {
        match self {
            Self::PathMap(pm) => pm.ascend_until(),
            Self::PathMapU(pm) => pm.ascend_until(),
            Self::ACTMmap(act) => act.ascend_until(),
            Self::ACTVec(act) => act.ascend_until(),
        }
    }
    fn ascend_until_branch(&mut self) -> bool {
        match self {
            Self::PathMap(pm) => pm.ascend_until_branch(),
            Self::PathMapU(pm) => pm.ascend_until_branch(),
            Self::ACTMmap(act) => act.ascend_until_branch(),
            Self::ACTVec(act) => act.ascend_until_branch(),
        }
    }
}

impl<'trie> ZipperIteration for MultiZipper<'trie> {

}

impl ZipperForking<()> for MultiZipper<'_> {
    type ReadZipperT<'t> = MultiZipper<'t> where Self: 't;
    fn fork_read_zipper<'a>(&'a self) -> MultiZipper<'a>
    {
        match self {
            Self::PathMap(pm) => MultiZipper::PathMapU(pm.fork_read_zipper()),
            Self::PathMapU(pm) => MultiZipper::PathMapU(pm.fork_read_zipper()),
            Self::ACTMmap(act) => MultiZipper::ACTMmap(act.fork_read_zipper()),
            Self::ACTVec(act) => MultiZipper::ACTVec(act.fork_read_zipper()),
        }
    }
}
impl<'trie> ZipperReadOnlyConditionalIteration<'trie, ()> for MultiZipper<'trie> {

}

impl<'trie> ZipperAbsolutePath for MultiZipper<'trie> {
    fn origin_path(&self) -> &[u8] {
        match self {
            Self::PathMap(pm) => pm.origin_path(),
            Self::PathMapU(pm) => pm.origin_path(),
            Self::ACTMmap(act) => act.origin_path(),
            Self::ACTVec(act) => act.origin_path(),
        }
    }
    fn root_prefix_path(&self) -> &[u8] {
        match self {
            Self::PathMap(pm) => pm.root_prefix_path(),
            Self::PathMapU(pm) => pm.root_prefix_path(),
            Self::ACTMmap(act) => act.root_prefix_path(),
            Self::ACTVec(act) => act.root_prefix_path(),
        }
    }
}

impl<'trie> ZipperPathBuffer for MultiZipper<'trie> {
    unsafe fn origin_path_assert_len(&self, len: usize) -> &[u8] {
        match self {
            Self::PathMap(pm) => pm.origin_path_assert_len(len),
            Self::PathMapU(pm) => pm.origin_path_assert_len(len),
            Self::ACTMmap(act) => act.origin_path_assert_len(len),
            Self::ACTVec(act) => act.origin_path_assert_len(len),
        }
    }
    fn prepare_buffers(&mut self) {
        match self {
            Self::PathMap(pm) => pm.prepare_buffers(),
            Self::PathMapU(pm) => pm.prepare_buffers(),
            Self::ACTMmap(act) => act.prepare_buffers(),
            Self::ACTVec(act) => act.prepare_buffers(),
        }
    }
    fn reserve_buffers(&mut self, path_len: usize, stack_depth: usize) {
        match self {
            Self::PathMap(pm) => pm.reserve_buffers(path_len, stack_depth),
            Self::PathMapU(pm) => pm.reserve_buffers(path_len, stack_depth),
            Self::ACTMmap(act) => act.reserve_buffers(path_len, stack_depth),
            Self::ACTVec(act) => act.reserve_buffers(path_len, stack_depth),
        }
    }
}
