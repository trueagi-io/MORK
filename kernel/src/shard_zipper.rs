//! ShardZipper: cost-bounded prefix decomposition of a pathspace into
//! locally-sweepable shards, with O(1) copy-on-write capture and reintegration.
//!
//! This is the substrate from Goertzel's ShardZipper note (2025). A massive
//! metagraph lives as a byte trie too large for one compute unit's fast memory,
//! so dense work runs as local sweeps over small shards. A shard is the subtrie
//! under a key prefix. The four pieces of the note map directly onto PathMap:
//!
//! - distribution-aware prefix decomposition: [`decompose_by_cost`] descends the
//!   trie and emits a prefix as a shard once its value count drops to a budget
//!   `l_max`, the cost `L(s)` the note bounds. The prefixes form a covering
//!   antichain (see the PrefixAntichain Verus proof).
//! - delimited-continuation zipper C_k: [`capture`] detaches the shard at a
//!   prefix as a standalone map via the write zipper's `take_map`. What stays is
//!   the rest of the trie. PathMap's copy-on-write keeps this O(prefix) plus
//!   shared-node refcount bumps, not O(shard).
//! - the continuation Gamma_s: [`reintegrate`] splices a (possibly updated)
//!   shard back in at the same prefix via `graft_map`, preserving all sharing in
//!   the rest of the DAG.
//! - the composite update Phi_s = Gamma_s . K . pi2 . C_k: [`sweep_shard`]
//!   captures, runs a locally-sweepable kernel that returns a bounded
//!   [`PatchLog`], replays the log, and reintegrates.
//!
//! Keys inside a captured shard are relative to the shard root (the suffixes
//! after the prefix), so a local sweep and its patch log see exactly the
//! detached subtree, never the global key. Decomposition assumes a prefix-free
//! key set (MORK's complete, self-delimiting expressions), so every value sits
//! at a leaf and the frontier covers all values; a value at an internal node
//! that cannot be split off by prefix is emitted as its own over-budget shard.

use pathmap::PathMap;
use pathmap::zipper::*;

/// Cost L(s) of the shard at `prefix`: the number of values under it. A proxy
/// for the materialised buffer size or the count of rule instantiations the
/// note measures local-sweepability in.
pub fn shard_cost(map: &PathMap<()>, prefix: &[u8]) -> usize {
    map.read_zipper_at_path(prefix).val_count()
}

/// Distribution-aware prefix decomposition. Returns a frontier of prefixes whose
/// shards each hold at most `l_max` values and together cover every value in the
/// map. Descends the trie, emitting a prefix once its subtree drops to the
/// budget. `l_max` must be at least one.
pub fn decompose_by_cost(map: &PathMap<()>, l_max: usize) -> Vec<Vec<u8>> {
    assert!(l_max >= 1, "shard budget must be at least one value");
    let mut out = Vec::new();
    let mut prefix = Vec::new();
    frontier(map, &mut prefix, l_max, &mut out);
    out
}

fn frontier(map: &PathMap<()>, prefix: &mut Vec<u8>, l_max: usize, out: &mut Vec<Vec<u8>>) {
    let (count, children) = {
        let rz = map.read_zipper_at_path(&prefix[..]);
        let count = rz.val_count();
        let children: Vec<u8> = if count > l_max {
            rz.child_mask().iter().collect()
        } else {
            Vec::new()
        };
        (count, children)
    };
    if count == 0 {
        return;
    }
    if count <= l_max {
        out.push(prefix.clone());
        return;
    }
    if children.is_empty() {
        // Over budget but unsplittable: a value sits at this internal node (the
        // key is a proper prefix of others). Emit it as its own shard.
        out.push(prefix.clone());
        return;
    }
    for b in children {
        prefix.push(b);
        frontier(map, prefix, l_max, out);
        prefix.pop();
    }
}

/// Capture C_k(T, s): detach the shard at `prefix`, returning it as a standalone
/// map whose keys are relative to the prefix. The map keeps the rest of the
/// trie. Reintegrate splices a shard back at the same prefix.
pub fn capture(map: &mut PathMap<()>, prefix: &[u8]) -> PathMap<()> {
    let mut wz = map.write_zipper_at_path(prefix);
    wz.take_map(false).unwrap_or_default()
}

/// Reintegrate Gamma_s(X): splice shard `shard` back in at `prefix`.
pub fn reintegrate(map: &mut PathMap<()>, prefix: &[u8], shard: PathMap<()>) {
    let mut wz = map.write_zipper_at_path(prefix);
    wz.graft_map(shard);
}

/// One structural edit in a shard's patch log, keyed relative to the shard root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Patch {
    Insert(Vec<u8>),
    Remove(Vec<u8>),
}

/// Append-only patch log of structural edits a kernel makes to a shard. Its size
/// is proportional to the number of edits, never the shard size, so it stays
/// small even for a large read-mostly shard. The host replays it before
/// reintegration.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PatchLog {
    ops: Vec<Patch>,
}

impl PatchLog {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record an inserted key (relative to the shard root).
    pub fn insert(&mut self, key: Vec<u8>) {
        self.ops.push(Patch::Insert(key));
    }

    /// Record a retracted key (relative to the shard root).
    pub fn remove(&mut self, key: Vec<u8>) {
        self.ops.push(Patch::Remove(key));
    }

    pub fn len(&self) -> usize {
        self.ops.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    pub fn ops(&self) -> &[Patch] {
        &self.ops
    }

    /// Replay the log onto a shard, in order.
    pub fn apply(&self, shard: &mut PathMap<()>) {
        for op in &self.ops {
            match op {
                Patch::Insert(key) => {
                    shard.insert(key, ());
                }
                Patch::Remove(key) => {
                    shard.remove(key);
                }
            }
        }
    }
}

/// One ShardZipper step Phi_s = Gamma_s . K . pi2 . C_k: capture the shard at
/// `prefix`, run the locally-sweepable kernel on it (it returns the structural
/// edits as a patch log), replay the log, and reintegrate. The kernel sees the
/// shard with shard-relative keys, exactly the detached subtree.
pub fn sweep_shard<K>(map: &mut PathMap<()>, prefix: &[u8], kernel: K)
where
    K: FnOnce(&PathMap<()>) -> PatchLog,
{
    let mut shard = capture(map, prefix);
    let patch = kernel(&shard);
    patch.apply(&mut shard);
    reintegrate(map, prefix, shard);
}

/// The whole pipeline over every shard, sequentially. Decompose at `l_max`, then
/// for each shard capture, run the kernel, replay its patch log, and
/// reintegrate. The kernel is handed the shard prefix and the shard (with
/// shard-relative keys).
pub fn sweep_all<K>(map: &mut PathMap<()>, l_max: usize, kernel: K)
where
    K: Fn(&[u8], &PathMap<()>) -> PatchLog,
{
    let prefixes = decompose_by_cost(map, l_max);
    for prefix in prefixes {
        let mut shard = capture(map, &prefix);
        let log = kernel(&prefix, &shard);
        log.apply(&mut shard);
        reintegrate(map, &prefix, shard);
    }
}

/// The whole pipeline with the per-shard sweeps run in parallel. Every shard is
/// captured first (the decomposition is a covering antichain, so this detaches
/// all values), the sweeps run across worker threads on the independent shard
/// maps, and the results are reintegrated on this thread. Only capture and
/// reintegrate touch the shared map; the sweeps never contend. The result is
/// identical to [`sweep_all`] with the same kernel.
pub fn sweep_all_parallel<K>(map: &mut PathMap<()>, l_max: usize, kernel: K)
where
    K: Fn(&[u8], &PathMap<()>) -> PatchLog + Sync,
{
    let prefixes = decompose_by_cost(map, l_max);
    let mut shards: Vec<(Vec<u8>, PathMap<()>)> = prefixes
        .into_iter()
        .map(|prefix| {
            let shard = capture(map, &prefix);
            (prefix, shard)
        })
        .collect();

    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(shards.len().max(1));
    let chunk = shards.len().div_ceil(workers.max(1)).max(1);
    std::thread::scope(|scope| {
        for part in shards.chunks_mut(chunk) {
            let kernel = &kernel;
            scope.spawn(move || {
                for (prefix, shard) in part.iter_mut() {
                    let log = kernel(prefix, shard);
                    log.apply(shard);
                }
            });
        }
    });

    for (prefix, shard) in shards {
        reintegrate(map, &prefix, shard);
    }
}

/// Reshard the region under `prefix`: re-decompose just that subtree into
/// within-budget shard prefixes. This is the note's adaptive refinement (step 7):
/// when a shard's realised cost after a sweep exceeds `l_max`, the host calls
/// this to split that region finer for the next round, equivalent to lengthening
/// the hash prefix `k`. The returned prefixes are absolute (each starts with
/// `prefix`); a region already within budget comes back as just `[prefix]`.
pub fn reshard(map: &PathMap<()>, prefix: &[u8], l_max: usize) -> Vec<Vec<u8>> {
    assert!(l_max >= 1, "shard budget must be at least one value");
    let mut out = Vec::new();
    let mut p = prefix.to_vec();
    frontier(map, &mut p, l_max, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keys(map: &PathMap<()>) -> Vec<Vec<u8>> {
        let mut out: Vec<Vec<u8>> = map.iter().map(|(k, _)| k).collect();
        out.sort();
        out
    }

    fn sample() -> PathMap<()> {
        // Prefix-free key set: aa, ab, ac under "a"; ba, bb under "b"; c alone.
        let mut map = PathMap::<()>::default();
        for k in [b"aa".as_slice(), b"ab", b"ac", b"ba", b"bb", b"c"] {
            map.insert(k, ());
        }
        map
    }

    // No key is a proper prefix of another in the frontier.
    fn is_antichain(prefixes: &[Vec<u8>]) -> bool {
        for (i, a) in prefixes.iter().enumerate() {
            for (j, b) in prefixes.iter().enumerate() {
                if i != j && b.starts_with(a) {
                    return false;
                }
            }
        }
        true
    }

    #[test]
    fn cost_is_subtree_value_count() {
        let map = sample();
        assert_eq!(shard_cost(&map, b""), 6);
        assert_eq!(shard_cost(&map, b"a"), 3);
        assert_eq!(shard_cost(&map, b"b"), 2);
        assert_eq!(shard_cost(&map, b"c"), 1);
    }

    #[test]
    fn decompose_covers_bounds_and_is_antichain() {
        let map = sample();
        for l_max in 1..=6 {
            let shards = decompose_by_cost(&map, l_max);
            // Each shard is within budget.
            let mut covered = 0;
            for prefix in &shards {
                let c = shard_cost(&map, prefix);
                assert!(c >= 1 && c <= l_max, "shard {prefix:?} cost {c} > {l_max}");
                covered += c;
            }
            // The shards partition all values (no overlap, full coverage).
            assert_eq!(covered, map.val_count(), "l_max={l_max} coverage");
            assert!(is_antichain(&shards), "l_max={l_max} not an antichain");
        }
    }

    #[test]
    fn capture_then_reintegrate_round_trips() {
        let original = sample();
        let before = keys(&original);

        let mut map = original.clone();
        let shard = capture(&mut map, b"a");
        // The shard holds the suffixes of the "a" keys; the rest stays in map.
        assert_eq!(
            keys(&shard),
            vec![b"a".to_vec(), b"b".to_vec(), b"c".to_vec()]
        );
        assert_eq!(map.val_count(), 3);

        reintegrate(&mut map, b"a", shard);
        assert_eq!(keys(&map), before);
    }

    #[test]
    fn sweep_edits_one_shard_and_leaves_the_rest() {
        let mut map = sample();
        // Sweep the "a" shard with a kernel that adds the shard-relative key "d"
        // (global key "ad") and retracts "c" (global "ac").
        sweep_shard(&mut map, b"a", |shard| {
            assert_eq!(shard.val_count(), 3);
            let mut log = PatchLog::new();
            log.insert(b"d".to_vec());
            log.remove(b"c".to_vec());
            log
        });
        assert_eq!(
            keys(&map),
            vec![
                b"aa".to_vec(),
                b"ab".to_vec(),
                b"ad".to_vec(),
                b"ba".to_vec(),
                b"bb".to_vec(),
                b"c".to_vec(),
            ]
        );
    }

    #[test]
    fn reshard_refines_an_over_budget_region() {
        let map = sample();
        // The "a" region holds aa, ab, ac (3 values). Reshard at budget 1 splits
        // it into within-budget pieces that cover the region and stay under "a".
        let refined = reshard(&map, b"a", 1);
        let covered: usize = refined.iter().map(|p| shard_cost(&map, p)).sum();
        assert_eq!(covered, 3);
        for p in &refined {
            assert!(shard_cost(&map, p) <= 1);
            assert!(p.starts_with(b"a"));
        }
        // A budget that already fits returns the region unchanged.
        assert_eq!(reshard(&map, b"a", 5), vec![b"a".to_vec()]);
    }

    #[test]
    fn sweep_all_with_empty_kernel_round_trips() {
        let original = sample();
        let mut map = original.clone();
        sweep_all(&mut map, 2, |_p, _s| PatchLog::new());
        assert_eq!(keys(&map), keys(&original));
    }

    #[test]
    fn sweep_all_sequential_and_parallel_agree() {
        let base = sample();
        let l_max = 2;
        // A kernel that drops one marker key (shard-relative "Z") into each shard.
        let kernel = |_prefix: &[u8], _shard: &PathMap<()>| {
            let mut log = PatchLog::new();
            log.insert(b"Z".to_vec());
            log
        };

        let mut seq = base.clone();
        sweep_all(&mut seq, l_max, &kernel);
        let mut par = base.clone();
        sweep_all_parallel(&mut par, l_max, &kernel);

        // The two pipelines produce the same space.
        assert_eq!(keys(&seq), keys(&par));

        // Every original key survives and each shard gets exactly one marker.
        let prefixes = decompose_by_cost(&base, l_max);
        for k in keys(&base) {
            assert!(seq.contains(&k), "lost original key {k:?}");
        }
        assert_eq!(seq.val_count(), base.val_count() + prefixes.len());
        for p in &prefixes {
            let mut marker = p.clone();
            marker.extend_from_slice(b"Z");
            assert!(seq.contains(&marker), "missing marker {marker:?}");
        }
    }
}
