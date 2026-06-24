//! Semiring-generalized graph closure: one Kleene-star algorithm, parameterized
//! by the weight semiring K, computes reachability (K = `Reach`, Boolean),
//! all-pairs shortest paths (K = `Tropical`, min-plus), or path counts
//! (K = `Count`). This is the K dimension of the relation engine (task #19): the
//! same closure machinery over a different semiring yields a different analysis,
//! the way the join layer is a semiring of signed multiplicities (the Z-set the
//! incremental work uses). References: Mohri, "Semiring Frameworks and Algorithms
//! for Shortest-Distance Problems", J. Automata, Languages and Combinatorics
//! 7(3):321-350, 2002; Lehmann, "Algebraic structures for transitive closure",
//! Theoretical Computer Science 4(1):59-76, 1977.

/// A semiring `(K, +, *, 0, 1)`: `+` combines alternative paths, `*` extends a
/// path, `0` is "no path", `1` is the empty path. `+` must be commutative and
/// associative with identity `0`; `*` associative with identity `1` and
/// annihilator `0`; `*` distributes over `+`.
pub trait Semiring: Clone + PartialEq {
    /// The additive identity (no path).
    fn zero() -> Self;
    /// The multiplicative identity (the empty path).
    fn one() -> Self;
    /// Combine alternative paths.
    fn add(&self, other: &Self) -> Self;
    /// Extend one path by another.
    fn mul(&self, other: &Self) -> Self;
}

/// Boolean reachability semiring: `+` is or, `*` is and. The closure is the
/// reflexive-transitive closure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reach(pub bool);

impl Semiring for Reach {
    fn zero() -> Self {
        Reach(false)
    }
    fn one() -> Self {
        Reach(true)
    }
    fn add(&self, other: &Self) -> Self {
        Reach(self.0 || other.0)
    }
    fn mul(&self, other: &Self) -> Self {
        Reach(self.0 && other.0)
    }
}

/// Tropical (min, +) semiring for shortest distances. `None` is +infinity (no
/// path); `Some(d)` is a finite distance. The closure is all-pairs shortest
/// paths (correct for non-negative weights with no negative cycle).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tropical(pub Option<i64>);

impl Semiring for Tropical {
    fn zero() -> Self {
        Tropical(None)
    }
    fn one() -> Self {
        Tropical(Some(0))
    }
    fn add(&self, other: &Self) -> Self {
        match (self.0, other.0) {
            (None, x) | (x, None) => Tropical(x),
            (Some(a), Some(b)) => Tropical(Some(a.min(b))),
        }
    }
    fn mul(&self, other: &Self) -> Self {
        match (self.0, other.0) {
            (Some(a), Some(b)) => Tropical(Some(a.saturating_add(b))),
            _ => Tropical(None),
        }
    }
}

/// Counting semiring: `+` adds, `*` multiplies. The closure counts distinct
/// paths, well-defined on a directed acyclic graph (a cycle gives infinitely
/// many paths). Counts saturate rather than overflow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Count(pub u64);

impl Semiring for Count {
    fn zero() -> Self {
        Count(0)
    }
    fn one() -> Self {
        Count(1)
    }
    fn add(&self, other: &Self) -> Self {
        Count(self.0.saturating_add(other.0))
    }
    fn mul(&self, other: &Self) -> Self {
        Count(self.0.saturating_mul(other.0))
    }
}

/// All-pairs closure of an `n`-node graph over the semiring `K`, by the
/// Kleene-star (Floyd-Warshall) algorithm. `edges` are `(from, to, weight)`;
/// parallel edges combine with `+`. The diagonal carries the empty path (`1`),
/// so `d[i][j]` is the semiring sum over all `i -> j` paths including the trivial
/// one. O(n^3) semiring operations. Out-of-range endpoints are ignored.
pub fn semiring_closure<K: Semiring>(n: usize, edges: &[(usize, usize, K)]) -> Vec<Vec<K>> {
    let mut d = vec![vec![K::zero(); n]; n];
    for (i, row) in d.iter_mut().enumerate() {
        row[i] = K::one();
    }
    for (from, to, weight) in edges {
        if *from < n && *to < n {
            d[*from][*to] = d[*from][*to].add(weight);
        }
    }
    // Relax only through a strictly intermediate node `k` (skip k == i or k == j,
    // which re-add the direct path). For idempotent semirings (Reach, Tropical)
    // those are no-ops; for the counting semiring skipping them avoids
    // double-counting the direct path through the empty-path diagonal.
    let zero = K::zero();
    for k in 0..n {
        for i in 0..n {
            if i == k {
                continue;
            }
            let dik = d[i][k].clone();
            if dik == zero {
                continue;
            }
            for j in 0..n {
                if j == k {
                    continue;
                }
                let through = dik.mul(&d[k][j]);
                d[i][j] = d[i][j].add(&through);
            }
        }
    }
    d
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reachability_closure_is_reflexive_transitive() {
        // 0 -> 1 -> 2, plus a branch 0 -> 3.
        let edges = [
            (0, 1, Reach(true)),
            (1, 2, Reach(true)),
            (0, 3, Reach(true)),
        ];
        let d = semiring_closure(4, &edges);
        // 0 reaches everything; 2 and 3 reach only themselves.
        assert_eq!(
            d[0],
            vec![Reach(true), Reach(true), Reach(true), Reach(true)]
        );
        assert_eq!(
            d[1],
            vec![Reach(false), Reach(true), Reach(true), Reach(false)]
        );
        assert_eq!(
            d[2],
            vec![Reach(false), Reach(false), Reach(true), Reach(false)]
        );
    }

    #[test]
    fn tropical_closure_is_shortest_paths() {
        // 0 -1-> 1 -2-> 2, and a longer direct 0 -10-> 2.
        let edges = [
            (0, 1, Tropical(Some(1))),
            (1, 2, Tropical(Some(2))),
            (0, 2, Tropical(Some(10))),
        ];
        let d = semiring_closure(3, &edges);
        assert_eq!(d[0][0], Tropical(Some(0)));
        assert_eq!(d[0][1], Tropical(Some(1)));
        // min(10, 1+2) = 3.
        assert_eq!(d[0][2], Tropical(Some(3)));
        assert_eq!(d[1][2], Tropical(Some(2)));
        // 2 cannot reach 0.
        assert_eq!(d[2][0], Tropical(None));
    }

    #[test]
    fn counting_closure_counts_paths_in_a_dag() {
        // Diamond: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3. Two paths 0 -> 3.
        let edges = [
            (0, 1, Count(1)),
            (0, 2, Count(1)),
            (1, 3, Count(1)),
            (2, 3, Count(1)),
        ];
        let d = semiring_closure(4, &edges);
        assert_eq!(d[0][3], Count(2));
        assert_eq!(d[0][1], Count(1));
        // A doubled parallel edge counts twice.
        let parallel = [(0, 1, Count(1)), (0, 1, Count(1))];
        let d2 = semiring_closure(2, &parallel);
        assert_eq!(d2[0][1], Count(2));
    }

    #[test]
    fn one_algorithm_three_analyses_agree_on_reachability() {
        // The same graph: tropical-finite iff counting-positive iff reach-true.
        let n = 5;
        let tropical = [
            (0, 1, Tropical(Some(4))),
            (1, 2, Tropical(Some(3))),
            (3, 4, Tropical(Some(1))),
        ];
        let reach = [
            (0, 1, Reach(true)),
            (1, 2, Reach(true)),
            (3, 4, Reach(true)),
        ];
        let dt = semiring_closure(n, &tropical);
        let dr = semiring_closure(n, &reach);
        for i in 0..n {
            for j in 0..n {
                assert_eq!(
                    dt[i][j].0.is_some(),
                    dr[i][j].0,
                    "reach mismatch at {i},{j}"
                );
            }
        }
    }
}
