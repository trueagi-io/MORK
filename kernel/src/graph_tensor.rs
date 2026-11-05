//! Materialise a binary relation into a CSR adjacency and run graph-numeric
//! sweeps with the linalg kernels. The bridge from MORK's symbolic relations to
//! the numeric einsum/CSR engine, and the numeric half of the ShardZipper
//! materialise step: a shard of `(rel a b)` facts becomes a sparse adjacency a
//! kernel can sweep (degrees, 2-hop counts, message passing), then results map
//! back to symbols.
//!
//! CSR needs a dense `0..n` node numbering, but MORK nodes are encoded symbol
//! bytes, so the materialiser carries a per-relation bijection
//! `symbol_bytes <-> dense u32` (the local node numbering). For a ShardZipper
//! shard this numbering is local and small, matching the cost-bounded
//! decomposition. Edge weights are `u32` counts (saturating), so 2-hop counts
//! and multiplicities compose; switch the value type to `f32` for weighted
//! message passing.

use std::collections::{HashMap, HashSet};

use linalg::csr::Csr;
use linalg::dense::Dense;
use linalg::jit::{JitInput, einsum_auto};
use linalg::tensor::NDIndex;
use mork_expr::{Tag, item_byte};

use crate::term_identity::{TermId, TermIdentitySidecar};

/// Encode a bare symbol name as MORK bytes: `SymbolSize(len)` then the name.
pub fn encode_symbol(name: &[u8]) -> Vec<u8> {
    assert!(
        (1..64).contains(&name.len()),
        "symbol length must be 1..64 bytes"
    );
    let mut out = vec![item_byte(Tag::SymbolSize(name.len() as u8))];
    out.extend_from_slice(name);
    out
}

/// Encode the fact `(head op0 op1 ...)` as MORK bytes. `head_name` is a bare
/// symbol name; each operand is already-encoded bytes (as `enumerate` returns).
pub fn encode_fact(head_name: &[u8], operand_encodings: &[&[u8]]) -> Vec<u8> {
    let arity = operand_encodings.len() + 1;
    assert!(arity < 64, "fact arity must fit the six-bit encoding");
    let mut out = vec![item_byte(Tag::Arity(arity as u8))];
    out.extend_from_slice(&encode_symbol(head_name));
    for operand in operand_encodings {
        out.extend_from_slice(operand);
    }
    out
}

/// A binary relation materialised as a square CSR adjacency over a dense local
/// node numbering. `index_to_symbol[i]` is the encoded bytes of node `i`.
pub struct RelationAdjacency {
    pub adjacency: Csr<u32, u32>,
    pub index_to_symbol: Vec<Vec<u8>>,
    symbol_to_index: HashMap<Vec<u8>, u32>,
    edges: Vec<(u32, u32)>,
}

impl RelationAdjacency {
    /// Build the adjacency for the relation whose head is `relation_head`, over
    /// its live binary facts in `sidecar`. A fact `(rel a b)` contributes the
    /// edge `a -> b`; the operands `a` and `b` are interned into the local node
    /// numbering by their encoded bytes. Facts that are not binary (arity other
    /// than `(head a b)`) are skipped.
    pub fn from_sidecar(sidecar: &TermIdentitySidecar, relation_head: TermId) -> Self {
        let mut symbol_to_index: HashMap<Vec<u8>, u32> = HashMap::new();
        let mut index_to_symbol: Vec<Vec<u8>> = Vec::new();
        let mut edges: Vec<(u32, u32)> = Vec::new();

        let mut intern = |sidecar: &TermIdentitySidecar,
                          node: TermId,
                          symbol_to_index: &mut HashMap<Vec<u8>, u32>,
                          index_to_symbol: &mut Vec<Vec<u8>>|
         -> u32 {
            let bytes = sidecar
                .get_term(node)
                .expect("operand term is interned")
                .encoded()
                .to_vec();
            if let Some(&i) = symbol_to_index.get(&bytes) {
                return i;
            }
            let i = index_to_symbol.len() as u32;
            symbol_to_index.insert(bytes.clone(), i);
            index_to_symbol.push(bytes);
            i
        };

        for &fact in sidecar.facts_for_relation(relation_head) {
            if !sidecar.is_fact_live(fact) {
                continue;
            }
            let Some(record) = sidecar.get_fact(fact) else {
                continue;
            };
            let Some(term) = sidecar.get_term(record.root) else {
                continue;
            };
            let children = term.children();
            // (rel a b) flattens to Arity(3) over [rel, a, b].
            if children.len() != 3 {
                continue;
            }
            let src = intern(
                sidecar,
                children[1],
                &mut symbol_to_index,
                &mut index_to_symbol,
            );
            let dst = intern(
                sidecar,
                children[2],
                &mut symbol_to_index,
                &mut index_to_symbol,
            );
            edges.push((src, dst));
        }

        let n = index_to_symbol.len() as u32;
        let adjacency = Csr::<u32, u32>::from_edges(n, &edges);
        Self {
            adjacency,
            index_to_symbol,
            symbol_to_index,
            edges,
        }
    }

    /// Number of nodes in the local numbering.
    pub fn node_count(&self) -> usize {
        self.index_to_symbol.len()
    }

    /// Dense index of an encoded node, if it appears in the relation.
    pub fn index_of(&self, symbol_bytes: &[u8]) -> Option<u32> {
        self.symbol_to_index.get(symbol_bytes).copied()
    }

    /// Out-degree of every node, `out_degree[i]` = number of edges from node `i`.
    /// Reads straight off the CSR row offsets, O(n).
    pub fn out_degrees(&self) -> Vec<u32> {
        (0..self.node_count())
            .map(|row| self.adjacency.row(row as u32).count() as u32)
            .collect()
    }

    /// Two-hop path counts: the SpGEMM `A . A`. Entry `(a, c)` counts the
    /// distinct intermediates `b` with `a -> b -> c`. Uses the linalg CSR
    /// matmul (saturating `u32` accumulation).
    pub fn two_hop(&self) -> Csr<u32, u32> {
        self.adjacency.matmul(&self.adjacency)
    }

    /// Enumerate the edges of a result adjacency over this numbering as
    /// `(src_bytes, dst_bytes, count)`, mapping dense indices back to symbols.
    pub fn enumerate(&self, result: &Csr<u32, u32>) -> Vec<(Vec<u8>, Vec<u8>, u32)> {
        let mut out = Vec::new();
        for row in 0..self.node_count() {
            for (col, count) in result.row(row as u32) {
                out.push((
                    self.index_to_symbol[row].clone(),
                    self.index_to_symbol[col as usize].clone(),
                    count,
                ));
            }
        }
        out
    }

    /// The raw adjacency as `f32` weights (every edge 1.0), for message passing
    /// with sum aggregation.
    pub fn adjacency_f32(&self) -> Csr<u32, f32> {
        Csr::<u32, f32>::from_edges(self.node_count() as u32, &self.edges)
    }

    /// The symmetric GCN-normalized adjacency of Kipf and Welling (ICLR 2017):
    /// `D_hat^-1/2 (A + A^T + I) D_hat^-1/2`. The relation is symmetrized and
    /// given self-loops, then each entry `(i, j)` is scaled by
    /// `1 / sqrt(deg_i * deg_j)` over the augmented degrees. This is the constant
    /// propagation operator a GCN layer multiplies node features by.
    pub fn gcn_normalized_adjacency(&self) -> Csr<u32, f32> {
        let n = self.node_count();
        // A_hat = A + A^T + I (symmetrize, add self-loops).
        let mut entries: HashSet<(u32, u32)> = HashSet::new();
        for &(a, b) in &self.edges {
            entries.insert((a, b));
            entries.insert((b, a));
        }
        for i in 0..n as u32 {
            entries.insert((i, i));
        }
        // Augmented degrees.
        let mut degree = vec![0u32; n];
        for &(i, _) in &entries {
            degree[i as usize] += 1;
        }
        // w_ij = 1 / sqrt(deg_i * deg_j).
        let mut triplets: Vec<(u32, u32, f32)> = entries
            .into_iter()
            .map(|(i, j)| {
                let scale =
                    1.0 / ((degree[i as usize] as f32) * (degree[j as usize] as f32)).sqrt();
                (i, j, scale)
            })
            .collect();
        Csr::<u32, f32>::from_coo(n as u32, &mut triplets)
    }

    /// One message-passing step `Y = W . X`: multiply a (typically normalized)
    /// weight adjacency `weights` by a dense node-feature matrix `features`
    /// (`[node_count, feature_dim]`) with the linalg sparse-aware einsum. This is
    /// the dominant operation of a GCN layer; compose `weights` once, sweep many
    /// layers. Per Cluster-GCN (Chiang et al., KDD 2019), running this per
    /// ShardZipper shard is the standard within-subgraph convolution.
    pub fn propagate(&self, weights: &Csr<u32, f32>, features: &Dense<f32>) -> Dense<f32> {
        let n = self.node_count();
        assert_eq!(
            features.shape.first().copied(),
            Some(n),
            "feature rows must equal node count"
        );
        let feature_dim = features.shape.get(1).copied().unwrap_or(1);
        let mut out = Dense::<f32>::zeros(vec![n, feature_dim]);
        // Route the sparse-by-dense SpMM through the linalg plan, which selects
        // the native SparseDenseMatmul kernel (no JIT compile) for CSR x Dense.
        // The crate's benchmarks put it at 55-131x the interpreted einsum VM.
        einsum_auto(
            "ab,bc->ac",
            &[JitInput::Csr(weights), JitInput::Dense(features)],
            &mut [&mut out],
        )
        .expect("sparse-dense matmul plan");
        out
    }

    /// One full GCN layer `H' = relu((A_norm . H) . W)`: aggregate neighbor
    /// features through the normalized adjacency, transform them by the dense
    /// weight `W` (`[feature_in, feature_out]`), then apply the ReLU nonlinearity.
    pub fn gcn_layer(
        &self,
        normalized: &Csr<u32, f32>,
        features: &Dense<f32>,
        weight: &Dense<f32>,
    ) -> Dense<f32> {
        relu(dense_matmul(&self.propagate(normalized, features), weight))
    }

    /// A full GCN forward pass: build the normalized adjacency once, then stack
    /// `weights.len()` layers `H <- relu((A_norm . H) . W_l)`. The input
    /// `features` is `[node_count, feature_0]`; each `weights[l]` is
    /// `[feature_l, feature_{l+1}]`.
    pub fn gcn_forward(&self, features: &Dense<f32>, weights: &[Dense<f32>]) -> Dense<f32> {
        let normalized = self.gcn_normalized_adjacency();
        let mut state = features.clone();
        for weight in weights {
            state = self.gcn_layer(&normalized, &state, weight);
        }
        state
    }

    /// PageRank over the relation (Brin and Page, 1998). Power-iterates
    /// `r <- (1-d)/N + d (M r + dangling_mass/N)`, where `M[b,a] = 1/outdeg(a)`
    /// for each edge `a -> b` is the out-degree-normalized transition (computed
    /// once and applied with the linalg SpMM), and the mass of dangling nodes
    /// (no out-edges) is redistributed uniformly so the scores stay a
    /// distribution. Returns `(node_bytes, score)` for every node. `damping` is
    /// usually 0.85.
    pub fn pagerank(&self, damping: f32, iterations: usize) -> Vec<(Vec<u8>, f32)> {
        let n = self.node_count();
        if n == 0 {
            return Vec::new();
        }
        let out_degree: Vec<u32> = (0..n)
            .map(|a| self.adjacency.row(a as u32).count() as u32)
            .collect();
        // Transition matrix M[b, a] = 1 / outdeg(a) for edge a -> b.
        let mut triplets: Vec<(u32, u32, f32)> = self
            .edges
            .iter()
            .map(|&(a, b)| (b, a, 1.0 / out_degree[a as usize] as f32))
            .collect();
        let transition = Csr::<u32, f32>::from_coo(n as u32, &mut triplets);
        let dangling: Vec<usize> = (0..n).filter(|&i| out_degree[i] == 0).collect();

        let mut rank = Dense::<f32>::zeros(vec![n, 1]);
        rank.fill_from(&vec![1.0 / n as f32; n]);
        for _ in 0..iterations {
            let dangling_mass: f32 = dangling.iter().map(|&i| rank.get(&[i, 0])).sum();
            let propagated = self.propagate(&transition, &rank);
            let base = (1.0 - damping) / n as f32 + damping * dangling_mass / n as f32;
            let mut next = Dense::<f32>::zeros(vec![n, 1]);
            for i in 0..n {
                next.set(&[i, 0], base + damping * propagated.get(&[i, 0]));
            }
            rank = next;
        }
        (0..n)
            .map(|i| (self.index_to_symbol[i].clone(), rank.get(&[i, 0])))
            .collect()
    }
}

/// Dense matrix product `[m, k] . [k, p] -> [m, p]` via the linalg einsum.
fn dense_matmul(a: &Dense<f32>, b: &Dense<f32>) -> Dense<f32> {
    let m = a.shape[0];
    let inner = a.shape[1];
    assert_eq!(inner, b.shape[0], "inner dimensions must match");
    let p = b.shape[1];
    let mut out = Dense::<f32>::zeros(vec![m, p]);
    linalg::einsum::einsum::<f32>(
        "ab,bc->ac",
        &[a as &dyn NDIndex<f32>, b as &dyn NDIndex<f32>],
        &mut [&mut out as &mut dyn NDIndex<f32>],
    )
    .expect("matmul spec is valid");
    out
}

/// ReLU nonlinearity in place over a dense tensor's flat storage.
fn relu(mut x: Dense<f32>) -> Dense<f32> {
    for v in &mut x.data {
        if *v < 0.0 {
            *v = 0.0;
        }
    }
    x
}

#[cfg(test)]
mod tests {
    use super::*;
    use mork_expr::{Tag, item_byte};

    fn sym(bytes: &[u8]) -> Vec<u8> {
        let mut out = vec![item_byte(Tag::SymbolSize(bytes.len() as u8))];
        out.extend_from_slice(bytes);
        out
    }

    fn app(children: &[Vec<u8>]) -> Vec<u8> {
        let mut out = vec![item_byte(Tag::Arity(children.len() as u8))];
        for child in children {
            out.extend_from_slice(child);
        }
        out
    }

    fn edge_fact(a: &[u8], b: &[u8]) -> Vec<u8> {
        app(&[sym(b"edge"), sym(a), sym(b)])
    }

    fn build(edges: &[(&[u8], &[u8])]) -> (TermIdentitySidecar, TermId) {
        let mut sidecar = TermIdentitySidecar::new();
        for (a, b) in edges {
            sidecar.insert_fact(&edge_fact(a, b)).unwrap();
        }
        let head = sidecar.term_id_for_encoded(&sym(b"edge")).unwrap();
        (sidecar, head)
    }

    #[test]
    fn materialise_adjacency_and_degrees() {
        // a -> b, a -> c, b -> c : node a has out-degree 2, b has 1, c has 0.
        let (sidecar, head) = build(&[(b"a", b"b"), (b"a", b"c"), (b"b", b"c")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        assert_eq!(adj.node_count(), 3);

        let a = adj.index_of(&sym(b"a")).unwrap() as usize;
        let b = adj.index_of(&sym(b"b")).unwrap() as usize;
        let c = adj.index_of(&sym(b"c")).unwrap() as usize;
        let deg = adj.out_degrees();
        assert_eq!(deg[a], 2);
        assert_eq!(deg[b], 1);
        assert_eq!(deg[c], 0);
    }

    #[test]
    fn two_hop_via_spgemm() {
        // Path a -> b -> c -> d. A.A gives a -> c and b -> d, each one path.
        let (sidecar, head) = build(&[(b"a", b"b"), (b"b", b"c"), (b"c", b"d")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        let two = adj.two_hop();
        let mut pairs = adj.enumerate(&two);
        pairs.sort();

        let mut expected = vec![(sym(b"a"), sym(b"c"), 1u32), (sym(b"b"), sym(b"d"), 1u32)];
        expected.sort();
        assert_eq!(pairs, expected);
    }

    #[test]
    fn two_hop_counts_distinct_intermediates() {
        // a -> b -> d and a -> c -> d: two distinct 2-paths a => d.
        let (sidecar, head) = build(&[(b"a", b"b"), (b"a", b"c"), (b"b", b"d"), (b"c", b"d")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        let two = adj.two_hop();
        let pairs = adj.enumerate(&two);
        let a_to_d = pairs
            .iter()
            .find(|(s, d, _)| *s == sym(b"a") && *d == sym(b"d"));
        assert_eq!(a_to_d.map(|(_, _, count)| *count), Some(2));
    }

    #[test]
    fn propagate_sum_aggregation() {
        // a -> b, a -> c. With one-hot features for b and c, node a's message
        // pass sums them: feature 0 comes from b, feature 1 from c.
        let (sidecar, head) = build(&[(b"a", b"b"), (b"a", b"c")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        let n = adj.node_count();
        let a = adj.index_of(&sym(b"a")).unwrap() as usize;
        let b = adj.index_of(&sym(b"b")).unwrap() as usize;
        let c = adj.index_of(&sym(b"c")).unwrap() as usize;

        let mut x = Dense::<f32>::zeros(vec![n, 2]);
        x.set(&[b, 0], 1.0);
        x.set(&[c, 1], 1.0);
        let y = adj.propagate(&adj.adjacency_f32(), &x);
        assert_eq!(y.get(&[a, 0]), 1.0);
        assert_eq!(y.get(&[a, 1]), 1.0);
    }

    #[test]
    fn gcn_normalization_is_symmetric_with_self_loops() {
        // Single edge a - b. A_hat = {(a,a),(a,b),(b,a),(b,b)}, deg_a = deg_b = 2,
        // each weight 1/sqrt(2*2) = 0.5. Propagating all-ones returns 1.0 per node
        // (a degree-preserving fixed point of the normalized operator).
        let (sidecar, head) = build(&[(b"a", b"b")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        assert_eq!(adj.node_count(), 2);

        let norm = adj.gcn_normalized_adjacency();
        assert_eq!(norm.nnz(), 4);

        let mut x = Dense::<f32>::zeros(vec![2, 1]);
        x.fill_from(&[1.0, 1.0]);
        let y = adj.propagate(&norm, &x);
        assert!((y.get(&[0, 0]) - 1.0).abs() < 1e-6);
        assert!((y.get(&[1, 0]) - 1.0).abs() < 1e-6);
    }

    #[test]
    fn gcn_layer_transforms_and_relus() {
        // Single edge a - b, normalized so propagate(ones) = ones. Weight [[2]]
        // scales to 2; weight [[-1]] goes negative and ReLU clamps it to 0.
        let (sidecar, head) = build(&[(b"a", b"b")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        let norm = adj.gcn_normalized_adjacency();
        let mut x = Dense::<f32>::zeros(vec![2, 1]);
        x.fill_from(&[1.0, 1.0]);

        let mut positive = Dense::<f32>::zeros(vec![1, 1]);
        positive.fill_from(&[2.0]);
        let y = adj.gcn_layer(&norm, &x, &positive);
        assert!((y.get(&[0, 0]) - 2.0).abs() < 1e-6);
        assert!((y.get(&[1, 0]) - 2.0).abs() < 1e-6);

        let mut negative = Dense::<f32>::zeros(vec![1, 1]);
        negative.fill_from(&[-1.0]);
        let z = adj.gcn_layer(&norm, &x, &negative);
        assert_eq!(z.get(&[0, 0]), 0.0);
        assert_eq!(z.get(&[1, 0]), 0.0);
    }

    #[test]
    fn gcn_forward_stacks_layers() {
        // A 3-cycle; a two-layer GCN projecting features 2 -> 3 -> 1.
        let (sidecar, head) = build(&[(b"a", b"b"), (b"b", b"c"), (b"c", b"a")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        let n = adj.node_count();
        assert_eq!(n, 3);

        let mut x = Dense::<f32>::zeros(vec![n, 2]);
        for i in 0..n {
            x.set(&[i, 0], 1.0);
            x.set(&[i, 1], 0.5);
        }
        let mut w0 = Dense::<f32>::zeros(vec![2, 3]);
        w0.fill_from(&[0.1, 0.2, 0.3, 0.4, 0.5, 0.6]);
        let mut w1 = Dense::<f32>::zeros(vec![3, 1]);
        w1.fill_from(&[1.0, 1.0, 1.0]);

        let out = adj.gcn_forward(&x, &[w0, w1]);
        assert_eq!(out.shape, vec![n, 1]);
        // Nonnegative inputs and weights through ReLU layers stay nonnegative.
        assert!(out.data.iter().all(|&v| v >= 0.0));
        // The cycle is vertex-transitive, so every node gets the same output.
        assert!((out.get(&[0, 0]) - out.get(&[1, 0])).abs() < 1e-6);
        assert!((out.get(&[1, 0]) - out.get(&[2, 0])).abs() < 1e-6);
    }

    #[test]
    fn pagerank_ranks_the_hub_highest() {
        // a -> c, b -> c. The sink c has two in-edges and should rank highest;
        // the scores form a distribution (sum ~ 1).
        let (sidecar, head) = build(&[(b"a", b"c"), (b"b", b"c")]);
        let adj = RelationAdjacency::from_sidecar(&sidecar, head);
        let ranks = adj.pagerank(0.85, 100);
        assert_eq!(ranks.len(), 3);

        let score = |s: &[u8]| ranks.iter().find(|(node, _)| node == &sym(s)).unwrap().1;
        let total: f32 = ranks.iter().map(|(_, r)| r).sum();
        assert!(
            (total - 1.0).abs() < 1e-4,
            "scores should sum to 1, got {total}"
        );
        assert!(score(b"c") > score(b"a"));
        assert!(score(b"c") > score(b"b"));
    }
}
