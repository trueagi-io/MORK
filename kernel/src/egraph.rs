//! Scoped equality domains: congruence closure with extraction.
//!
//! Equality lives here, not in the global byte pathspace. Terms are only
//! quotiented inside an explicit [`EGraph`], so ordinary syntactic MM2 and
//! PathMap semantics stay untouched everywhere else. You build a graph, feed it
//! equalities (for MeTTa, the `(= lhs rhs)` facts), call [`EGraph::rebuild`] to
//! close under congruence, and then ask whether two terms are equal or pull out
//! the cheapest representative of a class.
//!
//! The three pieces are the standard equality-saturation kit:
//!
//! - a union-find with path halving and union by rank over e-class ids,
//! - congruence closure by the canonical-rebuild loop (egg's `rebuild`): after a
//!   batch of unions, recanonicalize every e-node against the current class
//!   roots, and any two e-nodes that now look identical name equal classes, so
//!   union them and repeat until a pass finds nothing new,
//! - bottom-up minimum-node-count extraction, picking a finite representative.
//!
//! The node representation follows MORK's encoding instead of a separate term
//! store: a leaf e-node carries its exact encoded bytes, and an application
//! e-node carries the arity tag byte plus its child classes. MORK flattens
//! `(f a b)` to `Arity(3)` over children `[f, a, b]`, so the operator identity
//! is `children[0]` and keying an e-node on `(arity_byte, child_classes)` gives
//! the right congruence: `(f a)` and `(f b)` are congruent exactly when `a`
//! and `b` land in the same class.
//!
//! The graph reads interned structure from a [`TermIdentitySidecar`] and
//! re-interns the extracted representative back into that same sidecar, so an
//! extracted term is an ordinary MORK [`TermId`] usable everywhere else.

use std::collections::{BTreeMap, HashMap};

use crate::term_identity::{TermId, TermIdentitySidecar, TermKind};

/// Identity of an equivalence class (a union-find node).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EClassId(pub u32);

impl EClassId {
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// Identity of an e-node (one syntactic shape sitting in some class).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ENodeId(pub u32);

impl ENodeId {
    #[inline]
    fn index(self) -> usize {
        self.0 as usize
    }
}

/// The syntactic shape of an e-node, with children named by class.
///
/// A `Leaf` holds the exact encoded bytes of a complete leaf term (a symbol, a
/// `NewVar`, or a `VarRef`), which is already a standalone MORK term. An `App`
/// holds the arity tag byte and the classes of its children; the head symbol of
/// the application is `children[0]`.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ENodeKind {
    Leaf(Box<[u8]>),
    App { head: u8, children: Box<[EClassId]> },
}

/// One e-node: a shape plus the class it currently belongs to.
#[derive(Clone, Debug)]
pub struct ENode {
    pub id: ENodeId,
    pub kind: ENodeKind,
    pub class: EClassId,
}

/// A scoped congruence-closure graph over interned terms.
#[derive(Clone, Debug, Default)]
pub struct EGraph {
    parents: Vec<EClassId>,
    ranks: Vec<u8>,
    nodes: Vec<ENode>,
    canonical: HashMap<ENodeKind, EClassId>,
    term_classes: HashMap<TermId, EClassId>,
    dirty: bool,
}

impl EGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn class_count(&self) -> usize {
        self.parents.len()
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    fn make_class(&mut self) -> EClassId {
        let id = EClassId(self.parents.len() as u32);
        self.parents.push(id);
        self.ranks.push(0);
        id
    }

    /// Class root, read-only (no path compression).
    pub fn find(&self, mut class: EClassId) -> EClassId {
        while self.parents[class.index()] != class {
            class = self.parents[class.index()];
        }
        class
    }

    /// Class root with path halving applied along the walk.
    fn find_mut(&mut self, class: EClassId) -> EClassId {
        let root = self.find(class);
        let mut current = class;
        while self.parents[current.index()] != current {
            let next = self.parents[current.index()];
            self.parents[current.index()] = root;
            current = next;
        }
        root
    }

    /// Merges two classes, union by rank. Marks the graph dirty so the next
    /// [`rebuild`](Self::rebuild) re-closes congruence.
    pub fn union(&mut self, left: EClassId, right: EClassId) -> EClassId {
        let mut left = self.find_mut(left);
        let mut right = self.find_mut(right);
        if left == right {
            return left;
        }
        if self.ranks[left.index()] < self.ranks[right.index()] {
            std::mem::swap(&mut left, &mut right);
        }
        self.parents[right.index()] = left;
        if self.ranks[left.index()] == self.ranks[right.index()] {
            self.ranks[left.index()] = self.ranks[left.index()].saturating_add(1);
        }
        self.dirty = true;
        left
    }

    /// Interns a term's structure into the graph, returning its class. Shares
    /// e-nodes by canonical shape, so equal subterms reuse a class. Reads child
    /// structure from `sidecar`.
    pub fn add_term(&mut self, term: TermId, sidecar: &TermIdentitySidecar) -> EClassId {
        if let Some(class) = self.term_classes.get(&term).copied() {
            return self.find(class);
        }
        let record = sidecar
            .get_term(term)
            .expect("e-graph add_term: TermId must be interned in the sidecar");
        let kind = match record.kind {
            TermKind::Application { .. } => {
                let head = record.encoded()[0];
                let child_terms: Vec<TermId> = record.children().to_vec();
                let children = child_terms
                    .into_iter()
                    .map(|child| self.add_term(child, sidecar))
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                ENodeKind::App { head, children }
            }
            TermKind::Symbol | TermKind::NewVar | TermKind::VarRef(_) => {
                ENodeKind::Leaf(record.encoded().to_vec().into_boxed_slice())
            }
        };
        let canonical_kind = self.canonicalize_kind(&kind);
        let class = if let Some(class) = self.canonical.get(&canonical_kind).copied() {
            self.find(class)
        } else {
            let class = self.make_class();
            let id = ENodeId(self.nodes.len() as u32);
            self.nodes.push(ENode {
                id,
                kind: canonical_kind.clone(),
                class,
            });
            self.canonical.insert(canonical_kind, class);
            class
        };
        self.term_classes.insert(term, class);
        class
    }

    /// Adds both terms and unions their classes (asserts `left = right`). The
    /// caller still owes a [`rebuild`](Self::rebuild) before querying.
    pub fn add_equivalence(
        &mut self,
        left: TermId,
        right: TermId,
        sidecar: &TermIdentitySidecar,
    ) -> EClassId {
        let left = self.add_term(left, sidecar);
        let right = self.add_term(right, sidecar);
        self.union(left, right)
    }

    /// Builds a closed equality graph from every live `(= lhs rhs)` fact whose
    /// relation head is `equality_head`, reading the facts straight out of the
    /// sidecar. The result is already rebuilt, so [`equivalent_terms`] and
    /// [`extract_cheapest`] are ready to use. This is the bridge from a Space's
    /// MeTTa equalities into a congruence domain.
    ///
    /// [`equivalent_terms`]: Self::equivalent_terms
    /// [`extract_cheapest`]: Self::extract_cheapest
    pub fn from_equalities(sidecar: &TermIdentitySidecar, equality_head: TermId) -> Self {
        let mut graph = Self::new();
        for &fact in sidecar.facts_for_relation(equality_head) {
            if !sidecar.is_fact_live(fact) {
                continue;
            }
            let Some(record) = sidecar.get_fact(fact) else {
                continue;
            };
            let root = record.root;
            let Some(term) = sidecar.get_term(root) else {
                continue;
            };
            // (= lhs rhs) flattens to Arity(3) over children [=, lhs, rhs].
            let children = term.children();
            if children.len() == 3 {
                graph.add_equivalence(children[1], children[2], sidecar);
            }
        }
        graph.rebuild();
        graph
    }

    pub fn equivalent_classes(&self, left: EClassId, right: EClassId) -> bool {
        self.find(left) == self.find(right)
    }

    /// Whether two terms are provably equal under the current closure. Adds them
    /// if absent (does not itself rebuild, so call after the equalities are in
    /// and rebuilt).
    pub fn equivalent_terms(
        &mut self,
        left: TermId,
        right: TermId,
        sidecar: &TermIdentitySidecar,
    ) -> bool {
        let left = self.add_term(left, sidecar);
        let right = self.add_term(right, sidecar);
        self.find(left) == self.find(right)
    }

    /// Rewrites an e-node's child classes to their current roots.
    fn canonicalize_kind(&self, kind: &ENodeKind) -> ENodeKind {
        match kind {
            ENodeKind::App { head, children } => ENodeKind::App {
                head: *head,
                children: children
                    .iter()
                    .copied()
                    .map(|child| self.find(child))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            },
            ENodeKind::Leaf(bytes) => ENodeKind::Leaf(bytes.clone()),
        }
    }

    /// Restores congruence closure after one or more unions. Returns the number
    /// of rebuilding rounds. A round may discover further unions (two e-nodes
    /// that now canonicalize identically name equal classes), which forces
    /// another pass; the loop ends when a pass finds nothing new.
    pub fn rebuild(&mut self) -> usize {
        let mut rounds = 0usize;
        while self.dirty || rounds == 0 {
            rounds += 1;
            self.dirty = false;
            for index in 0..self.parents.len() {
                self.find_mut(EClassId(index as u32));
            }

            let entries = self
                .nodes
                .iter()
                .map(|node| {
                    (
                        node.id,
                        self.canonicalize_kind(&node.kind),
                        self.find(node.class),
                    )
                })
                .collect::<Vec<_>>();
            let mut table = HashMap::<ENodeKind, EClassId>::new();
            let mut unions = Vec::new();
            for (_, kind, class) in &entries {
                if let Some(existing) = table.insert(kind.clone(), *class) {
                    if self.find(existing) != self.find(*class) {
                        unions.push((existing, *class));
                    }
                }
            }
            if unions.is_empty() {
                self.canonical.clear();
                for (node_id, kind, class) in entries {
                    let root = self.find(class);
                    self.nodes[node_id.index()].kind = kind.clone();
                    self.nodes[node_id.index()].class = root;
                    self.canonical.insert(kind, root);
                }
                for class in self.term_classes.values_mut() {
                    // Local root walk: borrowing all of self while the map is
                    // mutably borrowed is not allowed, so walk parents directly.
                    let mut root = *class;
                    while self.parents[root.index()] != root {
                        root = self.parents[root.index()];
                    }
                    *class = root;
                }
                break;
            }
            for (left, right) in unions {
                self.union(left, right);
            }
        }
        rounds
    }

    /// All e-nodes grouped by current class root.
    pub fn classes(&self) -> BTreeMap<EClassId, Vec<&ENode>> {
        let mut classes = BTreeMap::<EClassId, Vec<&ENode>>::new();
        for node in &self.nodes {
            classes.entry(self.find(node.class)).or_default().push(node);
        }
        classes
    }

    pub fn nodes_in_class(&self, class: EClassId) -> impl Iterator<Item = &ENode> {
        let root = self.find(class);
        self.nodes
            .iter()
            .filter(move |node| self.find(node.class) == root)
    }

    /// Extracts the minimum-node-count representative reachable from a class and
    /// re-interns it into `sidecar`, returning its [`TermId`]. A purely cyclic
    /// class with no finite base term returns `None`. Ties break on encoded
    /// bytes, so extraction is deterministic.
    pub fn extract_cheapest(
        &self,
        class: EClassId,
        sidecar: &mut TermIdentitySidecar,
    ) -> Option<TermId> {
        #[derive(Clone)]
        struct Best {
            cost: u64,
            encoded: Vec<u8>,
        }
        let mut best = HashMap::<EClassId, Best>::new();
        let max_rounds = self.parents.len().saturating_add(1);
        for _ in 0..max_rounds {
            let mut changed = false;
            for node in &self.nodes {
                let root = self.find(node.class);
                let candidate = match &node.kind {
                    ENodeKind::Leaf(bytes) => Some(Best {
                        cost: 1,
                        encoded: bytes.to_vec(),
                    }),
                    ENodeKind::App { head, children } => {
                        let child_best = children
                            .iter()
                            .copied()
                            .map(|child| best.get(&self.find(child)).cloned())
                            .collect::<Option<Vec<_>>>();
                        child_best.map(|kids| {
                            let cost = 1_u64
                                .saturating_add(kids.iter().map(|best| best.cost).sum::<u64>());
                            let mut encoded = Vec::with_capacity(
                                1 + kids.iter().map(|b| b.encoded.len()).sum::<usize>(),
                            );
                            encoded.push(*head);
                            for kid in &kids {
                                encoded.extend_from_slice(&kid.encoded);
                            }
                            Best { cost, encoded }
                        })
                    }
                };
                if let Some(candidate) = candidate {
                    let replace = best.get(&root).map_or(true, |current| {
                        candidate.cost < current.cost
                            || (candidate.cost == current.cost
                                && candidate.encoded < current.encoded)
                    });
                    if replace {
                        best.insert(root, candidate);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        best.get(&self.find(class)).map(|best| {
            sidecar
                .insert_term(&best.encoded)
                .expect("extracted representative must re-intern")
        })
    }

    /// Cheap structural self-check for tests and assertions.
    pub fn validate(&self) -> Result<(), String> {
        if self.parents.len() != self.ranks.len() {
            return Err("union-find arrays differ in length".into());
        }
        for (index, parent) in self.parents.iter().copied().enumerate() {
            if parent.index() >= self.parents.len() {
                return Err(format!("invalid parent at class {index}"));
            }
            let mut slow = EClassId(index as u32);
            let mut fast = slow;
            for _ in 0..=self.parents.len() {
                slow = self.parents[slow.index()];
                fast = self.parents[self.parents[fast.index()].index()];
                if slow == fast {
                    break;
                }
            }
            if slow != self.find(slow) && self.parents[slow.index()] == slow {
                return Err("union-find corruption".into());
            }
        }
        for node in &self.nodes {
            if node.class.index() >= self.parents.len() {
                return Err("e-node has invalid class".into());
            }
            if let ENodeKind::App { children, .. } = &node.kind {
                if children
                    .iter()
                    .any(|child| child.index() >= self.parents.len())
                {
                    return Err("e-node has invalid child class".into());
                }
            }
        }
        Ok(())
    }
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

    fn intern(sidecar: &mut TermIdentitySidecar, bytes: &[u8]) -> TermId {
        sidecar.insert_term(bytes).expect("test term must intern")
    }

    // f(a) and f(b) are not congruent until a and b are merged, then the rebuild
    // propagates equality up through the shared head.
    #[test]
    fn congruence_rebuild_merges_parents() {
        let mut sidecar = TermIdentitySidecar::new();
        let a = intern(&mut sidecar, &sym(b"a"));
        let b = intern(&mut sidecar, &sym(b"b"));
        let fa = intern(&mut sidecar, &app(&[sym(b"f"), sym(b"a")]));
        let fb = intern(&mut sidecar, &app(&[sym(b"f"), sym(b"b")]));

        let mut graph = EGraph::new();
        let ca = graph.add_term(a, &sidecar);
        let cb = graph.add_term(b, &sidecar);
        let cfa = graph.add_term(fa, &sidecar);
        let cfb = graph.add_term(fb, &sidecar);

        assert!(!graph.equivalent_classes(cfa, cfb));
        graph.union(ca, cb);
        assert!(graph.rebuild() >= 1);
        assert!(graph.equivalent_classes(cfa, cfb));
        graph.validate().unwrap();
    }

    // Congruence with several arguments: f(a,b) = f(c,d) once a=c and b=d.
    #[test]
    fn congruence_closes_over_all_arguments() {
        let mut sidecar = TermIdentitySidecar::new();
        let a = intern(&mut sidecar, &sym(b"a"));
        let b = intern(&mut sidecar, &sym(b"b"));
        let c = intern(&mut sidecar, &sym(b"c"));
        let d = intern(&mut sidecar, &sym(b"d"));
        let fab = intern(&mut sidecar, &app(&[sym(b"f"), sym(b"a"), sym(b"b")]));
        let fcd = intern(&mut sidecar, &app(&[sym(b"f"), sym(b"c"), sym(b"d")]));

        let mut graph = EGraph::new();
        let cfab = graph.add_term(fab, &sidecar);
        let cfcd = graph.add_term(fcd, &sidecar);
        let (ca, cb) = (graph.add_term(a, &sidecar), graph.add_term(b, &sidecar));
        let (cc, cd) = (graph.add_term(c, &sidecar), graph.add_term(d, &sidecar));

        graph.union(ca, cc);
        assert!(graph.rebuild() >= 1);
        // Only one pair merged so far, the applications stay distinct.
        assert!(!graph.equivalent_classes(cfab, cfcd));
        graph.union(cb, cd);
        graph.rebuild();
        assert!(graph.equivalent_classes(cfab, cfcd));
        graph.validate().unwrap();
    }

    // Different heads do not become congruent from equal arguments alone.
    #[test]
    fn distinct_heads_stay_distinct() {
        let mut sidecar = TermIdentitySidecar::new();
        let a = intern(&mut sidecar, &sym(b"a"));
        let b = intern(&mut sidecar, &sym(b"b"));
        let fa = intern(&mut sidecar, &app(&[sym(b"f"), sym(b"a")]));
        let gb = intern(&mut sidecar, &app(&[sym(b"g"), sym(b"b")]));

        let mut graph = EGraph::new();
        let cfa = graph.add_term(fa, &sidecar);
        let cgb = graph.add_term(gb, &sidecar);
        let ca = graph.add_term(a, &sidecar);
        let cb = graph.add_term(b, &sidecar);

        graph.union(ca, cb);
        graph.rebuild();
        // a = b, but f /= g, so f(a) /= g(b).
        assert!(!graph.equivalent_classes(cfa, cgb));
        graph.validate().unwrap();
    }

    // With a = f(a) in the class, extraction picks the finite base term a.
    #[test]
    fn extraction_chooses_smaller_term() {
        let mut sidecar = TermIdentitySidecar::new();
        let a = intern(&mut sidecar, &sym(b"a"));
        let fa = intern(&mut sidecar, &app(&[sym(b"f"), sym(b"a")]));

        let mut graph = EGraph::new();
        let class = graph.add_equivalence(a, fa, &sidecar);
        graph.rebuild();
        let extracted = graph.extract_cheapest(class, &mut sidecar);
        assert_eq!(extracted, Some(a));
    }

    // The end-to-end bridge: load `(= a b)` and `(= b c)` as facts, build the
    // graph from them, and the closure makes a and c equal (and then c its own
    // cheapest representative since all three are single symbols).
    #[test]
    fn equality_facts_close_transitively() {
        let mut sidecar = TermIdentitySidecar::new();
        sidecar
            .insert_fact(&app(&[sym(b"="), sym(b"a"), sym(b"b")]))
            .unwrap();
        sidecar
            .insert_fact(&app(&[sym(b"="), sym(b"b"), sym(b"c")]))
            .unwrap();
        let eq = sidecar.term_id_for_encoded(&sym(b"=")).unwrap();
        let a = sidecar.term_id_for_encoded(&sym(b"a")).unwrap();
        let c = sidecar.term_id_for_encoded(&sym(b"c")).unwrap();

        let mut graph = EGraph::from_equalities(&sidecar, eq);
        assert!(graph.equivalent_terms(a, c, &sidecar));
        graph.validate().unwrap();

        let class = graph.add_term(a, &sidecar);
        // Every member is a one-symbol leaf, so the cheapest is whichever sorts
        // first by encoded bytes; a sorts before b and c.
        assert_eq!(graph.extract_cheapest(class, &mut sidecar), Some(a));
    }
}
