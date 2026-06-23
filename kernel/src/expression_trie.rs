use std::collections::BTreeMap;

use crate::pattern_relations::{
    lower_pattern, match_fact_ids, PatternLoweringError, PatternRelationMatchError,
    PatternRelationMatches,
};
use crate::term_identity::{FactId, TermId, TermIdentitySidecar, TermKind};

/// Typed preorder token used by the derived expression trie.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum ExpressionTrieToken {
    /// Application node with encoded arity.
    App(u8),
    /// Complete interned symbol item.
    Symbol(TermId),
    /// Stored schematic new-variable token.
    NewVar,
    /// Stored schematic variable reference token.
    VarRef(u8),
}

/// Snapshot-local discrimination-trie style index over canonical term roots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpressionTrieIndex {
    nodes: Vec<ExpressionTrieNode>,
    stats: ExpressionTrieStats,
}

/// Counters for expression-trie build and candidate lookup.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ExpressionTrieStats {
    /// Complete facts indexed.
    pub facts_indexed: usize,
    /// Trie nodes allocated, including the root.
    pub trie_nodes: usize,
    /// Typed preorder tokens inserted across all facts.
    pub tokens_indexed: usize,
}

/// Candidate lookup result before exact filtering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpressionTrieCandidates {
    /// Conservative typed prefix used for trie descent.
    pub prefix: Box<[ExpressionTrieToken]>,
    /// Complete facts below the prefix.
    pub facts: Box<[FactId]>,
}

/// Match result from expression-trie candidate retrieval plus exact filtering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpressionTrieMatches {
    /// Prefix-filter candidates.
    pub candidates: ExpressionTrieCandidates,
    /// Exact relationalized pattern matches over the candidate facts.
    pub exact: PatternRelationMatches,
}

/// Errors from expression-trie construction or matching.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExpressionTrieError {
    /// A term referenced by a fact or pattern is absent from the sidecar.
    UnknownTerm { term: TermId },
    /// Pattern lowering failed.
    Lowering(PatternLoweringError),
    /// Exact candidate filtering failed.
    Match(PatternRelationMatchError),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ExpressionTrieNode {
    children: BTreeMap<ExpressionTrieToken, usize>,
    facts: Vec<FactId>,
}

impl ExpressionTrieIndex {
    /// Builds a derived typed expression trie from complete fact roots.
    pub fn build(sidecar: &TermIdentitySidecar) -> Result<Self, ExpressionTrieError> {
        let mut index = Self {
            nodes: vec![ExpressionTrieNode::default()],
            stats: ExpressionTrieStats {
                trie_nodes: 1,
                ..ExpressionTrieStats::default()
            },
        };

        for fact in sidecar.facts() {
            index.insert_fact(sidecar, fact.id, fact.root)?;
        }

        Ok(index)
    }

    /// Build and lookup counters.
    pub fn stats(&self) -> ExpressionTrieStats {
        self.stats
    }

    /// Returns candidate fact IDs for the grounded typed prefix of `pattern`.
    ///
    /// Pattern variables stop prefix extraction because they match complete
    /// subterms of unknown length. Later constants are checked by the exact
    /// relationalized matcher.
    pub fn candidates_for_pattern(
        &self,
        sidecar: &TermIdentitySidecar,
        pattern: TermId,
    ) -> Result<ExpressionTrieCandidates, ExpressionTrieError> {
        let mut prefix = Vec::new();
        append_ground_prefix(sidecar, pattern, &mut prefix)?;
        let facts = self.facts_below_prefix(&prefix);

        Ok(ExpressionTrieCandidates {
            prefix: prefix.into_boxed_slice(),
            facts: facts.into_boxed_slice(),
        })
    }

    /// Prefix-filtered exact matching for one pattern term.
    pub fn match_pattern(
        &self,
        sidecar: &TermIdentitySidecar,
        pattern: TermId,
    ) -> Result<ExpressionTrieMatches, ExpressionTrieError> {
        let candidates = self.candidates_for_pattern(sidecar, pattern)?;
        let plan = lower_pattern(sidecar, pattern).map_err(ExpressionTrieError::Lowering)?;
        let exact = match_fact_ids(sidecar, &plan, candidates.facts.iter().copied())
            .map_err(ExpressionTrieError::Match)?;

        Ok(ExpressionTrieMatches { candidates, exact })
    }

    fn insert_fact(
        &mut self,
        sidecar: &TermIdentitySidecar,
        fact: FactId,
        root: TermId,
    ) -> Result<(), ExpressionTrieError> {
        let mut path = Vec::new();
        append_exact_tokens(sidecar, root, &mut path)?;

        let mut node = 0usize;
        for token in path {
            self.stats.tokens_indexed += 1;
            if let Some(&child) = self.nodes[node].children.get(&token) {
                node = child;
                continue;
            }

            let child = self.nodes.len();
            self.nodes.push(ExpressionTrieNode::default());
            self.nodes[node].children.insert(token, child);
            self.stats.trie_nodes += 1;
            node = child;
        }

        self.nodes[node].facts.push(fact);
        self.stats.facts_indexed += 1;
        Ok(())
    }

    fn facts_below_prefix(&self, prefix: &[ExpressionTrieToken]) -> Vec<FactId> {
        let mut node = 0usize;
        for token in prefix {
            let Some(&child) = self.nodes[node].children.get(token) else {
                return Vec::new();
            };
            node = child;
        }

        let mut facts = Vec::new();
        self.collect_facts(node, &mut facts);
        facts.sort_unstable();
        facts
    }

    fn collect_facts(&self, node: usize, facts: &mut Vec<FactId>) {
        facts.extend_from_slice(&self.nodes[node].facts);
        for &child in self.nodes[node].children.values() {
            self.collect_facts(child, facts);
        }
    }
}

fn append_exact_tokens(
    sidecar: &TermIdentitySidecar,
    term: TermId,
    out: &mut Vec<ExpressionTrieToken>,
) -> Result<(), ExpressionTrieError> {
    let Some(record) = sidecar.get_term(term) else {
        return Err(ExpressionTrieError::UnknownTerm { term });
    };

    match record.kind {
        TermKind::Symbol => out.push(ExpressionTrieToken::Symbol(term)),
        TermKind::Application { arity } => {
            out.push(ExpressionTrieToken::App(arity));
            for &child in record.children() {
                append_exact_tokens(sidecar, child, out)?;
            }
        }
        TermKind::NewVar => out.push(ExpressionTrieToken::NewVar),
        TermKind::VarRef(level) => out.push(ExpressionTrieToken::VarRef(level)),
    }

    Ok(())
}

fn append_ground_prefix(
    sidecar: &TermIdentitySidecar,
    term: TermId,
    out: &mut Vec<ExpressionTrieToken>,
) -> Result<bool, ExpressionTrieError> {
    let Some(record) = sidecar.get_term(term) else {
        return Err(ExpressionTrieError::UnknownTerm { term });
    };

    match record.kind {
        TermKind::Symbol => {
            out.push(ExpressionTrieToken::Symbol(term));
            Ok(true)
        }
        TermKind::Application { arity } => {
            out.push(ExpressionTrieToken::App(arity));
            for &child in record.children() {
                if !append_ground_prefix(sidecar, child, out)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        TermKind::NewVar | TermKind::VarRef(_) => Ok(false),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::space::Space;
    use crate::test_exprs::{
        add_repeated_edge_facts, app, repeated_edge_pattern, repeated_edge_product_roots, sym,
    };

    #[test]
    fn typed_expression_trie_filters_repeated_variable_pattern_before_exact_match() {
        let mut space = Space::new();
        add_repeated_edge_facts(
            &mut space,
            br#"
(node Alice)
(tag Bob)
"#,
        );

        let pattern = repeated_edge_pattern();
        let mut sidecar = TermIdentitySidecar::new();
        let pattern_root = sidecar.insert_term(&pattern).unwrap();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        let index = ExpressionTrieIndex::build(&sidecar).unwrap();

        let matches = index.match_pattern(&sidecar, pattern_root).unwrap();
        let (product_count, product_roots) = repeated_edge_product_roots(&space);
        let trie_roots = matches
            .exact
            .rows
            .iter()
            .map(|row| sidecar.get_term(row.root).unwrap().encoded().to_vec())
            .collect::<BTreeSet<_>>();

        assert_eq!(product_count, 2);
        assert_eq!(matches.exact.stats.matches, product_count);
        assert_eq!(trie_roots, product_roots);
        assert_eq!(matches.candidates.prefix.len(), 2);
        assert_eq!(matches.candidates.facts.len(), 5);
        assert!(matches.candidates.facts.len() < sidecar.stats().facts);
        assert_eq!(
            matches.exact.stats.facts_scanned,
            matches.candidates.facts.len()
        );
    }

    #[test]
    fn typed_expression_trie_exact_ground_prefix_returns_one_candidate() {
        let mut space = Space::new();
        space
            .add_all_sexpr(
                br#"
(edge Alice Bob)
(edge Bob Carol)
(node Alice)
"#,
            )
            .unwrap();

        let pattern = app(&[sym(b"edge"), sym(b"Alice"), sym(b"Bob")]);
        let mut sidecar = TermIdentitySidecar::new();
        let pattern_root = sidecar.insert_term(&pattern).unwrap();
        sidecar.extend_from_pathmap(&space.btm).unwrap();
        let index = ExpressionTrieIndex::build(&sidecar).unwrap();

        let matches = index.match_pattern(&sidecar, pattern_root).unwrap();

        assert_eq!(matches.candidates.facts.len(), 1);
        assert_eq!(matches.candidates.prefix.len(), 4);
        assert_eq!(matches.exact.stats.matches, 1);
        assert_eq!(matches.exact.stats.facts_scanned, 1);
    }
}
