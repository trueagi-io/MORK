use std::collections::HashMap;

use mork_expr::{Tag, maybe_byte_item, Expr};

/// Canonical identity for an encoded MORK term or subterm.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct TermId(pub u64);

/// Canonical identity for a complete fact present in a pathspace snapshot.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FactId(pub u32);

/// Small structural flags cached for every interned term.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TermFlags {
    /// The term contains no encoded MORK variables.
    pub ground: bool,
    /// The term contains a `NewVar` or `VarRef` item.
    pub contains_vars: bool,
}

impl TermFlags {
    fn ground() -> Self {
        Self {
            ground: true,
            contains_vars: false,
        }
    }

    fn schematic() -> Self {
        Self {
            ground: false,
            contains_vars: true,
        }
    }
}

/// Shape tag for an interned encoded term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TermKind {
    /// Complete symbol item: `SymbolSize(n)` plus payload bytes.
    Symbol,
    /// Application with the encoded arity.
    Application { arity: u8 },
    /// New variable item.
    NewVar,
    /// Reference to a previously introduced variable level.
    VarRef(u8),
}

/// Interned term metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermRecord {
    /// Canonical term identity.
    pub id: TermId,
    /// Term shape.
    pub kind: TermKind,
    /// Cached ground/schematic flags.
    pub flags: TermFlags,
    /// Deterministic structural hash. Hash equality is only a filter; encoded
    /// bytes are compared exactly before identities are reused.
    pub structural_hash: u128,
    /// Encoded byte length of this exact term.
    pub encoded_len: u32,
    /// Maximum nested expression depth, counting leaves as depth 1.
    pub depth: u16,
    /// Number of term nodes in this expression tree.
    pub node_count: u32,
    encoded: Box<[u8]>,
    children: Box<[TermId]>,
}

impl TermRecord {
    /// Exact encoded bytes represented by this term identity.
    pub fn encoded(&self) -> &[u8] {
        &self.encoded
    }

    /// Child term identities for applications; empty for leaves.
    pub fn children(&self) -> &[TermId] {
        &self.children
    }
}

/// Complete fact metadata derived from a pathspace value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FactRecord {
    /// Canonical fact identity.
    pub id: FactId,
    /// Root term for this fact.
    pub root: TermId,
    /// Structural hash copied from the root term.
    pub structural_hash: u128,
    /// Root term flags.
    pub flags: TermFlags,
    /// Sidecar generation at which this fact was inserted.
    pub generation: u32,
}

/// Read-only counters for a [`TermIdentitySidecar`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TermIdentityStats {
    /// Number of interned complete terms and subterms.
    pub terms: usize,
    /// Number of complete facts.
    pub facts: usize,
    /// Number of facts whose root term is ground.
    pub ground_facts: usize,
    /// Number of facts whose root term contains variables.
    pub schematic_facts: usize,
    /// Interned terms that are not complete fact roots.
    pub subterms: usize,
    /// Bytes retained by exact interned term encodings.
    pub encoded_bytes: usize,
    /// Maximum observed term depth.
    pub max_depth: u16,
    /// Number of structural-hash buckets.
    pub hash_buckets: usize,
    /// Extra candidates inside non-singleton structural-hash buckets.
    pub hash_collision_candidates: usize,
    /// Current sidecar generation.
    pub generation: u32,
}

/// Parse error for malformed encoded MORK terms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermParseError {
    /// Byte offset at which parsing failed.
    pub offset: usize,
    /// Specific parse failure.
    pub kind: TermParseErrorKind,
}

/// Specific encoded-term parse failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermParseErrorKind {
    /// The input ended before another item could be read.
    UnexpectedEnd,
    /// The byte is reserved by the encoding and is not a valid item tag.
    ReservedTag(u8),
    /// A symbol item declared more payload bytes than remain in the input.
    TruncatedSymbol { len: usize, remaining: usize },
    /// A complete expression was parsed before the end of the provided slice.
    TrailingBytes { parsed_len: usize, total_len: usize },
    /// More than `u32::MAX` complete facts were inserted.
    TooManyFacts,
}

/// Derived canonical identity sidecar for encoded MORK facts and subfacts.
#[derive(Clone, Debug, Default)]
pub struct TermIdentitySidecar {
    terms: Vec<TermRecord>,
    facts: Vec<FactRecord>,
    /// Liveness weight per fact, parallel to `facts` and indexed by `FactId`. A
    /// fact is present iff its weight is positive. Removal tombstones (sets the
    /// weight to 0) instead of compacting, so postings keyed on `FactId` stay
    /// valid; this is the Lucene "live documents" deletion model. Re-insertion
    /// revives the fact.
    fact_weight: Vec<i64>,
    hash_buckets: HashMap<u128, Vec<TermId>>,
    fact_by_term: HashMap<TermId, FactId>,
    encoded_bytes: usize,
    max_depth: u16,
    generation: u32,
    /// Facts grouped by relation head (the root term's first child). Lets a
    /// consumer (`EGraph::from_equalities`, `RelationAdjacency::from_sidecar`)
    /// scan one relation's facts instead of the whole sidecar. Entries are never
    /// removed (a tombstoned or rolled-back `FactId` stays), because consumers
    /// already filter by liveness and by head, so stale entries are skipped, not
    /// wrong.
    facts_by_relation: HashMap<TermId, Vec<FactId>>,
}

impl TermIdentitySidecar {
    /// Creates an empty derived identity sidecar.
    pub fn new() -> Self {
        Self::default()
    }

    /// Interns one complete encoded term and all of its subterms without adding
    /// a complete fact record.
    pub fn insert_term(&mut self, encoded: &[u8]) -> Result<TermId, TermParseError> {
        let (parsed, _) = self.intern_complete(encoded)?;
        Ok(parsed.id)
    }

    /// Interns one complete encoded fact and all of its subterms.
    ///
    /// Re-inserting the same complete fact returns the existing [`FactId`].
    pub fn insert_fact(&mut self, encoded: &[u8]) -> Result<FactId, TermParseError> {
        let (parsed, mark) = self.intern_complete(encoded)?;

        if let Some(&fact) = self.fact_by_term.get(&parsed.id) {
            // Revive a tombstoned fact on re-insert. Set semantics: presence is
            // binary, so clamp the weight at 1 rather than counting derivations.
            let weight = &mut self.fact_weight[fact.0 as usize];
            if *weight <= 0 {
                *weight = 1;
                self.generation = self.generation.saturating_add(1);
            }
            return Ok(fact);
        }

        let fact_index = match u32::try_from(self.facts.len()) {
            Ok(fact_index) => fact_index,
            Err(_) => {
                self.rollback_to(mark);
                return Err(TermParseError {
                    offset: 0,
                    kind: TermParseErrorKind::TooManyFacts,
                });
            }
        };
        self.generation = self.generation.saturating_add(1);

        let root = self.term(parsed.id);
        let relation_head = root.children().first().copied();
        let fact = FactRecord {
            id: FactId(fact_index),
            root: parsed.id,
            structural_hash: root.structural_hash,
            flags: root.flags,
            generation: self.generation,
        };

        self.facts.push(fact);
        self.fact_weight.push(1);
        self.fact_by_term.insert(parsed.id, fact.id);
        if let Some(head) = relation_head {
            self.facts_by_relation
                .entry(head)
                .or_default()
                .push(fact.id);
        }
        Ok(fact.id)
    }

    /// Removes a fact, tombstoning it if it is present and live. Returns `true`
    /// when the fact was live and is now removed, `false` when it was absent or
    /// already dead. The `FactRecord` and `FactId` are retained (weight set to 0)
    /// so arrangement and trie postings keyed on `FactId` stay valid; a later
    /// `insert_fact` of the same fact revives the same `FactId`. This is the
    /// Lucene "live documents" deletion model (flip a liveness bit, leave the
    /// immutable postings, reclaim space only on an optional later compaction)
    /// and the counting algorithm for multiset view maintenance (Gupta, Mumick,
    /// Subrahmanian, "Maintaining Views Incrementally", SIGMOD 1993).
    pub fn remove_fact(&mut self, encoded: &[u8]) -> bool {
        let Some(term) = self.term_id_for_encoded(encoded) else {
            return false;
        };
        let Some(&fact) = self.fact_by_term.get(&term) else {
            return false;
        };
        let weight = &mut self.fact_weight[fact.0 as usize];
        if *weight <= 0 {
            return false;
        }
        *weight = 0;
        self.generation = self.generation.saturating_add(1);
        true
    }

    /// Whether a fact is currently live (present in the snapshot). A tombstoned
    /// fact is retained for `FactId` stability but is not live; consumers that
    /// scan `facts()` must skip dead facts via this check.
    pub fn is_fact_live(&self, fact: FactId) -> bool {
        self.fact_weight
            .get(fact.0 as usize)
            .is_some_and(|&weight| weight > 0)
    }

    /// Count of live facts. Tombstoned facts still occupy a `FactId` slot but are
    /// not counted.
    pub fn live_fact_count(&self) -> usize {
        self.fact_weight
            .iter()
            .filter(|&&weight| weight > 0)
            .count()
    }

    /// Returns a term record by identity.
    pub fn get_term(&self, id: TermId) -> Option<&TermRecord> {
        self.terms.get(id.0 as usize)
    }

    /// Returns a fact record by identity.
    pub fn get_fact(&self, id: FactId) -> Option<&FactRecord> {
        self.facts.get(id.0 as usize)
    }

    /// Returns complete fact records in insertion order.
    pub fn facts(&self) -> &[FactRecord] {
        &self.facts
    }

    /// Fact ids under a relation head (the root term's first child): the bounded
    /// scan set for arrangement build. Empty for an unknown relation. May contain
    /// tombstoned or stale ids, which the caller filters by liveness and head.
    pub fn facts_for_relation(&self, relation: TermId) -> &[FactId] {
        self.facts_by_relation
            .get(&relation)
            .map_or(&[][..], |facts| facts.as_slice())
    }

    /// Returns the existing identity for `encoded` if it has already been interned.
    pub fn term_id_for_encoded(&self, encoded: &[u8]) -> Option<TermId> {
        let hash = structural_hash(encoded);
        self.hash_buckets.get(&hash)?.iter().copied().find(|&id| {
            self.get_term(id)
                .is_some_and(|record| record.encoded() == encoded)
        })
    }

    /// Returns sidecar counters without exposing retained encodings.
    pub fn stats(&self) -> TermIdentityStats {
        let mut stats = TermIdentityStats {
            terms: self.terms.len(),
            facts: self.facts.len(),
            subterms: self.terms.len().saturating_sub(self.facts.len()),
            encoded_bytes: self.encoded_bytes,
            max_depth: self.max_depth,
            hash_buckets: self.hash_buckets.len(),
            generation: self.generation,
            ..TermIdentityStats::default()
        };

        for fact in &self.facts {
            if fact.flags.ground {
                stats.ground_facts += 1;
            } else {
                stats.schematic_facts += 1;
            }
        }

        stats.hash_collision_candidates = self
            .hash_buckets
            .values()
            .map(|bucket| bucket.len().saturating_sub(1))
            .sum();

        stats
    }

    fn term(&self, id: TermId) -> &TermRecord {
        self.get_term(id)
            .expect("TermId should refer to an interned record")
    }

    fn intern_complete(
        &mut self,
        encoded: &[u8],
    ) -> Result<(ParsedTerm, SidecarMark), TermParseError> {
        let mark = self.mark();
        let parsed = match self.intern_at(encoded, 0) {
            Ok(parsed) => parsed,
            Err(error) => {
                self.rollback_to(mark);
                return Err(error);
            }
        };

        if parsed.end != encoded.len() {
            self.rollback_to(mark);
            return Err(TermParseError {
                offset: parsed.end,
                kind: TermParseErrorKind::TrailingBytes {
                    parsed_len: parsed.end,
                    total_len: encoded.len(),
                },
            });
        }

        Ok((parsed, mark))
    }

    fn mark(&self) -> SidecarMark {
        SidecarMark {
            terms: self.terms.len(),
            facts: self.facts.len(),
            encoded_bytes: self.encoded_bytes,
            max_depth: self.max_depth,
            generation: self.generation,
        }
    }

    fn rollback_to(&mut self, mark: SidecarMark) {
        while self.terms.len() > mark.terms {
            let Some(record) = self.terms.pop() else {
                break;
            };

            let empty = if let Some(bucket) = self.hash_buckets.get_mut(&record.structural_hash) {
                bucket.retain(|&id| id != record.id);
                bucket.is_empty()
            } else {
                false
            };

            if empty {
                self.hash_buckets.remove(&record.structural_hash);
            }
        }

        while self.facts.len() > mark.facts {
            let Some(fact) = self.facts.pop() else {
                break;
            };
            self.fact_by_term.remove(&fact.root);
        }
        self.fact_weight.truncate(self.facts.len());

        self.encoded_bytes = mark.encoded_bytes;
        self.max_depth = mark.max_depth;
        self.generation = mark.generation;
    }

    fn intern_at(&mut self, encoded: &[u8], offset: usize) -> Result<ParsedTerm, TermParseError> {
        let Some(&byte) = encoded.get(offset) else {
            return Err(TermParseError {
                offset,
                kind: TermParseErrorKind::UnexpectedEnd,
            });
        };

        match maybe_byte_item(byte).map_err(|reserved| TermParseError {
            offset,
            kind: TermParseErrorKind::ReservedTag(reserved),
        })? {
            Tag::NewVar => {
                let id = self.intern_term(
                    &encoded[offset..offset + 1],
                    TermKind::NewVar,
                    TermFlags::schematic(),
                    Vec::new(),
                    1,
                    1,
                );
                Ok(ParsedTerm {
                    id,
                    end: offset + 1,
                })
            }
            Tag::VarRef(level) => {
                let id = self.intern_term(
                    &encoded[offset..offset + 1],
                    TermKind::VarRef(level),
                    TermFlags::schematic(),
                    Vec::new(),
                    1,
                    1,
                );
                Ok(ParsedTerm {
                    id,
                    end: offset + 1,
                })
            }
            Tag::SymbolSize(len) => {
                let len = usize::from(len);
                let payload_start = offset + 1;
                let end = payload_start + len;
                if end > encoded.len() {
                    return Err(TermParseError {
                        offset,
                        kind: TermParseErrorKind::TruncatedSymbol {
                            len,
                            remaining: encoded.len().saturating_sub(payload_start),
                        },
                    });
                }

                let id = self.intern_term(
                    &encoded[offset..end],
                    TermKind::Symbol,
                    TermFlags::ground(),
                    Vec::new(),
                    1,
                    1,
                );
                Ok(ParsedTerm { id, end })
            }
            Tag::Arity(arity) => {
                let mut cursor = offset + 1;
                let mut children = Vec::with_capacity(usize::from(arity));
                let mut flags = TermFlags::ground();
                let mut depth = 1u16;
                let mut node_count = 1u32;

                for _ in 0..arity {
                    let child = self.intern_at(encoded, cursor)?;
                    cursor = child.end;

                    let child_record = self.term(child.id);
                    flags.contains_vars |= child_record.flags.contains_vars;
                    flags.ground &= child_record.flags.ground;
                    depth = depth.max(child_record.depth.saturating_add(1));
                    node_count = node_count.saturating_add(child_record.node_count);
                    children.push(child.id);
                }

                let id = self.intern_term(
                    &encoded[offset..cursor],
                    TermKind::Application { arity },
                    flags,
                    children,
                    depth,
                    node_count,
                );
                Ok(ParsedTerm { id, end: cursor })
            }
        }
    }

    fn intern_term(
        &mut self,
        encoded: &[u8],
        kind: TermKind,
        flags: TermFlags,
        children: Vec<TermId>,
        depth: u16,
        node_count: u32,
    ) -> TermId {
        let hash = structural_hash(encoded);
        if let Some(bucket) = self.hash_buckets.get(&hash) {
            for &candidate in bucket {
                if self.term(candidate).encoded() == encoded {
                    return candidate;
                }
            }
        }

        let id = TermId(self.terms.len() as u64);
        let encoded_len = u32::try_from(encoded.len()).unwrap_or(u32::MAX);
        self.encoded_bytes = self.encoded_bytes.saturating_add(encoded.len());
        self.max_depth = self.max_depth.max(depth);

        self.terms.push(TermRecord {
            id,
            kind,
            flags,
            structural_hash: hash,
            encoded_len,
            depth,
            node_count,
            encoded: encoded.to_vec().into_boxed_slice(),
            children: children.into_boxed_slice(),
        });
        self.hash_buckets.entry(hash).or_default().push(id);

        id
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ParsedTerm {
    id: TermId,
    end: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SidecarMark {
    terms: usize,
    facts: usize,
    encoded_bytes: usize,
    max_depth: u16,
    generation: u32,
}

/// Deterministic 128-bit structural hash for an exact encoded term, reusing the
/// canonical `Expr::hash` (gxhash128 over the term's byte span) rather than a
/// hand-rolled hash. The hash is only a collision-bucket filter -- exact bytes are
/// compared before an identity is reused -- so any deterministic hash is sound;
/// this just stops reimplementing one (Alloy fac22_term_identity: the swap
/// preserves canonical identity). `encoded` must be exactly one encoded term.
pub fn structural_hash(encoded: &[u8]) -> u128 {
    if encoded.is_empty() {
        return 0;
    }
    unsafe { Expr { ptr: encoded.as_ptr() as *mut u8 }.hash() }
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

    #[test]
    fn insert_fact_interns_complete_expression_and_subterms() {
        let mut encoded = vec![item_byte(Tag::Arity(3))];
        encoded.extend(sym(b"edge"));
        encoded.extend(sym(b"Alice"));
        let inner_start = encoded.len();
        encoded.push(item_byte(Tag::Arity(2)));
        encoded.extend(sym(b"f"));
        encoded.extend(sym(b"Bob"));
        let inner = encoded[inner_start..].to_vec();

        let mut sidecar = TermIdentitySidecar::new();
        let fact = sidecar.insert_fact(&encoded).unwrap();
        let root = sidecar.get_fact(fact).unwrap().root;
        let root_record = sidecar.get_term(root).unwrap();

        assert_eq!(root_record.kind, TermKind::Application { arity: 3 });
        assert_eq!(root_record.children().len(), 3);
        assert_eq!(root_record.flags, TermFlags::ground());
        assert_eq!(root_record.node_count, 6);
        assert!(sidecar.term_id_for_encoded(&inner).is_some());
        assert_eq!(
            sidecar.stats(),
            TermIdentityStats {
                terms: 6,
                facts: 1,
                ground_facts: 1,
                schematic_facts: 0,
                subterms: 5,
                encoded_bytes: sidecar.stats().encoded_bytes,
                max_depth: 3,
                hash_buckets: 6,
                hash_collision_candidates: 0,
                generation: 1,
            }
        );
    }

    #[test]
    fn duplicate_complete_fact_reuses_fact_identity() {
        let mut encoded = vec![item_byte(Tag::Arity(2))];
        encoded.extend(sym(b"foo"));
        encoded.extend(sym(b"bar"));

        let mut sidecar = TermIdentitySidecar::new();
        let first = sidecar.insert_fact(&encoded).unwrap();
        let second = sidecar.insert_fact(&encoded).unwrap();

        assert_eq!(first, second);
        assert_eq!(sidecar.stats().facts, 1);
        assert_eq!(sidecar.stats().terms, 3);
    }

    #[test]
    fn insert_term_does_not_create_fact_record() {
        let mut encoded = vec![item_byte(Tag::Arity(2))];
        encoded.extend(sym(b"pattern"));
        encoded.push(item_byte(Tag::NewVar));

        let mut sidecar = TermIdentitySidecar::new();
        let root = sidecar.insert_term(&encoded).unwrap();

        assert_eq!(
            sidecar.get_term(root).unwrap().kind,
            TermKind::Application { arity: 2 }
        );
        assert_eq!(sidecar.stats().facts, 0);
        assert!(sidecar.facts().is_empty());
    }

    #[test]
    fn variable_bearing_fact_is_classified_as_schematic() {
        let mut encoded = vec![item_byte(Tag::Arity(2))];
        encoded.extend(sym(b"fact"));
        encoded.push(item_byte(Tag::NewVar));

        let mut sidecar = TermIdentitySidecar::new();
        let fact = sidecar.insert_fact(&encoded).unwrap();

        assert!(!sidecar.get_fact(fact).unwrap().flags.ground);
        assert!(sidecar.get_fact(fact).unwrap().flags.contains_vars);
        assert_eq!(sidecar.stats().schematic_facts, 1);
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        let encoded = [item_byte(Tag::SymbolSize(1)), b'x', b'y'];
        let mut sidecar = TermIdentitySidecar::new();

        assert_eq!(
            sidecar.insert_fact(&encoded).unwrap_err(),
            TermParseError {
                offset: 2,
                kind: TermParseErrorKind::TrailingBytes {
                    parsed_len: 2,
                    total_len: 3,
                },
            }
        );
        assert_eq!(sidecar.stats(), TermIdentityStats::default());
    }
}
