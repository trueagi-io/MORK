use mork::__mork_expr::{Tag, item_byte};
use mork::term_identity::{TermIdentitySidecar, TermIdentityStats};

fn sym(bytes: &[u8]) -> Vec<u8> {
    let mut out = vec![item_byte(Tag::SymbolSize(bytes.len() as u8))];
    out.extend_from_slice(bytes);
    out
}

#[test]
fn term_identity_sidecar_interns_ground_and_schematic_facts() {
    let mut ground = vec![item_byte(Tag::Arity(2))];
    ground.extend(sym(b"edge"));
    ground.extend(sym(b"Alice"));

    let mut schematic = vec![item_byte(Tag::Arity(2))];
    schematic.extend(sym(b"edge"));
    schematic.push(item_byte(Tag::VarRef(0)));

    let mut sidecar = TermIdentitySidecar::new();
    sidecar.insert_fact(&ground).unwrap();
    sidecar.insert_fact(&schematic).unwrap();

    assert_eq!(
        sidecar.stats(),
        TermIdentityStats {
            terms: 5,
            facts: 2,
            ground_facts: 1,
            schematic_facts: 1,
            subterms: 3,
            encoded_bytes: sidecar.stats().encoded_bytes,
            max_depth: 2,
            hash_buckets: 5,
            hash_collision_candidates: 0,
            generation: 2,
        }
    );
}

fn app(children: &[Vec<u8>]) -> Vec<u8> {
    let mut out = vec![item_byte(Tag::Arity(children.len() as u8))];
    for child in children {
        out.extend_from_slice(child);
    }
    out
}

#[test]
fn insert_term_returns_stable_identity() {
    let mut sidecar = TermIdentitySidecar::new();
    let edge = app(&[sym(b"edge"), sym(b"a"), sym(b"b")]);

    let first = sidecar.insert_term(&edge).unwrap();
    let second = sidecar.insert_term(&edge).unwrap();

    assert_eq!(first, second);
    assert_eq!(sidecar.term_id_for_encoded(&edge), Some(first));
}

#[test]
fn fact_liveness_tracks_insert_remove_and_revive() {
    let mut sidecar = TermIdentitySidecar::new();
    let fact = app(&[sym(b"edge"), sym(b"a"), sym(b"b")]);

    let id = sidecar.insert_fact(&fact).unwrap();
    assert!(sidecar.is_fact_live(id));
    assert_eq!(sidecar.live_fact_count(), 1);

    assert!(sidecar.remove_fact(&fact));
    assert!(!sidecar.is_fact_live(id));
    assert_eq!(sidecar.live_fact_count(), 0);
    assert!(!sidecar.remove_fact(&fact));

    let revived = sidecar.insert_fact(&fact).unwrap();
    assert_eq!(revived, id);
    assert!(sidecar.is_fact_live(id));
    assert_eq!(sidecar.live_fact_count(), 1);
}

#[test]
fn facts_for_relation_groups_by_head() {
    let mut sidecar = TermIdentitySidecar::new();
    let edge = sidecar.insert_term(&sym(b"edge")).unwrap();

    let e1 = sidecar
        .insert_fact(&app(&[sym(b"edge"), sym(b"a"), sym(b"b")]))
        .unwrap();
    let e2 = sidecar
        .insert_fact(&app(&[sym(b"edge"), sym(b"b"), sym(b"c")]))
        .unwrap();
    sidecar
        .insert_fact(&app(&[sym(b"node"), sym(b"a")]))
        .unwrap();

    let mut edge_facts = sidecar.facts_for_relation(edge).to_vec();
    edge_facts.sort();
    let mut expected = vec![e1, e2];
    expected.sort();
    assert_eq!(edge_facts, expected);
}
