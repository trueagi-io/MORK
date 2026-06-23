use mork::__mork_expr::{item_byte, Tag};
use mork::term_identity::{TermIdentitySidecar, TermIdentityStats};
use pathmap::PathMap;

fn sym(bytes: &[u8]) -> Vec<u8> {
    let mut out = vec![item_byte(Tag::SymbolSize(bytes.len() as u8))];
    out.extend_from_slice(bytes);
    out
}

#[test]
fn term_identity_sidecar_builds_from_pathmap_values() {
    let mut ground = vec![item_byte(Tag::Arity(2))];
    ground.extend(sym(b"edge"));
    ground.extend(sym(b"Alice"));

    let mut schematic = vec![item_byte(Tag::Arity(2))];
    schematic.extend(sym(b"edge"));
    schematic.push(item_byte(Tag::VarRef(0)));

    let mut map = PathMap::new();
    map.insert(&ground, ());
    map.insert(&schematic, ());

    let mut sidecar = TermIdentitySidecar::new();

    assert_eq!(sidecar.extend_from_pathmap(&map).unwrap(), 2);
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
