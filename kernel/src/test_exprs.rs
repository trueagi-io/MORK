use std::collections::BTreeSet;

use crate::space::Space;
use mork_expr::{item_byte, Tag};

pub fn sym(bytes: &[u8]) -> Vec<u8> {
    let mut out = vec![item_byte(Tag::SymbolSize(bytes.len() as u8))];
    out.extend_from_slice(bytes);
    out
}

pub fn app(children: &[Vec<u8>]) -> Vec<u8> {
    let mut out = vec![item_byte(Tag::Arity(children.len() as u8))];
    for child in children {
        out.extend_from_slice(child);
    }
    out
}

pub fn var() -> Vec<u8> {
    vec![item_byte(Tag::NewVar)]
}

pub fn var_ref(slot: u8) -> Vec<u8> {
    vec![item_byte(Tag::VarRef(slot))]
}

pub fn repeated_edge_pattern() -> Vec<u8> {
    app(&[sym(b"edge"), var(), app(&[sym(b"f"), var_ref(0)])])
}

pub fn add_repeated_edge_facts(space: &mut Space, extra_facts: &[u8]) {
    let mut facts = br#"
(edge Alice (f Alice))
(edge Alice (f Bob))
(edge Bob (f Bob))
(edge Carol (g Carol))
(edge Dave (f Eve))
"#
    .to_vec();
    facts.extend_from_slice(extra_facts);
    space.add_all_sexpr(&facts).unwrap();
}

pub fn repeated_edge_product_roots(space: &Space) -> (usize, BTreeSet<Vec<u8>>) {
    let product_pattern = crate::expr!(space, "[2] , [3] edge $ [2] f _1");
    let mut product_roots = BTreeSet::new();
    let product_count = Space::query_multi(&space.btm, product_pattern, |_, loc| {
        let span = unsafe { loc.span().as_ref().unwrap() };
        product_roots.insert(span.to_vec());
        true
    });
    (product_count, product_roots)
}
