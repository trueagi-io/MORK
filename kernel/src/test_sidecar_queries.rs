use crate::space::Space;
use crate::term_identity::{TermId, TermIdentitySidecar};

fn encoded_expr(space: &mut Space, expr: &'static str) -> Vec<u8> {
    let expr = crate::expr!(space, expr);
    unsafe { expr.span().as_ref().unwrap() }.to_vec()
}

pub(crate) fn transitive_edge_sidecar() -> (Space, TermIdentitySidecar, TermId) {
    let mut space = Space::new();
    space
        .add_all_sexpr(
            br#"
(edge Alice Bob)
(edge Bob Carol)
(edge Alice Dana)
(edge Dana Carol)
(edge Carol Erin)
(edge X Y)
"#,
        )
        .unwrap();

    let mut sidecar = TermIdentitySidecar::new();
    sidecar.extend_from_pathmap(&space.btm).unwrap();
    let edge = sidecar
        .term_id_for_encoded(&encoded_expr(&mut space, "edge"))
        .unwrap();

    (space, sidecar, edge)
}

pub(crate) fn transitive_edge_product_count(space: &mut Space) -> usize {
    let product_pattern = crate::expr!(space, "[3] , [3] edge $ $ [3] edge _2 $");
    Space::query_multi(&space.btm, product_pattern, |_, _| true)
}
