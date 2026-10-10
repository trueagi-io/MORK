//! The exec special-form contract, pinned as behavior tests.
//!
//! `Space::interpret` accepts `(exec <loc> <patterns> <templates>)` where the
//! pattern functor is `,` or `I` and the template functor is `,` or `O`; any
//! other shape is rejected. `metta_calculus` removes an exec from the space
//! before interpreting it, so a rejected exec is consumed without effect. These
//! tests pin that surface: the four valid functor combinations do their work,
//! the invalid ones are consumed as no-ops, and an exec written by a template is
//! scheduled like any other.

use mork::space::Space;

fn run(program: &[u8]) -> String {
    let mut s = Space::new();
    s.add_all_sexpr(program).unwrap();
    s.metta_calculus(100);
    let mut out = Vec::new();
    s.dump_all_sexpr(&mut out).unwrap();
    String::from_utf8_lossy(&out).into_owned()
}

#[test]
fn comma_comma_exec_rewrites_and_is_consumed() {
    let dump = run(b"(edge a b)\n(exec 0 (, (edge $x $y)) (, (path $x $y)))\n");
    assert!(dump.contains("(path a b)"), "template not applied:\n{dump}");
    assert!(!dump.contains("(exec"), "exec not consumed:\n{dump}");
    assert!(dump.contains("(edge a b)"), "matched fact must remain:\n{dump}");
}

#[test]
fn i_o_exec_sources_bind_and_sinks_apply() {
    // (== <pattern> $r) binds $r to the very atom the pattern matched, so the
    // O template can both add a derived atom and remove the consumed one.
    let dump = run(b"(q 7)\n(exec 0 (I (== (q $x) $r)) (O (+ (got $x)) (- $r)))\n");
    assert!(dump.contains("(got 7)"), "add sink did not fire:\n{dump}");
    assert!(!dump.contains("(q 7)"), "remove sink did not consume the source atom:\n{dump}");
}

#[test]
fn invalid_template_functor_is_consumed_without_effect() {
    let dump = run(b"(edge a b)\n(exec 0 (, (edge $x $y)) (X (path $x $y)))\n");
    assert!(!dump.contains("(path"), "rejected template must not run:\n{dump}");
    assert!(!dump.contains("(exec"), "rejected exec must still be consumed:\n{dump}");
    assert!(dump.contains("(edge a b)"), "space must be otherwise untouched:\n{dump}");
}

#[test]
fn invalid_pattern_functor_is_consumed_without_effect() {
    let dump = run(b"(edge a b)\n(exec 0 (Q (edge $x $y)) (, (path $x $y)))\n");
    assert!(!dump.contains("(path"), "rejected pattern must not run:\n{dump}");
    assert!(!dump.contains("(exec"), "rejected exec must still be consumed:\n{dump}");
}

#[test]
fn symbol_pattern_is_rejected_and_consumed() {
    let dump = run(b"(exec 0 foo (, (made a)))\n");
    assert!(!dump.contains("(made"), "symbol pattern must be rejected:\n{dump}");
    assert!(!dump.contains("(exec"), "rejected exec must still be consumed:\n{dump}");
}

#[test]
fn exec_template_can_schedule_further_execs() {
    // An exec written by a template is a plain atom under the exec prefix, so the
    // calculus loop picks it up on a later step: self-scheduling.
    let dump = run(b"(seed 5)\n(exec 0 (, (seed $x)) (, (exec 1 (, (seed $y)) (, (grown $y)))))\n");
    assert!(dump.contains("(grown 5)"), "respawned exec did not run:\n{dump}");
    assert!(!dump.contains("(exec"), "all execs must be consumed at fixpoint:\n{dump}");
}
