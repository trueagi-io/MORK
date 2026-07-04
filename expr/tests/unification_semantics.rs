use std::collections::BTreeMap;

use mork_expr::{Expr, ExprZipper, Tag, UnificationFailure, item_byte, parse};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum OracleTerm {
    Var(u8),
    Fun(&'static str, Vec<OracleTerm>),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ScopedTerm {
    Var(Side, u8),
    Fun(&'static str, Vec<ScopedTerm>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Side {
    Left,
    Right,
}

#[derive(Debug, Eq, PartialEq)]
enum OracleFailure {
    Difference,
    Occurs,
}

type Substitution = BTreeMap<(Side, u8), ScopedTerm>;

fn var(id: u8) -> OracleTerm {
    OracleTerm::Var(id)
}

fn sym(name: &'static str) -> OracleTerm {
    OracleTerm::Fun(name, Vec::new())
}

fn app(name: &'static str, args: Vec<OracleTerm>) -> OracleTerm {
    OracleTerm::Fun(name, args)
}

fn canonicalize_vars(term: &OracleTerm) -> OracleTerm {
    fn go(term: &OracleTerm, seen: &mut BTreeMap<u8, u8>) -> OracleTerm {
        match term {
            OracleTerm::Var(id) => {
                let next = seen.len() as u8;
                OracleTerm::Var(*seen.entry(*id).or_insert(next))
            }
            OracleTerm::Fun(name, args) => {
                OracleTerm::Fun(name, args.iter().map(|arg| go(arg, seen)).collect())
            }
        }
    }

    go(term, &mut BTreeMap::new())
}

fn scoped(term: &OracleTerm, side: Side) -> ScopedTerm {
    match term {
        OracleTerm::Var(id) => ScopedTerm::Var(side, *id),
        OracleTerm::Fun(name, args) => {
            ScopedTerm::Fun(name, args.iter().map(|arg| scoped(arg, side)).collect())
        }
    }
}

fn encode(term: &OracleTerm) -> Vec<u8> {
    fn go(term: &OracleTerm, vars: &mut BTreeMap<u8, u8>, out: &mut Vec<u8>) {
        match term {
            OracleTerm::Var(id) => {
                let next = vars.len() as u8;
                let intro = *vars.entry(*id).or_insert(next);
                if intro == next {
                    out.push(item_byte(Tag::NewVar));
                } else {
                    out.push(item_byte(Tag::VarRef(intro)));
                }
            }
            OracleTerm::Fun(name, args) => {
                if !args.is_empty() {
                    out.push(item_byte(Tag::Arity((args.len() + 1) as u8)));
                }
                out.push(item_byte(Tag::SymbolSize(name.len() as u8)));
                out.extend_from_slice(name.as_bytes());
                for arg in args {
                    go(arg, vars, out);
                }
            }
        }
    }

    let mut out = Vec::new();
    go(term, &mut BTreeMap::new(), &mut out);
    out
}

fn walk(term: ScopedTerm, substitution: &Substitution) -> ScopedTerm {
    match term {
        ScopedTerm::Var(side, id) => match substitution.get(&(side, id)) {
            Some(bound) => walk(bound.clone(), substitution),
            None => ScopedTerm::Var(side, id),
        },
        ScopedTerm::Fun(name, args) => ScopedTerm::Fun(
            name,
            args.into_iter()
                .map(|arg| walk(arg, substitution))
                .collect(),
        ),
    }
}

fn occurs(var: (Side, u8), term: &ScopedTerm, substitution: &Substitution) -> bool {
    match walk(term.clone(), substitution) {
        ScopedTerm::Var(side, id) => (side, id) == var,
        ScopedTerm::Fun(_, args) => args.iter().any(|arg| occurs(var, arg, substitution)),
    }
}

fn bind(
    var: (Side, u8),
    term: ScopedTerm,
    substitution: &mut Substitution,
) -> Result<(), OracleFailure> {
    match walk(term, substitution) {
        ScopedTerm::Var(side, id) if (side, id) == var => Ok(()),
        term if occurs(var, &term, substitution) => Err(OracleFailure::Occurs),
        term => {
            substitution.insert(var, term);
            Ok(())
        }
    }
}

fn unify_oracle(lhs: ScopedTerm, rhs: ScopedTerm) -> Result<Substitution, OracleFailure> {
    let mut substitution = Substitution::new();
    let mut pending = vec![(lhs, rhs)];

    while let Some((lhs, rhs)) = pending.pop() {
        match (walk(lhs, &substitution), walk(rhs, &substitution)) {
            (ScopedTerm::Var(side, id), term) => bind((side, id), term, &mut substitution)?,
            (term, ScopedTerm::Var(side, id)) => bind((side, id), term, &mut substitution)?,
            (ScopedTerm::Fun(left_name, left_args), ScopedTerm::Fun(right_name, right_args))
                if left_name == right_name && left_args.len() == right_args.len() =>
            {
                pending.extend(left_args.into_iter().zip(right_args));
            }
            _ => return Err(OracleFailure::Difference),
        }
    }

    Ok(substitution)
}

fn format_scoped(term: &ScopedTerm) -> String {
    fn go(term: &ScopedTerm, seen: &mut BTreeMap<(Side, u8), u8>) -> String {
        match term {
            ScopedTerm::Var(side, id) => {
                let next = seen.len() as u8;
                let intro = *seen.entry((*side, *id)).or_insert(next);
                if intro == next {
                    "$".to_string()
                } else {
                    format!("_{}", intro + 1)
                }
            }
            ScopedTerm::Fun(name, args) if args.is_empty() => (*name).to_string(),
            ScopedTerm::Fun(name, args) => {
                let mut formatted = String::from("(");
                formatted.push_str(name);
                for arg in args {
                    formatted.push(' ');
                    formatted.push_str(&go(arg, seen));
                }
                formatted.push(')');
                formatted
            }
        }
    }

    go(term, &mut BTreeMap::new())
}

fn oracle_unify_to_string(lhs: &OracleTerm, rhs: &OracleTerm) -> Result<String, OracleFailure> {
    let lhs = canonicalize_vars(lhs);
    let rhs = canonicalize_vars(rhs);
    let scoped_lhs = scoped(&lhs, Side::Left);
    let scoped_rhs = scoped(&rhs, Side::Right);
    let substitution = unify_oracle(scoped_lhs.clone(), scoped_rhs)?;

    Ok(format_scoped(&walk(scoped_lhs, &substitution)))
}

fn mork_unify_to_string(lhs: &OracleTerm, rhs: &OracleTerm) -> Result<String, UnificationFailure> {
    let lhs = canonicalize_vars(lhs);
    let rhs = canonicalize_vars(rhs);
    let mut lhs = encode(&lhs);
    let mut rhs = encode(&rhs);

    unify_to_string(&mut lhs, &mut rhs)
}

fn oracle_cases() -> Vec<OracleTerm> {
    let atoms = vec![var(0), var(1), sym("a"), sym("b")];
    let mut terms = atoms.clone();

    for arg in &atoms {
        terms.push(app("f", vec![arg.clone()]));
        terms.push(app("g", vec![arg.clone()]));
    }

    for lhs in &atoms {
        for rhs in &atoms {
            terms.push(app("p", vec![lhs.clone(), rhs.clone()]));
        }
    }

    terms.extend([
        app("f", vec![app("g", vec![var(0)])]),
        app("g", vec![app("f", vec![var(0)])]),
        app("p", vec![app("f", vec![var(0)]), var(0)]),
        app("p", vec![var(0), app("f", vec![var(0)])]),
        app("p", vec![app("f", vec![sym("a")]), app("g", vec![var(0)])]),
        app("p", vec![app("f", vec![var(0)]), app("g", vec![var(1)])]),
    ]);

    terms
}

fn expr_from_bytes(bytes: &mut [u8]) -> Expr {
    Expr {
        ptr: bytes.as_mut_ptr(),
    }
}

#[allow(deprecated)] // _unify is the existing engine entry point these tests seal
fn unify_to_string(lhs: &mut [u8], rhs: &mut [u8]) -> Result<String, UnificationFailure> {
    let lhs = expr_from_bytes(lhs);
    let rhs = expr_from_bytes(rhs);
    let mut output = vec![0_u8; 512];
    let mut zipper = ExprZipper::new(expr_from_bytes(&mut output));

    lhs._unify(rhs, &mut zipper)?;

    Ok(format!("{:?}", expr_from_bytes(&mut output)))
}

#[test]
fn unify_materializes_first_order_mgu() {
    let mut lhs = parse!("[2] f $");
    let mut rhs = parse!("[2] f a");

    let result = unify_to_string(&mut lhs, &mut rhs).unwrap();

    assert_eq!(result, "(f a)");
}

#[test]
fn unify_materializes_same_nested_mgu_from_either_side() {
    let mut lhs = parse!("[4] rel $ [2] g _1 [2] h _1");
    let mut rhs = parse!("[4] rel a [2] g a [2] h a");

    let left_first = unify_to_string(&mut lhs, &mut rhs).unwrap();

    let mut lhs = parse!("[4] rel $ [2] g _1 [2] h _1");
    let mut rhs = parse!("[4] rel a [2] g a [2] h a");
    let right_first = unify_to_string(&mut rhs, &mut lhs).unwrap();

    assert_eq!(left_first, "(rel a (g a) (h a))");
    assert_eq!(right_first, left_first);
}

#[test]
fn unify_respects_repeated_variable_constraints() {
    let mut lhs = parse!("[3] pair $ _1");
    let mut rhs = parse!("[3] pair a b");

    let result = unify_to_string(&mut lhs, &mut rhs);

    assert!(matches!(result, Err(UnificationFailure::Difference(_, _))));
}

#[test]
fn unify_respects_repeated_variable_constraints_on_rhs() {
    let mut lhs = parse!("[3] pair a b");
    let mut rhs = parse!("[3] pair $ _1");

    let result = unify_to_string(&mut lhs, &mut rhs);

    assert!(matches!(result, Err(UnificationFailure::Difference(_, _))));
}

#[test]
fn unify_rejects_indirect_occurs_cycles() {
    let mut lhs = parse!(
        "[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ [3] / 1 $ $ _3 \
         [3] \\ _3 [3] * [3] K _1 [3] T _2 _3 [3] * _4 _3"
    );
    let mut rhs = parse!(
        "[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ [3] / 1 $ $ _3 \
         [3] \\ _3 [3] * [3] K _1 [3] T _2 [3] / 1 _3 [3] * _4 _3"
    );

    let result = unify_to_string(&mut lhs, &mut rhs);

    assert!(matches!(result, Err(UnificationFailure::Occurs(_, _))));
}

#[test]
fn unify_keeps_expression_variable_namespaces_separate() {
    let mut lhs = parse!("$");
    let mut rhs = parse!("[2] f $");

    let result = unify_to_string(&mut lhs, &mut rhs).unwrap();

    assert_eq!(result, "(f $)");
}

#[test]
fn unify_remains_first_order_syntactic_without_background_evaluation() {
    let mut lhs = parse!("[3] + 1 2");
    let mut rhs = parse!("3");

    let result = unify_to_string(&mut lhs, &mut rhs);

    assert!(matches!(result, Err(UnificationFailure::Difference(_, _))));
}

#[test]
fn unify_reports_symbol_shape_difference() {
    let mut lhs = parse!("[2] f a");
    let mut rhs = parse!("[2] g a");

    let result = unify_to_string(&mut lhs, &mut rhs);

    assert!(matches!(result, Err(UnificationFailure::Difference(_, _))));
}

#[test]
fn unify_matches_first_order_occurs_check_oracle_on_finite_terms() {
    let cases = oracle_cases();

    for lhs in &cases {
        for rhs in &cases {
            match (
                oracle_unify_to_string(lhs, rhs),
                mork_unify_to_string(lhs, rhs),
            ) {
                (Ok(expected), Ok(actual)) => assert_eq!(actual, expected, "{lhs:?} ~ {rhs:?}"),
                (Err(OracleFailure::Difference), Err(UnificationFailure::Difference(_, _))) => {}
                (Err(OracleFailure::Occurs), Err(UnificationFailure::Occurs(_, _))) => {}
                (expected, actual) => {
                    panic!("{lhs:?} ~ {rhs:?}: expected {expected:?}, got {actual:?}")
                }
            }
        }
    }
}
