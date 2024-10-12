#![cfg(test)]

use crate::*;

#[test]
fn test_examples() {
  #![allow(non_snake_case)]
  #![cfg_attr(rustfmt, rustfmt::skip)]

  let sym = |c| Val::atom(Sym::new(c));
  let [f, g, h] = ["f", "g", "h"].map(sym);
  let [a, b, c] = ["a", "b", "c"].map(sym);
  let [A, B, C] = ["A", "B", "C"].map(sym);
  let S = sym("S");
  let [eq, comma, colon, arrow, star, plus] = ["=", ",", ":", "-->", "*", "+"].map(sym);

  let parse = |src| test_parser::DyckParser::new(src).next().unwrap().unwrap();
  type ParserOutput = (DyckStructureZipperU64, Vec<Val>, test_parser::Variables);
  let [e1, e2, e3, r1] = ["(f $x a)", "(f $x $y $y $x)", "(f $y (g $y $x))", "(= (f (, $x (g (g $y)))) (h (, $x (g a)) (, $x (g $y))))"].map(parse);

  // fn atom(a: Sym) -> Val {
  //   a
  // }
  fn atoms<const L: usize>(a: [Sym; L]) -> [Val; L] {
a.map(Val::atom)
  }

  '_foldMap_size_fvars: {
// shared/src/test/scala/ExprTest.scala
// ```scala
//   test("foldMap size fvars") {
//   assert(e1.size == 5)
//   assert(e1.fvars == Seq(1, 10))
//   assert(e2.size == 9)
//   assert(e2.fvars == Seq(1))
//   assert(e3.size == 9)
//   assert(e2.fvars == Seq(1))
// }
// ```

// `size` can be computed with the dyck word, though to emulate the scala test, we have to include branches too
// `fvars`` can be done with just an slice filter
let size = |&(DyckStructureZipperU64 { structure, .. }, _, _): &ParserOutput| u64::BITS - structure.leading_zeros();
let fvars = |(_, data, _): &ParserOutput| {
  data
    .iter()
    .copied()
    .filter(|e| match e.decode_val() {
      ValPattern::Atom(_) => true,
      _ => false,
    })
    .collect::<Vec<_>>()
};

core::assert_eq!(size(&e1), 5);
core::assert_eq!(&fvars(&e1), &[f, a]);

core::assert_eq!(size(&e2), 9);
core::assert_eq!(&fvars(&e2), &[f]);

core::assert_eq!(size(&e3), 9);
core::assert_eq!(&fvars(&e3), &[f, g]);
  }

  '_toAbsolute_toRelative: {
// shared/src/test/scala/ExprTest.scala
// ```scala
// test("toAbsolute toRelative") {
//   val e1a = Expr(f, Expr.Var(-100), a)
//   val e2a = Expr(f, Expr.Var(-100), Expr.Var(-101), Expr.Var(-101), Expr.Var(-100))
//   val e3a = Expr(f, Expr.Var(-100), Expr(g, Expr.Var(-100), Expr.Var(-101)))
//   assert(e1.toAbsolute(100) == e1a)
//   assert(e2.toAbsolute(100) == e2a)
//   assert(e3.toAbsolute(100) == e3a)
//   assert(e1a.toRelative == e1)
//   assert(e2a.toRelative == e2)
//   assert(e3a.toRelative == e3)
//   assert(r1.toAbsolute(100).toRelative == r1)
//   assert(r1.toAbsolute(100).toRelative.toAbsolute(200) == r1.toAbsolute(200))
// }
// ```

// changing the variables is structure independant, we need only change the underlying slice


let e1a = [f, Val(-100), a];
let e2a = [f, Val(-100), Val(-101), Val(-101), Val(-100)];
let e3a = [f, Val(-100), g, Val(-100), Val(-101)];

core::assert_eq! {&to_absolute(&e1.1, 100), &e1a}
core::assert_eq! {&to_absolute(&e2.1, 100), &e2a}
core::assert_eq! {&to_absolute(&e3.1, 100), &e3a}

core::assert_eq! {&to_relative(&e1a), &e1.1}
core::assert_eq! {&to_relative(&e2a), &e2.1}
core::assert_eq! {&to_relative(&e3a), &e3.1}

core::assert_eq! { &to_relative(&to_absolute(&r1.1, 100)), &r1.1 }
core::assert_eq! { &to_absolute(&to_relative(&to_absolute(&r1.1, 200)), 100), &to_absolute(&r1.1, 100) }
  }

  '_substReIndex: {
// shared/src/test/scala/ExprTest.scala
// ```scala
// test("substReIndex") {
//   val r1 = Expr(f, $, _1)
//   assert(r1.substReIndex(Seq($)) == r1)
//   assert(r1.substReIndex(Seq(Expr(a, $, $))) == Expr(f, Expr(a, $, $), Expr(a, _1, _2)))
//   val r2 = Expr(f, $, $, _1)
//   assert(r2.substReIndex(Seq(Expr(a, $, $), A)) == Expr(f, Expr(a, $, $), A, Expr(a, _1, _2)))
//   assert(r2.substReIndex(Seq(Expr(a, $, $), $)) == Expr(f, Expr(a, $, $), $, Expr(a, _1, _2)))
//   assert(r2.substReIndex(Seq(Expr(a, $, _1), $)) == Expr(f, Expr(a, $, _1), $, Expr(a, _1, _1)))
//   val r3 = Expr(`,`, Expr(f, $, $), Expr(g, _2, $, _3))
//   assert(r3.substReIndex(Seq(a, b, c)) == Expr(`,`, Expr(f, a, b), Expr(g, b, c, c)))
//   assert(r3.substReIndex(Seq(a, $, c)) == Expr(`,`, Expr(f, a, $), Expr(g, _1, c, c)))
//   assert(r3.substReIndex(Seq(a, $, $)) == Expr(`,`, Expr(f, a, $), Expr(g, _1, $, _2)))
//   assert(r3.substReIndex(Seq($, $, $)) == Expr(`,`, Expr(f, $, $), Expr(g, _2, $, _3)))
//   assert(r3.substReIndex(Seq(a, Expr(B, $, $), c)) == Expr(`,`, Expr(f, a, Expr(B, $, $)), Expr(g, Expr(B, _1, _2), c, c)))
//   assert(r3.substReIndex(Seq($, Expr(B, $, $), $)) == Expr(`,`, Expr(f, $, Expr(B, $, $)), Expr(g, Expr(B, _2, _3), $, _4)))
//   assert(r3.substReIndex(Seq($, Expr(B, $, _1), c)) == Expr(`,`, Expr(f, $, Expr(B, $, _2)), Expr(g, Expr(B, _2, _2), c, c)))
//   assert(r3.substReIndex(Seq(Expr(A, $, $), Expr(B, $, _1), c)) == Expr(`,`, Expr(f, Expr(A, $, $), Expr(B, $, _3)), Expr(g, Expr(B, _3, _3), c, c)))
//   assert(r3.substReIndex(Seq(Expr(A, $, $), Expr(B, $, $, _2), Expr(C, $, _1))) == Expr(`,`, Expr(f, Expr(A, $, $), Expr(B, $, $, _4)), Expr(g, Expr(B, _3, _4, _4), Expr(C, $, _5), Expr(C, _5, _5))))
// }
// ```


let intro_var = DyckExprRef::new_debug_checked(DyckWord::LEAF, &[Val::INTRO][..]);
let get_word = |expr: &DyckExprSubOutput| match expr {
  DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { word, .. }) => *word,
  DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { word, .. }) => core::panic!(),
};
let get_data: fn(&_) -> &_ = |expr: &DyckExprSubOutput| match expr {
  DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { data, len, .. }) => &data[0..*len],
  | DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { data, .. }) => data,
};
let get_data_mut: fn(&mut _) -> &mut _ = |expr: &mut DyckExprSubOutput| match expr {
  DyckExprSubOutput::SmallDyckExpr(SmallDyckExpr { data, len,.. }) => &mut data[0..*len],
  | DyckExprSubOutput::LargeDyckExpr(LargeDyckExpr { data, .. }) => data,
};
let sub_re_index_input: fn(&(DyckStructureZipperU64, Vec<Val>, test_parser::Variables), u8) -> (DyckExprRef, _) = |x, offset| (DyckExprRef::new_debug_checked(x.0.current_substructure(), &x.1[..]), offset);

const LEAF: DyckWord = DyckWord { word: 1 };

macro_rules! templates {($($ID:ident $SRC:literal)+) => {$(
  let _tmp = parse($SRC);
  #[allow(non_snake_case)]
  let $ID  = sub_re_index_input(&_tmp,0);
)+};}

templates! {
  r1   "(f $x $x)"
  r2   "(f $x $y $x)"
  r3   "(, (f $x $y) (g $y $z $z))"
  axy  "(a $x $y)"
  axx  "(a $x $x)"
  Bxy  "(B $x $y)"
  Bxx  "(B $x $x)"
  Axy  "(A $x $y)"
  Bxyy "(B $x $y $y)"
  Cxx  "(C $x $x)"


  i3_r1   "($a $b $c    (f $x $x))"
  i3_r2   "($a $b $c    (f $x $y $x))"
  i3_r3   "($a $b $c    (, (f $x $y) (g $y $z $z)))"
}


let mut tmp_ = i3_r1.0.word.zipper(); tmp_.decend_right(); let d3_r1 = (DyckExprRef::new_debug_checked(tmp_.current_substructure() ,&i3_r1.0.data[3..]), 3);
let mut tmp_ = i3_r2.0.word.zipper(); tmp_.decend_right(); let d3_r2 = (DyckExprRef::new_debug_checked(tmp_.current_substructure() ,&i3_r2.0.data[3..]), 3);
let mut tmp_ = i3_r3.0.word.zipper(); tmp_.decend_right(); let d3_r3 = (DyckExprRef::new_debug_checked(tmp_.current_substructure() ,&i3_r3.0.data[3..]), 3);


let s1 = subst_re_index_with_pat_offset((r1.0, 0), &[intro_var]);
core::assert_eq! {r1.0.word, get_word(&s1) }
core::assert_eq! {r1.0.data,&get_data(&s1)[..]}

macro_rules! substitutions {($($OFFSET:literal [$PAT:ident / [$($SUB:expr),*]] => $EXPECTED:literal | $INTROS:tt;)+) => {$(
  let s = subst_re_index_with_pat_offset(($PAT.0, $OFFSET), &[$($SUB),*]);
  let expected_ = parse($EXPECTED);
  let tmp = sub_re_index_input(&expected_,0);

  let expected  = subst_re_index_with_pat_offset(tmp, &$INTROS);

  core::assert_eq!(get_word(&s), get_word(&expected));
  core::assert_eq!(get_data(&s), get_data(&expected));
)+};}

let data_a = &[a][..]; let leaf_a = DyckExprRef::new_debug_checked(LEAF, data_a);
let data_b = &[b][..]; let leaf_b = DyckExprRef::new_debug_checked(LEAF, data_b);
let data_c = &[c][..]; let leaf_c = DyckExprRef::new_debug_checked(LEAF, data_c);
let data_A = &[A][..]; let leaf_A = DyckExprRef::new_debug_checked(LEAF ,data_A);
substitutions! {
  0 [r1 / [axy.0]                              ] => "(f (a $x $y) (a $x $y))"                                             | [intro_var, intro_var];
  0 [r2 / [axy.0, leaf_A]                      ] => "(f (a $x $y) A (a $x $y))"                                           | [intro_var, intro_var];
  0 [r2 / [axx.0, intro_var]                   ] => "(f (a $x $x) $ (a $x $x))"                                           | [intro_var, intro_var];
  0 [r3 / [leaf_a, leaf_b, leaf_c]             ] => "(, (f a b) (g b c c))"                                               | [];
  0 [r3 / [leaf_a, intro_var, leaf_c]          ] => "(, (f a $x) (g $x c c))"                                             | [intro_var];
  0 [r3 / [leaf_a, intro_var, intro_var]       ] => "(, (f a $x) (g $x $y $y))"                                           | [intro_var, intro_var];
  0 [r3 / [intro_var, intro_var, intro_var]    ] => "(, (f $x $y) (g $y $z $z))"                                          | [intro_var, intro_var, intro_var];
  0 [r3 / [leaf_a, Bxy.0, leaf_c]              ] => "(, (f a (B $x $y)) (g (B $x $y) c c))"                               | [intro_var, intro_var];
 
  0 [r3 / [intro_var, Bxy.0, intro_var]        ] => "(, (f $w (B $x $y)) (g (B $x $y) $z $z))"                            | [intro_var, intro_var, intro_var, intro_var];
  0 [r3 / [intro_var, Bxx.0, leaf_c]           ] => "(, (f $w (B $x $x)) (g (B $x $x) c c))"                              | [intro_var, intro_var];
  0 [r3 / [Axy.0, Bxx.0, leaf_c]               ] => "(, (f (A $w $x) (B $y $y)) (g (B $y $y) c c))"                       | [intro_var, intro_var, intro_var];
  0 [r3 / [Axy.0, Bxyy.0, Cxx.0]               ] => "(, (f (A $v $w) (B $x $y $y)) (g (B $x $y $y) (C $z $z) (C $z $z)))" | [intro_var, intro_var, intro_var, intro_var, intro_var];



  3 [d3_r1 / [axy.0]                           ] => "(f (a $x $y) (a $x $y))"                                             | [intro_var, intro_var];
  3 [d3_r2 / [axy.0, leaf_A]                   ] => "(f (a $x $y) A (a $x $y))"                                           | [intro_var, intro_var];
  3 [d3_r2 / [axx.0, intro_var]                ] => "(f (a $x $x) $ (a $x $x))"                                           | [intro_var, intro_var];
  3 [d3_r3 / [leaf_a, leaf_b, leaf_c]          ] => "(, (f a b) (g b c c))"                                               | [];
  3 [d3_r3 / [leaf_a, intro_var, leaf_c]       ] => "(, (f a $x) (g $x c c))"                                             | [intro_var];
  3 [d3_r3 / [leaf_a, intro_var, intro_var]    ] => "(, (f a $x) (g $x $y $y))"                                           | [intro_var, intro_var];
  3 [d3_r3 / [intro_var, intro_var, intro_var] ] => "(, (f $x $y) (g $y $z $z))"                                          | [intro_var, intro_var, intro_var];
  3 [d3_r3 / [leaf_a, Bxy.0, leaf_c]           ] => "(, (f a (B $x $y)) (g (B $x $y) c c))"                               | [intro_var, intro_var];
  3 [d3_r3 / [intro_var, Bxy.0, intro_var]     ] => "(, (f $w (B $x $y)) (g (B $x $y) $z $z))"                            | [intro_var, intro_var, intro_var, intro_var];
  3 [d3_r3 / [intro_var, Bxx.0, leaf_c]        ] => "(, (f $w (B $x $x)) (g (B $x $x) c c))"                              | [intro_var, intro_var];
  3 [d3_r3 / [Axy.0, Bxx.0, leaf_c]            ] => "(, (f (A $w $x) (B $y $y)) (g (B $y $y) c c))"                       | [intro_var, intro_var, intro_var];
  3 [d3_r3 / [Axy.0, Bxyy.0, Cxx.0]            ] => "(, (f (A $v $w) (B $x $y $y)) (g (B $x $y $y) (C $z $z) (C $z $z)))" | [intro_var, intro_var, intro_var, intro_var, intro_var];
}
  }


  '_matches: {
// shared/src/test/scala/ExprTest.scala
// ```scala
// test("matches") {
//   /*
//   for all matching lhs, rhs
//   val Some((lhs_vars, rhs_vars)) = (lhs matches rhs)
//   assert(lhs.substRel(lhs_vars) == rhs.substRel(rhs_vars))
//   */
//   assert((a matches a).contains((List(), List())))
//   assert((a matches b).isEmpty)
//   assert(($ matches $).contains((List($),List($))))
//   assert((Expr(a, b) matches Expr(a, b)).contains((List(), List())))
//   assert((Expr(a, b) matches Expr(a, c)).isEmpty)
//   assert((Expr($, b) matches Expr(a, b)).contains((List(a),List())))
//   assert((Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr(c, a), Expr(c, b))).contains((List(c),List())))
//   assert((Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr(c, a), Expr(a, b))).isEmpty)
//   assert((Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr(a, $), Expr(a, _1))).isEmpty)
//   assert((Expr(Expr($, a), Expr(_1, a)) matches Expr(Expr(b, $), Expr(b, _1))).contains((List(b), List(a))))
//   // println(Expr(Expr($, a), Expr(_1, b)) matches Expr(Expr($, a), Expr(b, _1)))
//   assert((Expr(Expr(a, $), Expr(_1, b)) matches Expr(Expr($, a), Expr(_1, b))).contains((List(a),List(a))))
//   // println(Expr($, _1, a, _1) matches Expr($, _1, _1, a))
//   assert((Expr($, _1, a, _1) matches Expr($, _1, _1, b)).isEmpty)
//   assert((Expr($, _1, a, _1) matches Expr($, _1, _1, b)).isEmpty)
//   assert((Expr($, a, _1) matches Expr(Expr(b, $), $, Expr(_2, _1))).isEmpty)
//   // println(Expr($, a, _1) matches Expr(Expr(b, $), $, Expr($, _1)))
// }
// ```


let expr = |w,d| DyckExprRef::new_debug_checked(DyckWord::new_debug_checked(w), d);

let tmp =  &[a][..];                                          let a_       = expr(1, tmp);
let tmp =  &[b][..];                                          let b_       = expr(1, tmp);
let tmp =  &[c][..];                                          let c_       = expr(1, tmp);
let tmp =  &[Val::INTRO][..];                                 let intro_   = expr(1, tmp);

let tmp =  &[a, b][..];                                       let ab_      = expr(0b_110, tmp);
let tmp =  &[a, c][..];                                       let ac_      = expr(0b_110, tmp);
let tmp =  &[Val::INTRO, b][..];                              let xb_      = expr(0b_110, tmp);

let tmp =  &[Val::INTRO, a,Val(-1), b][..];                   let xa_xb_   = expr(0b_110_110_0, tmp);
let tmp =  &[c, a,c, b][..];                                  let ca_cb_   = expr(0b_110_110_0, tmp);
let tmp =  &[c, a,a, b][..];                                  let ca_ab_   = expr(0b_110_110_0, tmp);
let tmp =  &[a, Val::INTRO,a, Val(-1)][..];                   let ax_ax_   = expr(0b_110_110_0, tmp);
let tmp =  &[Val::INTRO,a, Val(-1),a][..];                    let xa_xa_   = expr(0b_110_110_0, tmp);
let tmp =  &[b, Val::INTRO,b, Val(-1)][..];                   let bx_bx_   = expr(0b_110_110_0, tmp);
let tmp =  &[a, Val::INTRO, Val(-1),b][..];                   let ax_xb_   = expr(0b_110_110_0, tmp);

let tmp =  &[Val::INTRO, Val(-1), a, Val(-1)][..];            let xxax_    = expr(0b_1101010, tmp);
let tmp =  &[Val::INTRO, Val(-1), Val(-1), b][..];            let xxxb_    = expr(0b_1101010, tmp);
let tmp =  &[Val::INTRO, a,Val(-1)][..];                      let xax_     = expr(0b_11010, tmp);
let tmp =  &[b,Val::INTRO,Val::INTRO,Val::INTRO,Val(-1)][..]; let bx_y_zx_ = expr(0b_110_10_110_0, tmp);

core::assert_eq! {expr_matches(a_, a_), Option::Some((Vec::new(), Vec::new()))}
core::assert_eq! {expr_matches(a_, b_), Option::None}
core::assert_eq! {expr_matches(intro_, intro_), Option::Some((Vec::from([intro_]), Vec::from([intro_])))}

core::assert_eq! {expr_matches(ab_, ab_), Option::Some((Vec::new(), Vec::new()))}
core::assert_eq! {expr_matches(ab_, ac_), Option::None}
core::assert_eq! {expr_matches(xb_, ab_), Option::Some((Vec::from([a_]), Vec::new()))}

core::assert_eq! {expr_matches(xa_xb_, ca_cb_), Option::Some((Vec::from([c_]), Vec::new()))}
core::assert_eq! {expr_matches(xa_xb_, ca_ab_), Option::None}
core::assert_eq! {expr_matches(xa_xb_, ax_ax_), Option::None}
core::assert_eq! {expr_matches(xa_xa_, bx_bx_), Option::Some((Vec::from([b_]), Vec::from([a_])))}
core::assert_eq! {expr_matches(ax_xb_, xa_xb_), Option::Some((Vec::from([a_]), Vec::from([a_])))}
core::assert_eq! {expr_matches(xxax_, xxxb_), Option::None}
core::assert_eq! {expr_matches(xax_, bx_y_zx_), Option::None}

  }


  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("unifiable") {
  //   assert(a unifiable a)
  //   assert(!(a unifiable b))
  //   assert($ unifiable $)
  //   assert(Expr(a, b) unifiable Expr(a, b))
  //   assert(!(Expr(a, b) unifiable Expr(a, c)))
  //   assert(Expr($, b) unifiable Expr(a, b))
  //   assert(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr(c, a), Expr(c, b)))
  //   assert(!(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr(c, a), Expr(a, b))))
  //   assert(!(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr(a, $), Expr(a, _1))))
  //   assert(Expr(Expr($, a), Expr(_1, a)) unifiable Expr(Expr(b, $), Expr(b, _1)))
  //   assert(Expr(Expr($, a), Expr(_1, b)) unifiable Expr(Expr($, a), Expr(b, _1)))
  //   assert(Expr(Expr(a, $), Expr(_1, b)) unifiable Expr(Expr($, a), Expr(_1, b)))
  //   assert(Expr($, _1, a, _1) unifiable Expr($, _1, _1, a))
  //   assert(!(Expr($, _1, a, _1) unifiable Expr($, _1, _1, b)))
  //   assert(!(Expr($, _1, a, _1) unifiable Expr($, _1, _1, b)))
  //   assert(!(Expr($, a, _1) unifiable Expr(Expr(b, $), $, Expr(_2, _1))))
  //   assert(Expr($, a, _1) unifiable Expr(Expr(b, $), $, Expr($, _1)))
  // }
  // ```

  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("unify bindings") {
  //   val $v = Var(-301)
  //   val $w = Var(-302)
  //   assert(Expr.unify(Expr(a, Expr(b, $x), Expr(f, $y, $x)),
  //     Expr(a, Expr(b, $z), Expr(f, $z, Expr(g, $v, $w)))) ==
  //   Map($x.leftMost -> App(App(g, $v), $w),
  //       $y.leftMost -> App(App(g, $v), $w),
  //       $z.leftMost -> App(App(g, $v), $w)))

  //   try
  //     Expr.unifyTo(Expr(`=`, App(App(App(f, $), _1), $), _2), Expr(`=`, App(App($, $), $), $))
  //     assert(false)
  //   catch case Solver.Cycle(r, d) => ()

  //   try
  //     Expr.unifyTo(Expr(`=`, App(App(App(f, $), _1), $), _2), Expr(`=`, App(App(f, $), App(App(_1, $), $)), $))
  //     assert(false)
  //   catch case Solver.Conflict(_, _) => ()
  // }
  // ```

  // shared/src/test/scala/ExprTest.scala
  // ```scala
  // test("unify multiple") {
  //   /*
  //   for all unifiable E1, E2, E3
  //   val m = Expr.unify(E1, E2, E3)
  //   E1.substAbs(m) == E2.substAbs(m) == E3.substAbs(m)
  //   */
  //   assert(Expr.unify(Expr($x, a, $x), $y, Expr(Expr(a, b), $z, Expr($z, b))) == Map(
  //     $x -> Expr(a, b),
  //     $y -> Expr(Expr(a, b), a, Expr(a, b)),
  //     $z -> a
  //   ).map{ case (Var(i), e) => i -> e })

  //   assert(Expr.unify(Expr(a, Expr(a, $x), Expr(a, $x, $y)), Expr($z, Expr($z, b), Expr($z, b, c))) == Map(
  //     $x -> b,
  //     $y -> c,
  //     $z -> a
  //   ).map{ case (Var(i), e) => i -> e })

  //   assert(Expr.unify(
  //     Expr(Expr(f, Var(-11)), Expr(Var(-12), Var(-13))),
  //     Expr(Expr(Var(-20), a), Expr(Var(-22), Var(-23))),
  //     Expr(Expr(Var(-30), Var(-31)), Expr(g, Var(-33))),
  //     Expr(Expr(Var(-40), Var(-41)), Expr(Var(-42), b))
  //   ) == Map(-22 -> g, -40 -> f, -11 -> a, -23 -> b, -30 -> f, -42 -> g, -20 -> f, -33 -> b, -31 -> a, -12 -> g, -13 -> b, -41 -> a))
  // }
  // ```

  '_transform : {
// shared/src/test/scala/ExprTest.scala
// ```scala
// test("transform") {
//   assert(Expr(A, a, b).transform(Expr(A, $, $), Expr(B, _2, _1)) == Expr(B, b, a))
  
//   val pair = Var(1000)
//   val rightItem = Var(1001)
//   val list = Var(1002)
//   val head = Var(1003)
//   val last = Var(1004)
  
//   {
//     val data =    Expr(pair, a, b)
//     val pattern = Expr(pair, a, $)
//     val template = Expr(rightItem, _1)
//     assert(data.transform(pattern, template) == Expr(rightItem, b))
//   }
  
//   {
//     val listData = Expr(list, Expr(pair, a, b), Expr(pair, b, c), Expr(pair, A, A))
//     val listOf3pattern = Expr(list, $, $, $)
//     val headTemplate = Expr(head, _1)
//     val lastTemplate = Expr(last, _3)
  
//     val extremaTemplate = Expr(pair, _1, _3)
  
//     assert(listData.transform(listOf3pattern, headTemplate) == Expr(head, Expr(pair, a, b)))
//     assert(listData.transform(listOf3pattern, lastTemplate) == Expr(last, Expr(pair, A, A)))
//     assert(listData.transform(listOf3pattern, extremaTemplate) == Expr(pair, Expr(pair, a, b), Expr(pair, A, A)))
//   }
// }
// ```

let pair       = Val(1000);
let right_item = Val(1001);
let list       = Val(1002);
let head       = Val(1003);
let last       = Val(1004);

let intro = Val::INTRO;
'_1 : {
  let expr = |w,d| DyckExprRef::new_debug_checked(DyckWord::new_debug_checked(w), d);
  
  let tmp = &[pair, a, b ][..];let data     = expr(0b_11010,tmp);  
  let tmp = &[pair, a, intro   ][..]; let pattern  = expr(0b_11010, tmp);  
  let tmp = &[right_item, Val(-1)][..]; let template = expr(0b_110, tmp);  
  let tmp = &[right_item, b][..]; let expected = expr(0b_110, tmp);  

  let t1_ret   = transform_re_index_small(data, pattern, template).unwrap();
  let t1       = DyckExprRef::new_debug_checked(t1_ret.word, &t1_ret.data[0..t1_ret.len]);
  core::assert_eq!(t1, expected);
  
}

'_2 : {
  let expr = |w,d| DyckExprRef::new_debug_checked(DyckWord::new_debug_checked(w), d);
  let tmp = &[list, 
  /*(*/ pair, a, b /*)*/, 
  /*(*/ pair, b, c /*)*/, 
  /*(*/ pair, A, A /*)*/, 
  ][..];
  let list_data = expr(0b_1_11010_0_11010_0_11010_0, tmp);

  let tmp = &[list, intro, intro, intro][..]; let list_of_3_pattern = expr(0b_1_10_10_10, tmp); 
  let tmp = &[head, Val(-1)         ][..];    let head_template     = expr(0b_110, tmp); 
  let tmp = &[last, Val(-3)         ][..];    let last_template     = expr(0b_110, tmp); 
  let tmp = &[pair, Val(-1), Val(-3)][..];    let extrema_template  = expr(0b_11010, tmp); 
  
  
  macro_rules! template_expected {($($TEMPLATE:ident => ($WORD:literal, $LIST:expr); )+) => {$(
    
    let expected = (DyckWord::new_debug_checked($WORD), &($LIST)[..]);
    let ret = transform_re_index_small(list_data, list_of_3_pattern, $TEMPLATE).unwrap();
    let t = (ret.word, &ret.data[0..ret.len]);
    core::assert_eq!(t, expected);
  )+};}
  template_expected!{
    head_template    => (0b_1_11010_0        , [head, /*(*/ pair, a, b /*)*/,                       ]);
    last_template    => (0b_1_11010_0        , [last,                         /*(*/ pair, A, A /*)*/]);
    extrema_template => (0b_1_11010_0_11010_0, [pair, /*(*/ pair, a, b /*)*/, /*(*/ pair, A, A /*)*/]);
  }
}
  }
  
  '_subst: {
// shared/src/test/scala/ExprTest.scala
// ```scala
// test("subst") {
//   assert(e1.substRel(Seq(b)) == Expr(f, b, a))
//   assert(e2.substRel(Seq(a, b)) == Expr(f, a, b, b, a))
//   assert(e3.substRel(Seq(a, b)) == Expr(f, a, Expr(g, a, b)))
// }
// ```

macro_rules! leaf {($V:expr) => { DyckExprRef::new_debug_checked(DyckWord::LEAF, &[$V][..]) };}

type DSZU64 = DyckStructureZipperU64;
let s1 = subst_rel_small((DyckExprRef::new_debug_checked(e1.0.current_substructure(), &e1.1), 0),  &[leaf!(b)          ][..],).unwrap();
let s2 = subst_rel_small((DyckExprRef::new_debug_checked(e2.0.current_substructure(), &e2.1), 0),  &[leaf!(a), leaf!(b)][..],).unwrap();
let s3 = subst_rel_small((DyckExprRef::new_debug_checked(e3.0.current_substructure(), &e3.1), 0),  &[leaf!(a), leaf!(b)][..],).unwrap();
let expected1 = parse("(f b a)");
let expected2 = parse("(f a b b a)");
let expected3 = parse("(f a (g a b))");
core::assert_eq! {(s1.word, &s1.data[0..s1.len]), (expected1.0.current_substructure(), &expected1.1[..])}
core::assert_eq! {(s2.word, &s2.data[0..s2.len]), (expected2.0.current_substructure(), &expected2.1[..])}
core::assert_eq! {(s3.word, &s3.data[0..s3.len]), (expected3.0.current_substructure(), &expected3.1[..])}

// with offset

macro_rules! make_offset_template {($($NAME:ident $SEXPR:literal $OFFSET:literal;)+) => {$(  
  let tmp_0 = parse($SEXPR);
  let mut tmp_1 = tmp_0.0.current_substructure().zipper();
  tmp_1.decend_right(); 
  let $NAME = DyckExprRef::new_debug_checked(tmp_1.current_substructure(), &tmp_0.1[$OFFSET..]);
)+};}
make_offset_template!{
  d3_fx   "($a $b $c   (f $x))"      3;
  d3_fxgx "($a $b $c   (f $x g $x))" 3;
  d3_fxgy "($a $b $c   (f $x g $y))" 3;
}

let s4 = subst_rel_small((d3_fx  , 3), &[leaf!(a)          ][..],).unwrap();
let s5 = subst_rel_small((d3_fxgx, 3), &[leaf!(a)          ][..],).unwrap();
let s6 = subst_rel_small((d3_fxgy, 3), &[leaf!(a), leaf!(b)][..],).unwrap();

let expected4 = parse("(f a)");
let expected5 = parse("(f a g a)");
let expected6 = parse("(f a g b)");

core::assert_eq! { (s4.word, &s4.data[0..s4.len]), (expected4.0.current_substructure(), &expected4.1[..])}
core::assert_eq! { (s5.word, &s5.data[0..s5.len]), (expected5.0.current_substructure(), &expected5.1[..])}
core::assert_eq! { (s6.word, &s6.data[0..s6.len]), (expected6.0.current_substructure(), &expected6.1[..])}
  }



  '_large_subst: {
// shared/src/test/scala/ExprTest.scala
// ```scala
// test("large subst") {
//   import Expr.*
//   val `5` = Var(200)
//   val Z = Var(201)
//   assert(r1.substRel(Seq(`5`, App(g,App(g,Z)))) == App(App(`=`,App(f,App(App(`,`,`5`),App(g,App(g,App(g,App(g,Z))))))),App(App(h,App(App(`,`,`5`),App(g,a))),App(App(`,`,`5`),App(g,App(g,App(g,Z)))))))
// }
// ```

/*
          [`=`,f,`,`,`5`,g,g,g,g,Z, h,`,`,`5`,g,a,`,`,`5`,g,g,g,Z] 11_110_111_110_000000___1_110_110_00_110_11_110_0000___0
    */

let _5 = Val(200);
let Z = Val(201);

let g = g;
let h = h;
let a = a;
let f = f;

let s = subst_rel_small((DyckExprRef::new_debug_checked(r1.0.current_substructure(), &r1.1), 0), &[DyckExprRef::new_debug_checked(DyckWord::LEAF, &[_5]), DyckExprRef::new_debug_checked(DyckWord::new_debug_checked(0b_11100), &[g, g, Z]),]).unwrap();
core::assert_eq!(
  (s.word, &s.data[0..s.len]),
  (
    DyckWord::new_debug_checked(0b___11_110_111_110_000000___1_110_110_00_110_11_110_0000___0),
    &[Val::atom(Sym::new("=")), f, Val::atom(Sym::new(",")), _5, g, g, g, g, Z, h, Val::atom(Sym::new(",")), _5, g, a, Val::atom(Sym::new(",")), _5, g, g, g, Z][..]
  )
);
  }  
}
