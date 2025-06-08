#[allow(unused_imports)]
use std::{fmt::{format, Formatter}, mem, ptr::slice_from_raw_parts, str::Utf8Error};
use mork_bytestring::*;

#[allow(unused)]
fn traverse(ez: &mut ExprZipper) {
    loop {
        let d = ez.trace.len();

        if let Tag::Arity(a) = ez.tag() { }
        else { println!("{}", " ".repeat(4 * d) + &*ez.item_str()) }

        if !ez.next() { break; }
    }
    // println!("{:?}", ez.parents);
}

// fn traverse_bracketed(ez: &mut ExprZipper) {
//     // WIP
//     //(, (f(A $ $)(B $ $ _4))(g(B _3 _4 _4)(C $ _5)(C _5 _5)))
//     loop {
//         // println!("       {:?}", ez.trace);
//         let d = ez.trace.len();
//
//         if let Tag::Arity(a) = ez.tag() { print!("(") }
//         else { print!(" {} ", &*ez.item_str()) }
//
//         if ez.next_descendant(-1, 0) { continue; }
//         // if d > 3 && ez.next_descendant(3, 0) { continue; }
//         // if d > 2 && ez.next_descendant(3, 0) { continue; }
//         // if d > 1 && ez.next_descendant(2, 0) { continue; }
//         // if d > 0 && ez.next_descendant(1, 0) { continue; }
//         // if ez.next_descendant(0, 0) { print!("%"); continue; }
//         else if ez.parent() { ez.next_child(); print!(")"); continue }
//         else { break; }
//     }
//     // println!("{:?}", ez.parents);
// }


#[test]
fn subexpr() {
    // (foo $ (200 201))
    let mut e = vec![Tag::Arity(3).byte(), Tag::SymbolSize(3).byte(), b'f', b'o', b'o', Tag::NewVar.byte(),
                                Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'\xc8', Tag::SymbolSize(1).byte(), b'\xc9'];
    let mut ez = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    assert!(ez.next());
    assert!(ez.next());
    assert!(ez.next());
    println!("after 3 next: {}", ez.item_str());
    let sez = ExprZipper::new(ez.subexpr());
    // sez.traverse(0);
    println!("{:?}", sez.root);
}

#[test]
fn children() {
    {
        // (= (func $) (add`0 (123456789 _1)))
        let mut e = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'=',
                         Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'f', b'u', b'n', b'c', Tag::NewVar.byte(),
                         Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'a', b'd', b'd', 0,
                         Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), 7, 91, 205, 21, Tag::VarRef(0).byte()];
        let mut ecz = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
        assert!(ecz.item_str() == "[3]" && ecz.loc == 0);
        assert!(ecz.next_child());
        assert!(ecz.item_str() == "=" && ecz.loc == 1);
        assert!(ecz.next_child());
        assert!(ecz.item_str() == "[2]" && ecz.loc == 3);
        assert!(ecz.next_child());
        assert!(ecz.item_str() == "[2]" && ecz.loc == 10);
        assert!(!ecz.next_child());
    }

    {
        //(, (f (A $ $) (B $ $ _4))
        //   (g (B _3 _4 _4) (C $ _5) (C _5 _5)))
        let mut e = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'A', Tag::NewVar.byte(), Tag::NewVar.byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::NewVar.byte(), Tag::VarRef(3).byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::VarRef(2).byte(), Tag::VarRef(3).byte(), Tag::VarRef(3).byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'C', Tag::NewVar.byte(), Tag::VarRef(4).byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'C', Tag::VarRef(4).byte(), Tag::VarRef(4).byte(),
        ];
        let mut ecz = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
        assert_eq!(ecz.root.string(), "(, (f (A $ $) (B $ $ _4)) (g (B _3 _4 _4) (C $ _5) (C _5 _5)))");

        assert!(ecz.next_child());
        print!("se: "); ecz.traverse(0); println!();
        assert!(ecz.next_child());
        let f = ecz.subexpr();
        let mut fz = ExprZipper::new(f);
        print!("se: "); ecz.traverse(0); println!();
        // assert!(ecz.next_child());
        assert!(ecz.next_descendant(1, 1));
        // assert!(ecz.next_descendant(-1, 1));
        print!("mv: "); ecz.traverse(0); println!();
        // assert!(ecz.next_descendant(1, 1));
        // assert!(ecz.next_descendant(2, 1));
        // assert!(ecz.next_descendant(2, 1));
        assert!(ecz.next_descendant(0, 0));
        let g = ecz.subexpr();
        let mut gz = ExprZipper::new(g);
        print!("se: "); ecz.traverse(0); println!();
        assert!(!ecz.next_child());

        assert!(fz.next_child());
        print!("sf: "); fz.traverse(0); println!();
        assert!(fz.next_child());
        // assert!(fz.next_child_relative(1, 1));
        print!("sf: "); fz.traverse(0); println!();
        assert!(fz.next_child());
        // assert!(fz.next_child_relative(0, 0));
        print!("sf: "); fz.traverse(0); println!();
        assert!(!fz.next_child());

        assert!(gz.next_child());
        print!("sg: "); gz.traverse(0); println!();
        assert!(gz.next_child());
        print!("sg: "); gz.traverse(0); println!();
        assert!(gz.next_child());
        print!("sg: "); gz.traverse(0); println!();
        assert!(gz.next_child());
        print!("sg: "); gz.traverse(0); println!();
        assert!(!gz.next_child());
    }

}

#[test]
fn substitute() {
    // only used when there's just data substituted in, no variables
    // (F foo); (Bar $ $)
    let mut data = vec![vec![Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'F', Tag::SymbolSize(3).byte(), b'f', b'o', b'o'],
                                    vec![Tag::Arity(3).byte(), Tag::SymbolSize(3).byte(), b'B', b'a', b'r', Tag::NewVar.byte(), Tag::NewVar.byte()]];
    let se = data.iter_mut().map(|i| Expr{ ptr: i.as_mut_ptr() }).collect::<Vec<Expr>>();
    // (image (Rel $ $) (Im _2))
    let mut exprv = vec![Tag::Arity(3).byte(), Tag::SymbolSize(5).byte(), b'i', b'm', b'a', b'g', b'e',
                                    Tag::Arity(3).byte(), Tag::SymbolSize(3).byte(), b'R', b'e', b'l', Tag::NewVar.byte(), Tag::NewVar.byte(),
                                    Tag::Arity(2).byte(), Tag::SymbolSize(2).byte(), b'I', b'm', Tag::VarRef(1).byte()];
    let expr = Expr { ptr: exprv.as_mut_ptr() };
    let mut buffer = vec![0u8; 100];

    for (i, &d) in se.iter().enumerate() {
        println!("data_{}: {:?}", i, d)
    }

    println!("expr: {:?}", expr);

    let mut rz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });
    expr.substitute(&se[..], &mut rz);
    println!("result: {:?}", Expr { ptr: buffer.as_mut_ptr() });
}

#[test]
fn de_bruijn() {
    let mut r1v = vec![
        Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
        Tag::NewVar.byte(),
        Tag::VarRef(0).byte()
    ];
    let r1 = Expr{ ptr: r1v.as_mut_ptr() };
    {
        // assert(r1.substReIndex(Seq($)) == r1)
        let mut s1v = vec![Tag::NewVar.byte()];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r1.substitute_de_bruijn(&[s1], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(r1).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*r1.span(), &*o.span());
            assert_eq!(&*r1.span(), &*o.span());
        }
    }
    {
        // assert(r1.substReIndex(Seq(Expr(a, $, $))) == Expr(f, Expr(a, $, $), Expr(a, _1, _2)))
        let mut s1v = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte()
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::VarRef(0).byte(),
            Tag::VarRef(1).byte()
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r1.substitute_de_bruijn(&[s1], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }

    let mut r2v = vec![
        Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'f',
        Tag::NewVar.byte(),
        Tag::NewVar.byte(),
        Tag::VarRef(0).byte()
    ];
    let r2 = Expr{ ptr: r2v.as_mut_ptr() };
    {
        // assert(r2.substReIndex(Seq(Expr(a, $, $), A)) == Expr(f, Expr(a, $, $), A, Expr(a, _1, _2)))
        let mut s1v = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte()
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![
            Tag::SymbolSize(1).byte(), b'A'
        ];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte(),
            Tag::SymbolSize(1).byte(), b'A',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::VarRef(0).byte(),
            Tag::VarRef(1).byte()
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r2.substitute_de_bruijn(&[s1, s2], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r2.substReIndex(Seq(Expr(a, $, $), $)) == Expr(f, Expr(a, $, $), $, Expr(a, _1, _2)))
        let mut s1v = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte()
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![
            Tag::NewVar.byte()
        ];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte(),
            Tag::NewVar.byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::VarRef(0).byte(),
            Tag::VarRef(1).byte()
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r2.substitute_de_bruijn(&[s1, s2], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r2.substReIndex(Seq(Expr(a, $, _1), $)) == Expr(f, Expr(a, $, _1), $, Expr(a, _1, _1)))
        let mut s1v = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::VarRef(0).byte()
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![
            Tag::NewVar.byte()
        ];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::VarRef(0).byte(),
            Tag::NewVar.byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::VarRef(0).byte(),
            Tag::VarRef(0).byte()
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r2.substitute_de_bruijn(&[s1, s2], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }

    let mut r3v = vec![
        Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
        Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
        Tag::NewVar.byte(),
        Tag::NewVar.byte(),
        Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
        Tag::VarRef(1).byte(),
        Tag::NewVar.byte(),
        Tag::VarRef(2).byte()
    ];
    // (, (f $ $) (g _2 $ _3))
    let r3 = Expr{ ptr: r3v.as_mut_ptr() };
    {
        // assert(r3.substReIndex(Seq(a, b, c)) == Expr(`,`, Expr(f, a, b), Expr(g, b, c, c)))
        let mut s1v = vec![Tag::SymbolSize(1).byte(), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::SymbolSize(1).byte(), b'b'];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::SymbolSize(1).byte(), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::SymbolSize(1).byte(), b'a',
            Tag::SymbolSize(1).byte(), b'b',
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::SymbolSize(1).byte(), b'b',
            Tag::SymbolSize(1).byte(), b'c',
            Tag::SymbolSize(1).byte(), b'c',
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq(a, $, c)) == Expr(`,`, Expr(f, a, $), Expr(g, _1, c, c)))
        let mut s1v = vec![Tag::SymbolSize(1).byte(), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::NewVar.byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::SymbolSize(1).byte(), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::VarRef(0).byte(),
            Tag::SymbolSize(1).byte(), b'c',
            Tag::SymbolSize(1).byte(), b'c',
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq(a, $, $)) == Expr(`,`, Expr(f, a, $), Expr(g, _1, $, _2)))
        let mut s1v = vec![Tag::SymbolSize(1).byte(), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::NewVar.byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::NewVar.byte()];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::VarRef(0).byte(),
            Tag::NewVar.byte(),
            Tag::VarRef(1).byte(),
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq($, $, $)) == Expr(`,`, Expr(f, $, $), Expr(g, _2, $, _3)))
        let mut s1v = vec![Tag::NewVar.byte()];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::NewVar.byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::NewVar.byte()];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(r3).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*r3.span(), &*o.span());
            assert_eq!(&*r3.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq(a, Expr(B, $, $), c)) == Expr(`,`, Expr(f, a, Expr(B, $, $)), Expr(g, Expr(B, _1, _2), c, c)))
        let mut s1v = vec![Tag::SymbolSize(1).byte(), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::NewVar.byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::SymbolSize(1).byte(), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::SymbolSize(1).byte(), b'a',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::NewVar.byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::VarRef(0).byte(), Tag::VarRef(1).byte(),
            Tag::SymbolSize(1).byte(), b'c',
            Tag::SymbolSize(1).byte(), b'c',
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq($, Expr(B, $, $), $)) == Expr(`,`, Expr(f, $, Expr(B, $, $)), Expr(g, Expr(B, _2, _3), $, _4)))
        let mut s1v = vec![Tag::NewVar.byte()];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::NewVar.byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::NewVar.byte()];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::NewVar.byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::NewVar.byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::VarRef(1).byte(), Tag::VarRef(2).byte(),
            Tag::NewVar.byte(),
            Tag::VarRef(3).byte(),
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq($, Expr(B, $, _1), c)) == Expr(`,`, Expr(f, $, Expr(B, $, _2)), Expr(g, Expr(B, _2, _2), c, c)))
        let mut s1v = vec![Tag::NewVar.byte()];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::VarRef(0).byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::SymbolSize(1).byte(), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::NewVar.byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::VarRef(1).byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::VarRef(1).byte(), Tag::VarRef(1).byte(),
            Tag::SymbolSize(1).byte(), b'c',
            Tag::SymbolSize(1).byte(), b'c',
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq(Expr(A, $, $), Expr(B, $, _1), c)) == Expr(`,`, Expr(f, Expr(A, $, $), Expr(B, $, _3)), Expr(g, Expr(B, _3, _3), c, c)))
        let mut s1v = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'A', Tag::NewVar.byte(), Tag::NewVar.byte()];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::VarRef(0).byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::SymbolSize(1).byte(), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'A', Tag::NewVar.byte(), Tag::NewVar.byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::VarRef(2).byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::VarRef(2).byte(), Tag::VarRef(2).byte(),
            Tag::SymbolSize(1).byte(), b'c',
            Tag::SymbolSize(1).byte(), b'c',
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    {
        // assert(r3.substReIndex(Seq(Expr(A, $, $), Expr(B, $, $, _2), Expr(C, $, _1))) ==
        //                        Expr(`,`, Expr(f, Expr(A, $, $), Expr(B, $, $, _4)), Expr(g, Expr(B, _3, _4, _4), Expr(C, $, _5), Expr(C, _5, _5))))
        let mut s1v = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'A', Tag::NewVar.byte(), Tag::NewVar.byte()];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::NewVar.byte(), Tag::VarRef(1).byte()];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'C', Tag::NewVar.byte(), Tag::VarRef(0).byte()];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b',',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'f',
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'A', Tag::NewVar.byte(), Tag::NewVar.byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::NewVar.byte(), Tag::NewVar.byte(), Tag::VarRef(3).byte(),
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'g',
            Tag::Arity(4).byte(), Tag::SymbolSize(1).byte(), b'B', Tag::VarRef(2).byte(), Tag::VarRef(3).byte(), Tag::VarRef(3).byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'C', Tag::NewVar.byte(), Tag::VarRef(4).byte(),
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'C', Tag::VarRef(4).byte(), Tag::VarRef(4).byte(),
        ];
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        let mut buffer = vec![0u8; 100];
        let o = Expr { ptr: buffer.as_mut_ptr() };
        let mut oz = ExprZipper::new(o);
        r3.substitute_de_bruijn(&[s1, s2, s3], &mut oz);
        unsafe {
            // print!("t: "); ExprZipper::new(target).traverse(0); println!();
            // print!("o: "); ExprZipper::new(o).traverse(0); println!();
            // println!("{:?} == {:?}", &*target.span(), &*o.span());
            assert_eq!(&*target.span(), &*o.span());
        }
    }
    // {
    //     // assert(r3.substReIndex(Seq(Expr(A, $, $), Expr(B, $, $, _2), Expr(C, $, _1))) ==
    //     //                        Expr(`,`, Expr(f, Expr(A, $, $), Expr(B, $, $, _4)), Expr(g, Expr(B, _3, _4, _4), Expr(C, $, _5), Expr(C, _5, _5))))
    //     let mut srcv = parse!("[4] $ $ _2 _1");
    //     let src = Expr{ ptr: srcv.as_mut_ptr() };
    //
    //     let mut targetv = parse!("[4] $ _1 _1 _1");
    //     let target = Expr{ ptr: targetv.as_mut_ptr() };
    //
    //     let mut sdbv = vec![0; 100];
    //     let o = Expr{ ptr: sdbv.as_mut_ptr() };
    //     src.substitute_de_bruijn(&[
    //         Expr{ ptr: vec![item_byte(Tag::NewVar)].leak().as_mut_ptr() },
    //         Expr{ ptr: vec![item_byte(Tag::VarRef(0))].leak().as_mut_ptr() },
    //     ], &mut ExprZipper::new(o));
    //
    //     unsafe {
    //         print!("t: "); ExprZipper::new(target).traverse(0); println!();
    //         print!("o: "); ExprZipper::new(o).traverse(0); println!();
    //         println!("{:?} == {:?}", &*target.span(), &*o.span());
    //         // assert_eq!(&*target.span(), &*o.span());
    //     }
    // }
    {
        let mut sdbv = vec![0; 100];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut srcv = parse!("[2] [2] flip [3] = $ $ [2] axiom [3] = _2 _1");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[2] [2] flip [3] = $ [4] L $ $ $ [2] axiom [3] = [4] L _2 _3 _4 _1");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_de_bruijn(&[
            Expr{ ptr: vec![Tag::NewVar.byte()].leak().as_mut_ptr() },
            Expr{ ptr: parse!("[4] L $ $ $").as_mut_ptr() }
        ], &mut ExprZipper::new(o));

        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 512];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("X");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[17] $ _1 A $ $ $ B $ _2 $ _6 _4 C _3 $ _6 _7");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[17] $ _1 A $ $ X B $ _2 $ _5 X C _3 $ _5 _6");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(3, subs, &mut ExprZipper::new(o));
        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 512];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("$");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[17] $ _1 A $ $ $ B $ _2 $ _6 _4 C _3 $ _6 _7");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[17] $ _1 A $ $ $ B $ _2 $ _6 _4 C _3 $ _6 _7");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(3, subs, &mut ExprZipper::new(o));
        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 512];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("_1");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[17] $ _1 A $ $ $ B $ _2 $ _6 _4 C _3 $ _6 _7");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[17] $ _1 A $ $ _1 B $ _2 $ _5 _1 C _3 $ _5 _6");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(3, subs, &mut ExprZipper::new(o));
        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 512];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("[2] $ _1");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[17] $ _1 A $ $ $ B $ _2 $ _6 _4 C _3 $ _6 _7");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[17] $ _1 A $ $ [2] $ _1 B $ _2 $ _6 [2] _4 _1 C _3 $ _6 _7");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(3, subs, &mut ExprZipper::new(o));
        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 512];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("_6");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[17] $ _1 A $ $ $ B $ _2 $ _6 _4 C _3 $ _6 _7");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[17] $ _1 A $ $ $ B $ _2 _4 _4 _4 C _3 $ _4 _6");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(3, subs, &mut ExprZipper::new(o));
        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 100];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("[4] R _2 _3 _4");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[2] [2] flip [3] = $ [4] L $ $ $ [2] axiom [3] = [4] L _2 _3 _4 _1");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[2] [2] flip [3] = [4] R $ $ $ [4] L _1 _2 _3 [2] axiom [3] = [4] L _1 _2 _3 [4] R _1 _2 _3");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(0, subs, &mut ExprZipper::new(o));

        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 100];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("[4] B _2 _2 _2");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[2] [2] flip [3] = $ [2] A $ [2] axiom [3] = [2] A _2 _1");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[2] [2] flip [3] = [4] B $ _1 _1 [2] A _1 [2] axiom [3] = [2] A _1 [4] B _1 _1 _1");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(0, subs, &mut ExprZipper::new(o));

        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
    {
        let mut sdbv = vec![0; 100];
        let o = Expr{ ptr: sdbv.as_mut_ptr() };
        let mut subsv = parse!("[4] B _2 $ _2");
        let subs = Expr { ptr: subsv.as_mut_ptr() };
        let mut srcv = parse!("[2] [2] flip [3] = $ [2] A $ [2] axiom [3] = [2] A _2 _1");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut targetv = parse!("[2] [2] flip [3] = [4] B $ $ _1 [2] A _1 [2] axiom [3] = [2] A _1 [4] B _1 _2 _1");
        let target = Expr{ ptr: targetv.as_mut_ptr() };
        src.substitute_one_de_bruijn_future(0, subs, &mut ExprZipper::new(o));

        assert_eq!(format!("{:?}", o), format!("{:?}", target));
    }
}

#[test]
fn equate_vars() {
    {
        let mut lhsv = parse!("[5] $ $ _1 _2 A");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[5] $ _1 _1 _1 A");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xffu8, 0]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    {
        let mut lhsv = parse!("[5] $ _1 $ _2 A");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[5] $ _1 _1 _1 A");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xffu8, 0]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    {
        let mut lhsv = parse!("[5] $ $ _2 _1 A");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[5] $ _1 _1 _1 A");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xffu8, 0]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    {
        let mut lhsv = parse!("[5] $ $ $ $ A");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[5] $ _1 $ _2 A");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xffu8, 0, 0xffu8, 1]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    {
        let mut lhsv = parse!("[5] $ $ $ $ A");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[5] $ $ _2 _1 A");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xffu8, 0xffu8, 1, 0]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    {
        let mut lhsv = parse!("[5] $ $ _1 $ $ ");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[5] $ $ _1 _2 _1");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xffu8, 0xffu8, 1, 0]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    {
        let mut lhsv = parse!("[2] [2] flip [3] = [4] R $ $ $ [4] L $ $ $ [2] axiom [3] = [4] L _4 _5 _6 [4] R _1 _2 _3");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[2] [2] flip [3] = [4] R $ $ $ [4] L $ _2 _3 [2] axiom [3] = [4] L _4 _2 _3 [4] R _1 _2 _3");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xff, 0xff, 0xff, 0xff, 1, 2]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    {
        let mut lhsv = parse!("[2] [2] flip [3] = [4] R $ $ $ [4] L $ $ $ [2] axiom [3] = [4] L _4 _5 _6 [4] R _1 _2 _3");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };

        let mut rhsv = parse!("[2] [2] flip [3] = [4] R $ $ $ [4] L _1 $ _3 [2] axiom [3] = [4] L _1 _4 _3 [4] R _1 _2 _3");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        lhs.equate_vars_inplace(&mut [0xff, 0xff, 0xff, 0, 0xff, 2]);

        assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    }
    // {
    //     self  "[2] [2] flip [3] = $ [2] A $ [2] axiom [3] = [2] A _2 [4] B _2 _2 _2"
    //     other "[2] [2] flip [3] = $ [2] A $ [2] axiom [3] = [2] A _2 _1"
    //     osubs (B _2 _2 _2) / _1
    //     sez  (B _2 _2 _2)
    //     intrm "[2] [2] flip [3] = [4] B $ $ $ [2] A $ [2] axiom [3] = [2] A _4 [4] B _1 _2 _3"
    //     after "[2] [2] flip [3] = [4] B $ $ $ [2] A _3 [2] axiom [3] = [2] A _3 [4] B _1 _2 _3"
    //
    //     let mut lhsv = parse!("[2] [2] flip [3] = [4] R $ $ $ [4] L $ $ $ [2] axiom [3] = [4] L _4 _5 _6 [4] R _1 _2 _3");
    //     let lhs = Expr{ ptr: lhsv.as_mut_ptr() };
    //
    //     let mut rhsv = parse!("[2] [2] flip [3] = [4] R $ $ $ [4] L _1 $ _3 [2] axiom [3] = [4] L _1 _4 _3 [4] R _1 _2 _3");
    //     let rhs = Expr{ ptr: rhsv.as_mut_ptr() };
    //
    //     lhs.equate_vars_inplace(&mut [0xff, 0xff, 0xff, 0, 0xff, 2]);
    //
    //     assert_eq!(format!("{:?}", lhs), format!("{:?}", rhs));
    // }
}

#[test]
fn data_matching() {
    {
        // (a $ $) extract_data (a foo bar) == [foo, bar]
        let mut pv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte()
        ];
        let p = Expr { ptr: pv.as_mut_ptr() };
        let mut dv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::SymbolSize(3).byte(), b'f', b'o', b'o',
            Tag::SymbolSize(3).byte(), b'b', b'a', b'r',
        ];
        let d = Expr { ptr: dv.as_mut_ptr() };
        let mut sv1 = vec![Tag::SymbolSize(3).byte(), b'f', b'o', b'o'];
        let s1 = Expr { ptr: sv1.as_mut_ptr() };
        let mut sv2 = vec![Tag::SymbolSize(3).byte(), b'b', b'a', b'r'];
        let s2 = Expr { ptr: sv2.as_mut_ptr() };
        let vs = vec![s1, s2];
        match p.extract_data(&mut ExprZipper::new(d)) {
            Ok(bs) => { assert_eq!(bs.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>(), vs.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>()) }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    {
        // (a $ $) extract_data (a foo (bar baz)) == [foo, (bar baz)]
        let mut pv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::NewVar.byte()
        ];
        let p = Expr { ptr: pv.as_mut_ptr() };
        let mut dv = vec![
            Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'a',
            Tag::SymbolSize(3).byte(), b'f', b'o', b'o',
            Tag::Arity(2).byte(),
            Tag::SymbolSize(3).byte(), b'b', b'a', b'r',
            Tag::SymbolSize(3).byte(), b'b', b'a', b'z',
        ];
        let d = Expr { ptr: dv.as_mut_ptr() };
        let mut sv1 = vec![Tag::SymbolSize(3).byte(), b'f', b'o', b'o'];
        let s1 = Expr { ptr: sv1.as_mut_ptr() };
        let mut sv2 = vec![Tag::Arity(2).byte(),
                           Tag::SymbolSize(3).byte(), b'b', b'a', b'r',
                           Tag::SymbolSize(3).byte(), b'b', b'a', b'z'];
        let s2 = Expr { ptr: sv2.as_mut_ptr() };
        let vs = vec![s1, s2];
        match p.extract_data(&mut ExprZipper::new(d)) {
            Ok(bs) => { assert_eq!(bs.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>(), vs.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>()) }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    // println!("(a $ b (cux $ $ z) c) extract_data (a (foo (bar baz)) b (cux x y z) c) == [(foo (bar baz)), x, y]");
    {
        // (a $ b (cux $ $ z) c) extract_data (a (foo (bar baz)) b (cux x y z) c) == [(foo (bar baz)), x, y]
        let mut pv = vec![
            Tag::Arity(5).byte(),
            Tag::SymbolSize(1).byte(), b'a',
            Tag::NewVar.byte(),
            Tag::SymbolSize(1).byte(), b'b',
            Tag::Arity(4).byte(),
                Tag::SymbolSize(3).byte(), b'c', b'u', b'x',
                Tag::NewVar.byte(),
                Tag::NewVar.byte(),
                Tag::SymbolSize(1).byte(), b'z',
            Tag::SymbolSize(1).byte(), b'c'
        ];
        let p = Expr { ptr: pv.as_mut_ptr() };
        let mut dv = vec![
            Tag::Arity(5).byte(),
            Tag::SymbolSize(1).byte(), b'a',
            Tag::Arity(2).byte(),
                Tag::SymbolSize(3).byte(), b'f', b'o', b'o',
                Tag::Arity(2).byte(),
                    Tag::SymbolSize(3).byte(), b'b', b'a', b'r',
                    Tag::SymbolSize(3).byte(), b'b', b'a', b'z',
            Tag::SymbolSize(1).byte(), b'b',
            Tag::Arity(4).byte(),
                Tag::SymbolSize(3).byte(), b'c', b'u', b'x',
                Tag::SymbolSize(1).byte(), b'x',
                Tag::SymbolSize(1).byte(), b'y',
                Tag::SymbolSize(1).byte(), b'z',
            Tag::SymbolSize(1).byte(), b'c'
        ];
        let d = Expr { ptr: dv.as_mut_ptr() };
        let mut sv1 = vec![Tag::Arity(2).byte(),
                           Tag::SymbolSize(3).byte(), b'f', b'o', b'o',
                           Tag::Arity(2).byte(),
                           Tag::SymbolSize(3).byte(), b'b', b'a', b'r',
                           Tag::SymbolSize(3).byte(), b'b', b'a', b'z'];
        let s1 = Expr { ptr: sv1.as_mut_ptr() };
        let mut sv2 = vec![Tag::SymbolSize(1).byte(), b'x'];
        let s2 = Expr { ptr: sv2.as_mut_ptr() };
        let mut sv3 = vec![Tag::SymbolSize(1).byte(), b'y'];
        let s3 = Expr { ptr: sv3.as_mut_ptr() };
        let vs = vec![s1, s2, s3];
        match p.extract_data(&mut ExprZipper::new(d)) {
            Ok(bs) => { assert_eq!(bs.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>(), vs.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>()) }
            Err(e) => { panic!("{:?}", e); }
        }
    }
}

#[test]
fn counts() {
    // (= (func $) (add`0 (123456789 _1)))
    let mut ev = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'=',
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'f', b'u', b'n', b'c', Tag::NewVar.byte(),
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'a', b'd', b'd', 0,
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), 7, 91, 205, 21, Tag::VarRef(0).byte()];
    let e = Expr { ptr: ev.as_mut_ptr() };
    assert!(e.size() == 10 && e.symbols() == 4 && e.leaves() == 6 && e.newvars() == 1);
}

#[test]
fn unbound() {
    {
        let mut ev = vec![Tag::Arity(3).byte(),
                      Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'a', Tag::NewVar.byte(),
                      Tag::NewVar.byte(),
                      Tag::VarRef(0).byte()];
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert!(!e.has_unbound());
    }
    {
        let mut ev = vec![Tag::Arity(3).byte(),
                          Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'a', Tag::NewVar.byte(),
                          Tag::NewVar.byte(),
                          Tag::VarRef(1).byte()];
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert!(!e.has_unbound());
    }
    {
        let mut ev = vec![Tag::Arity(3).byte(),
                          Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'a', Tag::NewVar.byte(),
                          Tag::NewVar.byte(),
                          Tag::VarRef(2).byte()];
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert!(e.has_unbound());
    }
}

#[test]
fn forward_references() {
    {
        let mut ev = parse!("[2] _1 $");
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert_eq!(e.forward_references(0), 1)
    }
    {
        let mut ev = parse!("[2] _1 $");
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert_eq!(e.forward_references(1), 0)
    }
    {
        let mut ev = parse!("[2] $ _1");
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert_eq!(e.forward_references(0), 0)
    }
    {
        let mut ev = parse!("[4] R _1 _2 _3");
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert_eq!(e.forward_references(0), 3)
    }
    {
        let mut ev = parse!("[4] R $ _2 _3");
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert_eq!(e.forward_references(0), 2)
    }
    {
        let mut ev = parse!("[4] R $ _2 _3");
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert_eq!(e.forward_references(1), 1)
    }
    {
        let mut ev = parse!("[4] R _2 _2 _2");
        let e = Expr { ptr: ev.as_mut_ptr() };
        assert_eq!(e.forward_references(0), 1)
    }
}

#[test]
fn unification() {
    {
        //     [2][2] $ a [2] _1  a  unification
        //     [2][2] b $ [2]  b _1  ==>
        //     [2][2] b a [2]  b  a
        let mut lhsv = vec![Tag::Arity(2).byte(),
                            Tag::Arity(2).byte(), Tag::NewVar.byte(), Tag::SymbolSize(1).byte(), b'a',
                            Tag::Arity(2).byte(), Tag::VarRef(0).byte(), Tag::SymbolSize(1).byte(), b'a'];
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };
        let mut rhsv = vec![Tag::Arity(2).byte(),
                            Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'b', Tag::NewVar.byte(),
                            Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'b', Tag::VarRef(0).byte()];
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };
        let mut rv = vec![Tag::Arity(2).byte(),
                          Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'b', Tag::SymbolSize(1).byte(), b'a',
                          Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'b', Tag::SymbolSize(1).byte(), b'a'];
        let r = Expr{ ptr: rv.as_mut_ptr() };
        match lhs.unification(rhs, Expr{ ptr: vec![0; 512].leak().as_mut_ptr() }) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    {
        // [3] $       a _1        unification
        // [3] [2] b $ $ [2] $ _1  ==>
        // [3] [2] b $ a [2] b _1
        let mut lhsv = vec![Tag::Arity(3).byte(),
                            Tag::NewVar.byte(),
                            Tag::SymbolSize(1).byte(), b'a',
                            Tag::VarRef(0).byte()];
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };
        let mut rhsv = vec![Tag::Arity(3).byte(),
                            Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'b', Tag::NewVar.byte(),
                            Tag::NewVar.byte(),
                            Tag::Arity(2).byte(), Tag::NewVar.byte(), Tag::VarRef(0).byte()];
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };
        let mut rv = vec![Tag::Arity(3).byte(),
                          Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'b', Tag::NewVar.byte(),
                          Tag::SymbolSize(1).byte(), b'a',
                          Tag::Arity(2).byte(), Tag::SymbolSize(1).byte(), b'b', Tag::VarRef(0).byte()];
        let r = Expr{ ptr: rv.as_mut_ptr() };
        match lhs.unification(rhs, Expr{ ptr: vec![0; 512].leak().as_mut_ptr() }) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    {
        //   [4]  $  $ _1 _2  unification
        //   [4]  $  $ _2 _1  ==>
        //   [4]  $ _1 _1 _1
        let mut lhsv = parse!("[5] $ $ _1 _2 A");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };
        let mut rhsv = parse!("[5] $ $ _2 _1 A");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        let mut sdbv = vec![0; 100];
        #[allow(unused_variables)]
        let sdb = Expr{ ptr: sdbv.as_mut_ptr() };
        // rhs.equate_var(1, 0, &mut ExprZipper::new(sdb));
        // lhs.equate_var(1, 0, &mut ExprZipper::new(sdb));
        lhs.equate_var_inplace(1, 0);

        let mut rv = parse!("[5] $ _1 _1 _1 A");
        let r = Expr{ ptr: rv.as_mut_ptr() };

        match lhs.unification(rhs, Expr{ ptr: vec![0; 512].leak().as_mut_ptr() }) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    {
        //   [2] $ [2] axiom [3] = [3] T $ [4] a _1 $ $ _1  unification
        //   [2] [2] flip [3] = $ $ [2] axiom [3] = _2 _1   ==>
        //
        let mut lhsv = parse!("[2] $ [2] axiom [3] = [3] T $ [4] a _2 $ $ _2");
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };
        let mut rhsv = parse!("[2] [2] flip [3] = $ $ [2] axiom [3] = _2 _1");
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };

        let mut rv = parse!("[2] [2] flip [3] = $ [3] T _1 [4] a _1 $ _1 [2] axiom [3] = [3] T _1 [4] a _1 _2 _1 _1");
        let r = Expr{ ptr: rv.as_mut_ptr() };

        let o = Expr{ ptr: vec![0; 512].leak().as_mut_ptr() };
        match lhs.unification(rhs, o) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => {
                println!("lhs  {:?}", lhs);
                println!("rhs  {:?}", rhs);
                println!("out  {:?}", o);
                panic!("{:?}", e); }
        }
    }
}

use freeze::{LiquidVecRef, BumpAllocRef};
pub struct AExpr<'a> {
    buf: LiquidVecRef<'a>
}

impl <'a> AExpr<'a> {
    pub fn new(a: &BumpAllocRef, e: impl AsRef<[u8]>) -> AExpr {
        a.top().extend_from_slice(e.as_ref());
        AExpr { buf: a.top() }
    }

    pub fn used(mut self) -> Expr {
        Expr { ptr: self.buf.as_mut_ptr() }
    }
}

impl <'a> Drop for AExpr<'a>  {
    fn drop(&mut self) {
        self.buf.set_len(0)
    }
}

pub fn with_buffer<Bytes, Body>(alloc: &mut BumpAllocRef, body: Body)
        where Bytes : AsRef<[u8]>, Body : Fn(&mut dyn FnMut(Bytes) -> Expr) -> () {
    let mut allocf = |bs: Bytes| {
        alloc.top().extend_from_slice(bs.as_ref());
        Expr { ptr: alloc.top().as_mut_ptr() }
    };
    body(&mut allocf);
    alloc.top().set_len(0)
}

#[test]
fn transform() {
    let mut buf0 = BumpAllocRef::new();
    with_buffer(&mut buf0, |alloc| {
        let src = alloc(parse!("[2] axiom [3] = [4] L $ $ $ [4] R _1 _2 _3"));
        // let mut srcv = parse!("[2] axiom [3] = [4] L $ $ $ [4] R _1 _2 _3"); let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut patv = parse!("[2] axiom [3] = _2 _1"); let pat = Expr{ ptr: patv.as_mut_ptr() };
        let mut templv = parse!("[2] flip [3] = $ $"); let templ = Expr{ ptr: templv.as_mut_ptr() };

        let mut rv = parse!("[2] flip [3] = [4] R $ $ $ [4] L _1 _2 _3"); let r = Expr{ ptr: rv.as_mut_ptr() };

        match src.transformed(templ, pat) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    });
    {
        let mut srcv = parse!("[2] axiom [3] = [4] L $ $ $ [4] R _1 _2 _3"); let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut patv = parse!("[2] axiom [3] = $ $"); let pat = Expr{ ptr: patv.as_mut_ptr() };
        let mut templv = parse!("[2] flip [3] = _2 _1"); let templ = Expr{ ptr: templv.as_mut_ptr() };

        let mut rv = parse!("[2] flip [3] = [4] R $ $ $ [4] L _1 _2 _3"); let r = Expr{ ptr: rv.as_mut_ptr() };

        match src.transform(pat, templ) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    {
        let mut srcv = parse!("[2] axiom [3] = [4] L $ $ $ [4] R $ _2 _3");
        let src = Expr{ ptr: srcv.as_mut_ptr() };

        let mut patv = parse!("[2] axiom [3] = _2 _1");
        let pat = Expr{ ptr: patv.as_mut_ptr() };

        let mut templv = parse!("[2] flip [3] = $ $");
        let templ = Expr{ ptr: templv.as_mut_ptr() };

        let mut rv = parse!("[2] flip [3] = [4] R $ $ $ [4] L $ _2 _3");
        let r = Expr{ ptr: rv.as_mut_ptr() };

        // [2] [2] flip [3] = [4] R $ $ $ [4] L $ _2 _3 [2] axiom [3] = [4] L _2 _2 _3 [4] R _1 _2 _3
        match src.transformed(templ, pat) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    {
        let mut srcv = parse!("[2] axiom [3] = [4] L $ $ $ [4] R _1 $ _3");
        let src = Expr{ ptr: srcv.as_mut_ptr() };

        let mut patv = parse!("[2] axiom [3] = _2 _1");
        let pat = Expr{ ptr: patv.as_mut_ptr() };

        let mut templv = parse!("[2] flip [3] = $ $");
        let templ = Expr{ ptr: templv.as_mut_ptr() };

        let mut rv = parse!("[2] flip [3] = [4] R $ $ $ [4] L _1 $ _3");
        let r = Expr{ ptr: rv.as_mut_ptr() };

        match src.transformed(templ, pat) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    println!("===");
    {
        // (axiom (= (\ $ 1) (/ 1 (L _1 _1 (\ _1 1)))))
        let mut srcv = parse!(r"[2] axiom [3] = [2] A $ [4] B _1 _1 _1");
        let src = Expr{ ptr: srcv.as_mut_ptr() };

        let mut patv = parse!("[2] axiom [3] = _2 _1");
        let pat = Expr{ ptr: patv.as_mut_ptr() };

        let mut templv = parse!("[2] flip [3] = $ $");
        let templ = Expr{ ptr: templv.as_mut_ptr() };

        let mut rv = parse!(r"[2] flip [3] = [4] B $ _1 _1 [2] A _1");
        let r = Expr{ ptr: rv.as_mut_ptr() };

        match src.transformed(templ, pat) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    println!("===");
    {
        let mut srcv = parse!(r"[2] axiom [3] = [3] T $ [3] * $ _2 [3] T _1 [3] R [4] a _1 $ $ [3] * _2 _2");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut patv = parse!("[2] axiom [3] = _2 _1");
        let pat = Expr{ ptr: patv.as_mut_ptr() };

        let mut templv = parse!("[2] flip [3] = $ $");
        let templ = Expr{ ptr: templv.as_mut_ptr() };

        let mut rv = parse!(r"[2] flip [3] = [3] T $ [3] R [4] a _1 $ $ [3] * $ _4 [3] T _1 [3] * _4 _4");
        let r = Expr{ ptr: rv.as_mut_ptr() };

        match src.transformed(templ, pat) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
}

#[test]
fn to_string() {
    // (= (func $) (add`0 (123456789 _1)))
    let mut e = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'=',
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'f', b'u', b'n', b'c', Tag::NewVar.byte(),
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'a', b'd', b'd', 0,
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), 7, 91, 205, 21, Tag::VarRef(0).byte()];
    // note the \0 is missing
    let ez = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    let s = "(= (func $) (add\x00 (\\x7\\x5b\\xcd\\x15 _1)))";

    assert_eq!(format!("{:?}", ez.root), s);
}

#[test]
fn parsing() {
    let data = parse!("[3] $ [3] $ foo _1 _2");
    assert_eq!(data, [Tag::Arity(3).byte(), Tag::NewVar.byte(), Tag::Arity(3).byte(), Tag::NewVar.byte(), Tag::SymbolSize(3).byte(), b'f', b'o', b'o', Tag::VarRef(0).byte(), Tag::VarRef(1).byte()]);
}

#[test]
fn serializing() {
    let data = serialize(&[Tag::Arity(3).byte(), Tag::NewVar.byte(), Tag::Arity(3).byte(), Tag::NewVar.byte(), Tag::SymbolSize(3).byte(), b'f', b'o', b'o', Tag::VarRef(0).byte(), Tag::VarRef(1).byte()]);
    assert_eq!(data, "[3] $ [3] $ foo _1 _2");

    let e = serialize(vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'=',
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'f', b'u', b'n', b'c', Tag::NewVar.byte(),
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'a', b'd', b'd', 0,
                     Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), 7, 91, 205, 21, Tag::VarRef(0).byte()].as_slice());
    assert_eq!(e, "[3] = [2] func $ [2] add\\x00 [2] \\x07[\\xCD\\x15 _1");
}

#[test]
fn prefix() {
    let mut ev = vec![Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'=',
                           Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'f', b'u', b'n', b'c', Tag::NewVar.byte(),
                           Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), b'a', b'd', b'd', 0,
                           Tag::Arity(2).byte(), Tag::SymbolSize(4).byte(), 7, 91, 205, 21, Tag::VarRef(0).byte()];
    let e = Expr { ptr: ev.as_mut_ptr() };

    let Ok(proper) = e.prefix() else { panic!() };
    let s = serialize(unsafe { &*proper });
    assert_eq!(s, "[3] = [2] func");

    let mut ev = vec![Tag::NewVar.byte()];
    let e = Expr { ptr: ev.as_mut_ptr() };
    let Ok(proper) = e.prefix() else { panic!() };
    assert!(unsafe { &*proper }.is_empty());
}

#[test]
fn difference() {
    {
        let mut xv = parse!(r"a");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"a");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), None);
        assert_eq!(x.constant_difference(y), None);
    }
    {
        let mut xv = parse!(r"[2] a b");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[2] a b");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), None);
        assert_eq!(x.constant_difference(y), None);
    }
    {
        let mut xv = parse!(r"a");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"a");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), None);
        assert_eq!(x.constant_difference(y), None);
    }
    {
        let mut xv = parse!(r"[2] a [3] a b c");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[2] a [2] a b");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), Some(3));
        assert_eq!(x.constant_difference(y), Some(3));
    }
    {
        let mut xv = parse!(r"[2] a [2] a a");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[2] a [2] b a");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), Some(4));
        assert_eq!(x.constant_difference(y), Some(4));
    }
    {
        let mut xv = parse!(r"[2] $ [2] _1 a");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[2] $ [2] _1 a");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), None);
        assert_eq!(x.constant_difference(y), None);
    }
    {
        let mut xv = parse!(r"[2] $ [2] _1 a");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[2] $ [2] $ a");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), Some(3));
        assert_eq!(x.constant_difference(y), None);
    }
    {
        let mut xv = parse!(r"[2] $ [2] axiom [3] = [3] T $ [4] a _2 $ $ _2");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[2] [2] flip [3] = $ $ [2] axiom [3] = _2 _1");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        assert_eq!(x.difference(y), Some(1));
        println!("---");
        println!("{:?}", x.constant_difference(y));
        // assert_eq!(x.constant_difference(y), None);
    }
    // {
    //     (a (b $) (f _1 (g $ $)))
    //     let mut xv = parse!(r"[2] $ [2] _1 a");
    //     let x = Expr{ ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[2] $ [2] $ a");
    //     let y = Expr{ ptr: yv.as_mut_ptr() };
    //     assert_eq!(x.difference(y), Some(3));
    //     assert_eq!(x.constant_difference(y), None);
    // }
}

#[test]
fn solver() {
    // {
    //     let mut s = ExprMapSolver::new();
    //     let mut xv = parse!(r"[2] a [3] x y z");
    //     let x = Expr{ ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[2] a [2] p q");
    //     let y = Expr{ ptr: yv.as_mut_ptr() };
    //     assert!(s.solve(&[x, y]).is_err());
    // }
    // {
    //     let mut s = ExprMapSolver::new();
    //     let mut xv = parse!(r"[2] a [3] x y [2] 1 2");
    //     let x = Expr{ ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[2] a [3] x y [2] 1 2");
    //     let y = Expr{ ptr: yv.as_mut_ptr() };
    //     assert!(s.solve(&[x, y]).is_ok());
    //     // unsafe {s.build_mapping();}
    //     // println!("{:?}", s.subs)
    // }
    // {
    //     let mut s = ExprMapSolver::new();
    //     let mut xv = parse!(r"[2] a [3] $ y [2] 1 $");
    //     let x = Expr{ ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[2] a [3] $ y [2] 1 $");
    //     let y = Expr{ ptr: yv.as_mut_ptr() };
    //     assert!(s.solve(&[x, y]).is_ok());
    //     // unsafe {s.build_mapping();}
    //     // println!("{:?}", s.subs)
    // }
    // {
    //     let mut s = ExprMapSolver::new();
    //     let mut xv = parse!(r"[2] a [3] $ y [2] 1 _1");
    //     let x = Expr{ ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[2] a [3] $ y [2] 1 _1");
    //     let y = Expr{ ptr: yv.as_mut_ptr() };
    //     assert!(s.solve(&[x, y]).is_ok());
    //     // unsafe {s.build_mapping();}
    //     // println!("{:?}", s.subs)
    // }
    // {
    //     let mut s = ExprMapSolver::new();
    //     let mut xv = parse!(r"[2] a [3] $ y [2] 1 _1");
    //     let x = Expr{ ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[2] a [3] $ y [2] 1 $");
    //     let y = Expr{ ptr: yv.as_mut_ptr() };
    //     assert!(s.solve(&[x, y]).is_ok());
    //     // unsafe {s.build_mapping();}
    //     // println!("{:?}", s.subs)
    // }
    // {
    //     let mut s = ExprMapSolver::new();
    //     let mut xv = parse!(r"[2] a [3] $ y [2] 1 $");
    //     let x = Expr{ ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[2] a [3] $ y [2] 1 2");
    //     let y = Expr{ ptr: yv.as_mut_ptr() };
    //     assert!(s.solve(&[x, y]).is_ok());
    //     println!("{:?}", s.subs);
    //     unsafe { s.build_mapping(); }
    //     // println!("{:?}", s.subs)
    // }
    {
        let mut s = ExprMapSolver::new();
        let mut xv = parse!(r"[3] a [2] b $ [3] f $ _1");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[3] a [2] b $ [3] f _1 [3] g $ $");
        let y = Expr{ ptr: yv.as_mut_ptr() };
        s.sources.push(x);
        s.sources.push(y);
        assert!(s.solve().is_ok());
        println!("{:?}", s.subs.iter().map(|(lhs, rhs)| {
            (unsafe { s.resolve_var(*lhs) },
            unsafe { s.abs(*rhs) }
            )
        }).collect::<Vec<_>>());
        // unsafe { s.build_mapping(); }
        let mut buf = vec![0; 512];
        let e = Expr{ ptr: buf.as_mut_ptr() };
        s.ret(&mut ExprZipper::new(e));
        println!("final {e:?}");
    }
}

// #[test]
fn unify_other() {
    // {
    //     let mut xv = parse!(r"[3] a [2] b $ [3] f $ _1");
    //     let x = Expr { ptr: xv.as_mut_ptr() };
    //     let mut yv = parse!(r"[3] a [2] b $ [3] f _1 [3] g $ $");
    //     let y = Expr { ptr: yv.as_mut_ptr() };
    //     let mut sx = vec![ExprEnv::new(0, x)];
    //     let mut sy = vec![ExprEnv::new(1, y)];
    //
    //     println!("{:?}", unify(sx, sy).map(|x| x.iter().map(|(k, v)| {
    //         (*k, *v)
    //     }).collect::<Vec<_>>()));
    // }
    {
        let mut tv = parse!(r"[3] [2] f [2] f a [3] h [2] f [2] f a [2] f a [2] f [2] f a"); // ((f $x) (h $y (f a)) $y)
        let t = Expr { ptr: tv.as_mut_ptr() };

        let mut xv = parse!(r"[3] $ [3] h _1 $ [2] f _2"); // ($z (h $z $w) (f $w))
        let x = Expr { ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2"); // ((f $x) (h $y (f a)) $y)
        let y = Expr { ptr: yv.as_mut_ptr() };

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        assert_eq!(format!("{:?}", to), format!("{:?}", t));
    }
    {
        let mut tv = parse!(r"[4] $ _1 _1 _1"); // $i $i $i $i
        let t = Expr { ptr: tv.as_mut_ptr() };
        
        let mut xv = parse!(r"[4] $ $ _1 _2"); // $a $b $a $b
        let x = Expr { ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[4] $ $ _2 _1"); // $x $y $y $x
        let y = Expr { ptr: yv.as_mut_ptr() };
        
        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        assert_eq!(format!("{:?}", to), format!("{:?}", t));
    }
    {
        let mut tv = parse!(r"[8] $ _1 _1 _1 _1 _1 _1 _1"); // $i $i $i $i $i $i $i $i
        let t = Expr { ptr: tv.as_mut_ptr() };

        let mut xv = parse!(r"[8] $ $ $ $ _3 _2 _3 _4"); // $a $b $c $d $c $b $c $d
        let x = Expr { ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[8] $ $ $ $ _4 _1 _2 _3"); // $x $y $z $w $w $x $y $z
        let y = Expr { ptr: yv.as_mut_ptr() };

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        assert_eq!(format!("{:?}", to), format!("{:?}", t));
    }
    {
        let mut tv = parse!("[2] [2] flip [3] = $ [3] T _1 [4] a _1 $ $ [2] axiom [3] = [3] T _1 [4] a _1 _2 _3 _1");
        //                   ((flip (= $ (T _1 (a _1 $ _1)))) (axiom (= (T _1 (a _1 _2 _1)) _1)))
        let t = Expr{ ptr: tv.as_mut_ptr() };
        
        let mut xv = parse!("[2] $ [2] axiom [3] = [3] T $ [4] a _2 $ $ _2");
        //                   ($res (axiom (= (T $x (a $x $y $z)) $x)))
        //                    result   input-data
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] [2] flip [3] = $ $ [2] axiom [3] = _2 _1");
        //                   ((flip (= $l $r)) (axiom (= $r $l))
        //                    template          pattern
        let y = Expr{ ptr: yv.as_mut_ptr() };

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        assert_eq!(format!("{:?}", to), format!("{:?}", t));
    }
    {
        let mut srcv = parse!(r"[2] axiom [3] = [3] T $ [3] * $ _2 [3] T _1 [3] R [4] a _1 $ $ [3] * _2 _2");
        let src = Expr{ ptr: srcv.as_mut_ptr() };
        let mut patv = parse!("[2] axiom [3] = _2 _1");
        let pat = Expr{ ptr: patv.as_mut_ptr() };
    
        let mut templv = parse!("[2] flip [3] = $ $");
        let templ = Expr{ ptr: templv.as_mut_ptr() };
    
        let mut rv = parse!(r"[2] flip [3] = [3] T $ [3] R [4] a _1 $ $ [3] * $ _4 [3] T _1 [3] * _4 _4");
        let r = Expr{ ptr: rv.as_mut_ptr() };
    
        match src.transformed(templ, pat) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    // println!("================");
    {
        // let mut tv = parse!("");
        // let t = Expr{ ptr: tv.as_mut_ptr() };
    
        let mut xv = parse!("[3] [3] [3] [3] [3] [3] a * $ * $ * $ * $ * $ = [3] _5 * [3] _4 * [3] _3 * [3] _2 * [3] _1 * a");
        //                   ($res (axiom (= (T $x (a $x $y $z)) $x)))
        //                    result   input-data
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[3] $ = _1");
        //                   ((flip (= $l $r)) (axiom (= $r $l))
        //                    template          pattern
        let y = Expr{ ptr: yv.as_mut_ptr() };
    
        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };
    
        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        println!("{:?}", to);
    }
    {
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] * [3] / 1 $ [3] * _1 $ $ _1 [3] \\ _1 1 [3] * _2 [3] * [3] * _3 _1 [3] \\ _1 1");
        //                   (axiom (= (* (* (* (* (/ 1 $) (* _1 $)) $) _1) (\ _1 1)) (* _2 (* (* _3 _1) (\ _1 1)))))
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] * [3] / 1 $ [3] * _1 $ $ _1 [3] \\ _1 1 [3] * _2 [3] * [3] * _3 _1 [3] \\ _1 1");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )
    
        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };
    
        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        assert_eq!(format!("{:?}", to), format!("{:?}", x));
    }
    {
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] / 1 $ $ $ _1 [3] \\ _1 [3] * _2 [3] * _3 _1");
        //                   (axiom (= (* (* (* (* (/ 1 $) (* _1 $)) $) _1) (\ _1 1)) (* _2 (* (* _3 _1) (\ _1 1)))))
        //                   (axiom (= (* (* (* (* (/ 1 $) (* _1 $)) $) _1) (\ _1 1)) (* _1 (* (* _1 _1) (\ _1 1)))))  <- gotten
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] / 1 $ $ _1 [3] K $ $ [3] \\ _1 [3] * _2 [3] * _1 [3] K _3 _4");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        println!("{:?}", to);
    }
    {
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ [3] / 1 $ $ _3 [3] \\ _3 [3] * [3] K _1 [3] T _2 _3 [3] * _4 _3");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ [3] / 1 $ $ _3 [3] \\ _3 [3] * [3] K _1 [3] T _2 [3] / 1 _3 [3] * _4 _3");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        // occurs
        assert!(matches!(x.unify(y, &mut ExprZipper::new(to)), Err(UnificationFailure::Occurs(_, _))));
    }
    {
        // [2] axiom [3] = [3] * [3] * $ [3] \ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4 _2 _2 _2 _2 
        // [2] axiom [3] = [3] * [3] * $ [3] \ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4 [3] \ _2 1 _2 _2 _2

        let mut xv = parse!("[2] axiom [3] = [3] * [3] * $ [3] \\ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4   _2            _2 _2 _2");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * $ [3] \\ $ 1 [3] K $ $ [4] L [3] / [3] * _1 [3] K _3 [3] T _4   [3] \\ _2 1   _2 _2 _2");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        assert!(matches!(x.unify(y, &mut ExprZipper::new(to)), Err(UnificationFailure::Occurs((1, 1), _))));
    }
    {
        let mut tv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ _1 _1 [4] L $ [4] L _1 _1 _1 [3] * _1 _1 [3] * [3] * _1 _1 [3] * [4] L [3] T _1 [3] * _1 _1 _1 _1 _2");
        let t = Expr{ ptr: tv.as_mut_ptr() };
        
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ _1 [4] L $ [4] L _1 _1 _2 [3] * _2 _1 [3] * [3] * _2 _1 [3] * [4] L [3] T _1 [3] * _1 _2 _1 _2 _3");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ _1 [4] L $ [4] L _1 _1 _2 [3] * _2 _1 [3] * [3] * _2 _1 [3] * [4] L [3] T _1 [3] * _2 _1 _1 _2 _3");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        assert!(x.unify(y, &mut ExprZipper::new(to)).is_ok());
        assert_eq!(format!("{:?}", to), format!("{:?}", t));
    }
    {
        //   
        // 
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ _1 _2 [3] * _2 [3] * _1 [3] * _2 _1");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ _1 $ [3] * [3] * _1 _1 _2 [3] * [3] * _1 [3] * _1 _2 [3] * _1 [3] * _1 _2");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
    }
    {
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ $ [3] K _2 _1 [3] T [3] * [3] * _2 _1 _3 [3] K _2 _1");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * $ $ $ [3] K _1 [4] L _2 [3] * _2 _1 _3 [3] T [3] * [3] * _2 _1 _3 [3] K _1 _2");
        let y = Expr{ ptr: yv.as_mut_ptr() };
    
        // x.serialize2()
        // println!("{}", )
    
        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };
    
        println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
    }
    {
        // LHS (axiom (= (* (* (* (K $ $) $) $) (a _2 _1 (K _4 _3       ))) (* (* (K _1 (L _2 _4 _3)) _4) (T _3 _4))))
        // RHS (axiom (= (* (* (* (K $ $) $) $) (a _1 _4 (K _3 (T _2 _4)))) (* (* (K _1 (L _2 _4 _3)) _4) (T _3 _4))))
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ $ $ [4] a _2 _1 [3] K _4 _3 [3] * [3] * [3] K _1 [4] L _2 _4 _3 _4 [3] T _3 _4");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * [3] * [3] K $ $ $ $ [4] a _1 _4 [3] K _3 [3] T _2 _4 [3] * [3] * [3] K _1 [4] L _2 _4 _3 _4 [3] T _3 _4");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
    }
    {
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * $ [3] * $ _2 _2 [3] * _1 [3] * [3] * _2 _2 _2");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * $ [3] * $ [3] \\ $ 1 [3] \\ [3] \\ _3 1 1 [3] * [3] / 1 _3 [3] * [3] * _3 _1 _2");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
    }
    {
        let mut xv = parse!("[2] axiom [3] = [3] * [3] * $ [3] T $ $ _3 [3] * [3] * _1 _2 [3] T _3 _2");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!("[2] axiom [3] = [3] * [3] * $ [3] T $ $ [3] T [3] T _2 _3 $ [3] * [3] * _1 _2 [3] T _2 [3] T _4 _3");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
    }
    println!("=================");
    {
        let mut xv = parse!(r"[2] axiom [3] = [3] * [3] K $ [3] * [3] \ $ [3] \ _2 $ [3] / $ 1 [3] T [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] * _3 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3");
        let x = Expr{ ptr: xv.as_mut_ptr() };
        let mut yv = parse!(r"[2] axiom [3] = [3] * [3] K $ [3] * [3] \ $ [3] \ _2 $ [3] / $ 1 [3] T [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] * _3 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3 [3] T _1 [3] \ _2 [3] \ _2 [3] \ [3] \ _4 [3] \ _2 [3] \ _2 _3 [3] \ _2 [3] \ _2 _3");
        let y = Expr{ ptr: yv.as_mut_ptr() };

        // x.serialize2()
        // println!("{}", )

        let tov = vec![0u8; 512];
        let to = Expr{ ptr: tov.leak().as_mut_ptr() };

        println!("{:?}", x.unify(y, &mut ExprZipper::new(to)));
    }
      
    
}

fn main() {
    const NAMES: &[&str] = &["A", "B", "C", "D", "E", "F", "G"];
    let mut yv = parse!(r"[3] [2] f $ [3] h $ [2] f a _2");
    let y = Expr { ptr: yv.as_mut_ptr() };

    let mut s = vec![];

    y.serialize_highlight(&mut s, |s| { std::str::from_utf8(s).unwrap() }, |v, _intro|
        format!("\x1B[4m{}\x1B[24m", NAMES[v as usize]).leak(), 1);
    println!("{}", std::str::from_utf8(&s[..]).unwrap());

    unify_other()
}