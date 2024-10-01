use std::fmt::{format, Formatter};
use std::ptr::slice_from_raw_parts;
use std::str::Utf8Error;
use mork_bytestring::*;

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
    let mut e = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o', item_byte(Tag::NewVar),
                                item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'\xc8', item_byte(Tag::SymbolSize(1)), b'\xc9'];
    let mut ez = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    assert!(ez.next());
    assert!(ez.next());
    assert!(ez.next());
    println!("after 3 next: {}", ez.item_str());
    let mut sez = ExprZipper::new(ez.subexpr());
    // sez.traverse(0);
    println!("{:?}", sez.root);
}

#[test]
fn children() {
    {
        // (= (func $) (add`0 (123456789 _1)))
        let mut e = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'=',
                         item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'f', b'u', b'n', b'c', item_byte(Tag::NewVar),
                         item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'a', b'd', b'd', 0,
                         item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), 7, 91, 205, 21, item_byte(Tag::VarRef(0))];
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
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'A', item_byte(Tag::NewVar), item_byte(Tag::NewVar),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::NewVar), item_byte(Tag::VarRef(3)),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::VarRef(2)), item_byte(Tag::VarRef(3)), item_byte(Tag::VarRef(3)),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'C', item_byte(Tag::NewVar), item_byte(Tag::VarRef(4)),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'C', item_byte(Tag::VarRef(4)), item_byte(Tag::VarRef(4)),
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
    let mut data = vec![vec![item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'F', item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o'],
                                    vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(3)), b'B', b'a', b'r', item_byte(Tag::NewVar), item_byte(Tag::NewVar)]];
    let se = data.iter_mut().map(|mut i| Expr{ ptr: i.as_mut_ptr() }).collect::<Vec<Expr>>();
    // (image (Rel $ $) (Im _2))
    let mut exprv = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(5)), b'i', b'm', b'a', b'g', b'e',
                                    item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(3)), b'R', b'e', b'l', item_byte(Tag::NewVar), item_byte(Tag::NewVar),
                                    item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(2)), b'I', b'm', item_byte(Tag::VarRef(1))];
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
        item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
        item_byte(Tag::NewVar),
        item_byte(Tag::VarRef(0))
    ];
    let r1 = Expr{ ptr: r1v.as_mut_ptr() };
    {
        // assert(r1.substReIndex(Seq($)) == r1)
        let mut s1v = vec![item_byte(Tag::NewVar)];
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
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar)
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::VarRef(0)),
            item_byte(Tag::VarRef(1))
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
        item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'f',
        item_byte(Tag::NewVar),
        item_byte(Tag::NewVar),
        item_byte(Tag::VarRef(0))
    ];
    let r2 = Expr{ ptr: r2v.as_mut_ptr() };
    {
        // assert(r2.substReIndex(Seq(Expr(a, $, $), A)) == Expr(f, Expr(a, $, $), A, Expr(a, _1, _2)))
        let mut s1v = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar)
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![
            item_byte(Tag::SymbolSize(1)), b'A'
        ];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar),
            item_byte(Tag::SymbolSize(1)), b'A',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::VarRef(0)),
            item_byte(Tag::VarRef(1))
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
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar)
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![
            item_byte(Tag::NewVar)
        ];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::VarRef(0)),
            item_byte(Tag::VarRef(1))
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
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::VarRef(0))
        ];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![
            item_byte(Tag::NewVar)
        ];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::VarRef(0)),
            item_byte(Tag::NewVar),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::VarRef(0)),
            item_byte(Tag::VarRef(0))
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
        item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
        item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
        item_byte(Tag::NewVar),
        item_byte(Tag::NewVar),
        item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
        item_byte(Tag::VarRef(1)),
        item_byte(Tag::NewVar),
        item_byte(Tag::VarRef(2))
    ];
    // (, (f $ $) (g _2 $ _3))
    let r3 = Expr{ ptr: r3v.as_mut_ptr() };
    {
        // assert(r3.substReIndex(Seq(a, b, c)) == Expr(`,`, Expr(f, a, b), Expr(g, b, c, c)))
        let mut s1v = vec![item_byte(Tag::SymbolSize(1)), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::SymbolSize(1)), b'b'];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::SymbolSize(1)), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::SymbolSize(1)), b'b',
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::SymbolSize(1)), b'b',
            item_byte(Tag::SymbolSize(1)), b'c',
            item_byte(Tag::SymbolSize(1)), b'c',
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
        let mut s1v = vec![item_byte(Tag::SymbolSize(1)), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::NewVar)];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::SymbolSize(1)), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::VarRef(0)),
            item_byte(Tag::SymbolSize(1)), b'c',
            item_byte(Tag::SymbolSize(1)), b'c',
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
        let mut s1v = vec![item_byte(Tag::SymbolSize(1)), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::NewVar)];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::NewVar)];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::VarRef(0)),
            item_byte(Tag::NewVar),
            item_byte(Tag::VarRef(1)),
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
        let mut s1v = vec![item_byte(Tag::NewVar)];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::NewVar)];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::NewVar)];
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
        let mut s1v = vec![item_byte(Tag::SymbolSize(1)), b'a'];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::NewVar)];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::SymbolSize(1)), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::NewVar),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::VarRef(0)), item_byte(Tag::VarRef(1)),
            item_byte(Tag::SymbolSize(1)), b'c',
            item_byte(Tag::SymbolSize(1)), b'c',
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
        let mut s1v = vec![item_byte(Tag::NewVar)];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::NewVar)];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::NewVar)];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::NewVar),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::NewVar),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::VarRef(1)), item_byte(Tag::VarRef(2)),
            item_byte(Tag::NewVar),
            item_byte(Tag::VarRef(3)),
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
        let mut s1v = vec![item_byte(Tag::NewVar)];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::VarRef(0))];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::SymbolSize(1)), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::NewVar),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::VarRef(1)),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::VarRef(1)), item_byte(Tag::VarRef(1)),
            item_byte(Tag::SymbolSize(1)), b'c',
            item_byte(Tag::SymbolSize(1)), b'c',
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
        let mut s1v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'A', item_byte(Tag::NewVar), item_byte(Tag::NewVar)];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::VarRef(0))];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::SymbolSize(1)), b'c'];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'A', item_byte(Tag::NewVar), item_byte(Tag::NewVar),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::VarRef(2)),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::VarRef(2)), item_byte(Tag::VarRef(2)),
            item_byte(Tag::SymbolSize(1)), b'c',
            item_byte(Tag::SymbolSize(1)), b'c',
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
        let mut s1v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'A', item_byte(Tag::NewVar), item_byte(Tag::NewVar)];
        let s1 = Expr{ ptr: s1v.as_mut_ptr() };
        let mut s2v = vec![item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::NewVar), item_byte(Tag::VarRef(1))];
        let s2 = Expr{ ptr: s2v.as_mut_ptr() };
        let mut s3v = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'C', item_byte(Tag::NewVar), item_byte(Tag::VarRef(0))];
        let s3 = Expr{ ptr: s3v.as_mut_ptr() };
        let mut targetv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b',',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'f',
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'A', item_byte(Tag::NewVar), item_byte(Tag::NewVar),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::NewVar), item_byte(Tag::NewVar), item_byte(Tag::VarRef(3)),
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'g',
            item_byte(Tag::Arity(4)), item_byte(Tag::SymbolSize(1)), b'B', item_byte(Tag::VarRef(2)), item_byte(Tag::VarRef(3)), item_byte(Tag::VarRef(3)),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'C', item_byte(Tag::NewVar), item_byte(Tag::VarRef(4)),
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'C', item_byte(Tag::VarRef(4)), item_byte(Tag::VarRef(4)),
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
}

#[test]
fn data_matching() {
    {
        // (a $ $) extract_data (a foo bar) == [foo, bar]
        let mut pv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar)
        ];
        let p = Expr { ptr: pv.as_mut_ptr() };
        let mut dv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o',
            item_byte(Tag::SymbolSize(3)), b'b', b'a', b'r',
        ];
        let d = Expr { ptr: dv.as_mut_ptr() };
        let mut sv1 = vec![item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o'];
        let s1 = Expr { ptr: sv1.as_mut_ptr() };
        let mut sv2 = vec![item_byte(Tag::SymbolSize(3)), b'b', b'a', b'r'];
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
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::NewVar)
        ];
        let p = Expr { ptr: pv.as_mut_ptr() };
        let mut dv = vec![
            item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o',
            item_byte(Tag::Arity(2)),
            item_byte(Tag::SymbolSize(3)), b'b', b'a', b'r',
            item_byte(Tag::SymbolSize(3)), b'b', b'a', b'z',
        ];
        let d = Expr { ptr: dv.as_mut_ptr() };
        let mut sv1 = vec![item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o'];
        let s1 = Expr { ptr: sv1.as_mut_ptr() };
        let mut sv2 = vec![item_byte(Tag::Arity(2)),
                           item_byte(Tag::SymbolSize(3)), b'b', b'a', b'r',
                           item_byte(Tag::SymbolSize(3)), b'b', b'a', b'z'];
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
            item_byte(Tag::Arity(5)),
            item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::NewVar),
            item_byte(Tag::SymbolSize(1)), b'b',
            item_byte(Tag::Arity(4)),
                item_byte(Tag::SymbolSize(3)), b'c', b'u', b'x',
                item_byte(Tag::NewVar),
                item_byte(Tag::NewVar),
                item_byte(Tag::SymbolSize(1)), b'z',
            item_byte(Tag::SymbolSize(1)), b'c'
        ];
        let p = Expr { ptr: pv.as_mut_ptr() };
        let mut dv = vec![
            item_byte(Tag::Arity(5)),
            item_byte(Tag::SymbolSize(1)), b'a',
            item_byte(Tag::Arity(2)),
                item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o',
                item_byte(Tag::Arity(2)),
                    item_byte(Tag::SymbolSize(3)), b'b', b'a', b'r',
                    item_byte(Tag::SymbolSize(3)), b'b', b'a', b'z',
            item_byte(Tag::SymbolSize(1)), b'b',
            item_byte(Tag::Arity(4)),
                item_byte(Tag::SymbolSize(3)), b'c', b'u', b'x',
                item_byte(Tag::SymbolSize(1)), b'x',
                item_byte(Tag::SymbolSize(1)), b'y',
                item_byte(Tag::SymbolSize(1)), b'z',
            item_byte(Tag::SymbolSize(1)), b'c'
        ];
        let d = Expr { ptr: dv.as_mut_ptr() };
        let mut sv1 = vec![item_byte(Tag::Arity(2)),
                           item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o',
                           item_byte(Tag::Arity(2)),
                           item_byte(Tag::SymbolSize(3)), b'b', b'a', b'r',
                           item_byte(Tag::SymbolSize(3)), b'b', b'a', b'z'];
        let s1 = Expr { ptr: sv1.as_mut_ptr() };
        let mut sv2 = vec![item_byte(Tag::SymbolSize(1)), b'x'];
        let s2 = Expr { ptr: sv2.as_mut_ptr() };
        let mut sv3 = vec![item_byte(Tag::SymbolSize(1)), b'y'];
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
    let mut ev = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'=',
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'f', b'u', b'n', b'c', item_byte(Tag::NewVar),
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'a', b'd', b'd', 0,
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), 7, 91, 205, 21, item_byte(Tag::VarRef(0))];
    let mut e = Expr { ptr: ev.as_mut_ptr() };
    assert!(e.size() == 10 && e.symbols() == 4 && e.leaves() == 6 && e.newvars() == 1);
}

#[test]
fn unbound() {
    {
        let mut ev = vec![item_byte(Tag::Arity(3)),
                      item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'a', item_byte(Tag::NewVar),
                      item_byte(Tag::NewVar),
                      item_byte(Tag::VarRef(0))];
        let mut e = Expr { ptr: ev.as_mut_ptr() };
        assert!(!e.has_unbound());
    }
    {
        let mut ev = vec![item_byte(Tag::Arity(3)),
                          item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'a', item_byte(Tag::NewVar),
                          item_byte(Tag::NewVar),
                          item_byte(Tag::VarRef(1))];
        let mut e = Expr { ptr: ev.as_mut_ptr() };
        assert!(!e.has_unbound());
    }
    {
        let mut ev = vec![item_byte(Tag::Arity(3)),
                          item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'a', item_byte(Tag::NewVar),
                          item_byte(Tag::NewVar),
                          item_byte(Tag::VarRef(2))];
        let mut e = Expr { ptr: ev.as_mut_ptr() };
        assert!(e.has_unbound());
    }
}

#[test]
fn unification() {
    {
        //     [2][2] $ a [2] _1  a  unification
        //     [2][2] b $ [2]  b _1  ==>
        //     [2][2] b a [2]  b  a
        let mut lhsv = vec![item_byte(Tag::Arity(2)),
                            item_byte(Tag::Arity(2)), item_byte(Tag::NewVar), item_byte(Tag::SymbolSize(1)), b'a',
                            item_byte(Tag::Arity(2)), item_byte(Tag::VarRef(0)), item_byte(Tag::SymbolSize(1)), b'a'];
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };
        let mut rhsv = vec![item_byte(Tag::Arity(2)),
                            item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'b', item_byte(Tag::NewVar),
                            item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'b', item_byte(Tag::VarRef(0))];
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };
        let mut rv = vec![item_byte(Tag::Arity(2)),
                            item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'b', item_byte(Tag::SymbolSize(1)), b'a',
                            item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'b', item_byte(Tag::SymbolSize(1)), b'a'];
        let r = Expr{ ptr: rv.as_mut_ptr() };
        match lhs.unification(rhs) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
    {
        // [3] $       a _1        unification
        // [3] [2] b $ $ [2] $ _1  ==>
        // [3] [2] b $ a [2] b _1
        let mut lhsv = vec![item_byte(Tag::Arity(3)),
                            item_byte(Tag::NewVar),
                            item_byte(Tag::SymbolSize(1)), b'a',
                            item_byte(Tag::VarRef(0))];
        let lhs = Expr{ ptr: lhsv.as_mut_ptr() };
        let mut rhsv = vec![item_byte(Tag::Arity(3)),
                            item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'b', item_byte(Tag::NewVar),
                            item_byte(Tag::NewVar),
                            item_byte(Tag::Arity(2)), item_byte(Tag::NewVar), item_byte(Tag::VarRef(0))];
        let rhs = Expr{ ptr: rhsv.as_mut_ptr() };
        let mut rv = vec![item_byte(Tag::Arity(3)),
                          item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'b', item_byte(Tag::NewVar),
                          item_byte(Tag::SymbolSize(1)), b'a',
                          item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'b', item_byte(Tag::VarRef(0))];
        let r = Expr{ ptr: rv.as_mut_ptr() };
        match lhs.unification(rhs) {
            Ok(e) => { assert_eq!(format!("{:?}", e), format!("{:?}", r)); }
            Err(e) => { panic!("{:?}", e); }
        }
    }
}

#[test]
fn to_string() {
    // (= (func $) (add`0 (123456789 _1)))
    let mut e = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'=',
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'f', b'u', b'n', b'c', item_byte(Tag::NewVar),
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'a', b'd', b'd', 0,
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), 7, 91, 205, 21, item_byte(Tag::VarRef(0))];
    // note the \0 is missing
    let mut ez = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    let s = "(= (func $) (add\x00 (\\x7\\x5b\\xcd\\x15 _1)))";

    assert_eq!(format!("{:?}", ez.root), s);
}

#[test]
fn parsing() {
    let data = parse!("[3] $ [3] $ foo _1 _2");
    assert_eq!(data, [item_byte(Tag::Arity(3)), item_byte(Tag::NewVar), item_byte(Tag::Arity(3)), item_byte(Tag::NewVar), item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o', item_byte(Tag::VarRef(0)), item_byte(Tag::VarRef(1))]);
}

#[test]
fn serializing() {
    let data = serialize(&[item_byte(Tag::Arity(3)), item_byte(Tag::NewVar), item_byte(Tag::Arity(3)), item_byte(Tag::NewVar), item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o', item_byte(Tag::VarRef(0)), item_byte(Tag::VarRef(1))]);
    assert_eq!(data, "[3] $ [3] $ foo _1 _2");

    let e = serialize(vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'=',
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'f', b'u', b'n', b'c', item_byte(Tag::NewVar),
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'a', b'd', b'd', 0,
                     item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), 7, 91, 205, 21, item_byte(Tag::VarRef(0))].as_slice());
    assert_eq!(e, "[3] = [2] func $ [2] add\\x00 [2] \\x07[\\xCD\\x15 _1");
}

#[test]
fn prefix() {
    let mut ev = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'=',
                           item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'f', b'u', b'n', b'c', item_byte(Tag::NewVar),
                           item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'a', b'd', b'd', 0,
                           item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), 7, 91, 205, 21, item_byte(Tag::VarRef(0))];
    let e = Expr { ptr: ev.as_mut_ptr() };

    let Ok(proper) = e.prefix() else { panic!() };
    let s = serialize(unsafe { &*proper });
    assert_eq!(s, "[3] = [2] func");

    let mut ev = vec![item_byte(Tag::NewVar)];
    let e = Expr { ptr: ev.as_mut_ptr() };
    let Ok(proper) = e.prefix() else { panic!() };
    assert!(unsafe { &*proper }.is_empty());
}

fn main() {

}