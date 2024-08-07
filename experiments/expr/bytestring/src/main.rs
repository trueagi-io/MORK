use std::fmt::format;
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

fn traverse_bracketed(ez: &mut ExprZipper) {
    //(, (f(A $ $)(B $ $ _4))(g(B _3 _4 _4)(C $ _5)(C _5 _5)))
    loop {
        // println!("       {:?}", ez.trace);
        let d = ez.trace.len();

        if let Tag::Arity(a) = ez.tag() { print!("(") }
        else { print!(" {} ", &*ez.item_str()) }

        if ez.next_descendant(-1, 0) { continue; }
        // if d > 3 && ez.next_descendant(3, 0) { continue; }
        // if d > 2 && ez.next_descendant(3, 0) { continue; }
        // if d > 1 && ez.next_descendant(2, 0) { continue; }
        // if d > 0 && ez.next_descendant(1, 0) { continue; }
        // if ez.next_descendant(0, 0) { print!("%"); continue; }
        else if ez.parent() { ez.next_child(); print!(")"); continue }
        else { break; }
    }
    // println!("{:?}", ez.parents);
}


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
    traverse(&mut sez);
}

fn children() {
    {
        // (= (func $) (add`0 (123456789 _1)))
        let mut e = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'=',
                         item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'f', b'u', b'n', b'c', item_byte(Tag::NewVar),
                         item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'a', b'd', b'd', 0,
                         item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), 7, 91, 205, 21, item_byte(Tag::VarRef(0))];
        let mut ecz = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
        println!("{} {}", ecz.item_str(), ecz.loc);
        assert!(ecz.next_child());
        println!("{} {}", ecz.item_str(), ecz.loc);
        assert!(ecz.next_child());
        println!("{} {}", ecz.item_str(), ecz.loc);
        assert!(ecz.next_child());
        println!("{} {}", ecz.item_str(), ecz.loc);
        assert!(!ecz.next_child());
    }

    {
        //(, (f(A $ $)(B $ $ _4))(g(B _3 _4 _4)(C $ _5)(C _5 _5)))
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
        print!("e: "); traverse_bracketed(&mut ExprZipper::new(Expr { ptr: e.as_mut_ptr() })); println!();

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

fn substitute() {
    // only used when there's just data substituted in, no variables
    // (F foo); (Bar $ $)
    let mut data = vec![vec![item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(1)), b'F', item_byte(Tag::SymbolSize(3)), b'f', b'o', b'o'],
                                    vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(3)), b'B', b'a', b'r', item_byte(Tag::NewVar), item_byte(Tag::NewVar)]];
    let se = data.iter_mut().map(|mut i| Expr{ ptr: i.as_mut_ptr() }).collect::<Vec<Expr>>();
    // (image (Rel $ $) (Im _2))
    let mut expr = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(5)), b'i', b'm', b'a', b'g', b'e',
                                    item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(3)), b'R', b'e', b'l', item_byte(Tag::NewVar), item_byte(Tag::NewVar),
                                    item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(2)), b'I', b'm', item_byte(Tag::VarRef(1))];

    let mut buffer = vec![0u8; 100];

    for (i, &d) in se.iter().enumerate() {
        let dz = ExprZipper::new(d);
        print!("data_{}: ", i); dz.traverse(0); println!();
    }

    let ez = ExprZipper::new(Expr { ptr: expr.as_mut_ptr() });
    print!("expr: "); ez.traverse(0); println!();

    let mut rz = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });
    Expr{ ptr: expr.as_mut_ptr() }.substitute(&se[..], &mut rz);
    rz.reset(); print!("result: "); rz.traverse(0); println!();
}

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

fn main() {
    // (100 $ (200 201))
    // let mut e = vec![Item::Arity(3), Item::Symbol(100), Item::NewVar, Item::Arity(2), Item::Symbol(200), Item::Symbol(201)];
    // (= (func $) (add`0 (123456789 _1)))
    let mut e = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'=',
                                item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'f', b'u', b'n', b'c', item_byte(Tag::NewVar),
                                item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), b'a', b'd', b'd', 0,
                                    item_byte(Tag::Arity(2)), item_byte(Tag::SymbolSize(4)), 7, 91, 205, 21, item_byte(Tag::VarRef(0))];
    println!("{:?}", e);
    let mut ez = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    // ez.traverse(0); println!();
    traverse(&mut ez);

    println!("---");
    subexpr();

    println!("---");
    children();

    println!("---");
    substitute();

    de_bruijn();
}