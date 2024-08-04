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

fn substitute() {
    // only used when there's just data substituted in, no variables
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

    Expr{ ptr: expr.as_mut_ptr() }.substitute(&se[..], buffer.as_mut_ptr());
    let ez = ExprZipper::new(Expr { ptr: buffer.as_mut_ptr() });
    print!("result: "); ez.traverse(0); println!();

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
}