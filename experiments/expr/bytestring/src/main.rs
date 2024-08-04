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
}