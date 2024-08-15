use std::time::Instant;
use mork_bytestring::*;
use ringmap::trie_map::BytesTrieMap;
use ringmap::zipper::Zipper;


fn main() {
    let n = 10000;

    let mut space = BytesTrieMap::<()>::new();
    let space_ptr = &mut space as *mut BytesTrieMap<()>;

    let t0 = Instant::now();

    let mut m3_path = vec![item_byte(Tag::Arity(2))];
    let m3_symbol = "m3".as_bytes();
    m3_path.push(item_byte(Tag::SymbolSize(m3_symbol.len() as u8)));
    m3_path.extend(m3_symbol);
    let mut m3_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m3_path[..]);

    m3_zipper.descend_to(&[item_byte(Tag::SymbolSize(4 as u8))]);
    m3_zipper.graft_map(BytesTrieMap::range::<true, u32>(3, n as u32, 3, ()));
    m3_zipper.reset();

    let mut m5_path = vec![item_byte(Tag::Arity(2))];
    let m5_symbol = "m5".as_bytes();
    m5_path.push(item_byte(Tag::SymbolSize(m5_symbol.len() as u8)));
    m5_path.extend(m5_symbol);
    let mut m5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m5_path[..]);

    m5_zipper.descend_to(&[item_byte(Tag::SymbolSize(4 as u8))]);
    m5_zipper.graft_map(BytesTrieMap::range::<true, u32>(5, n as u32, 5, ()));
    m5_zipper.reset();

    let mut r_path = vec![item_byte(Tag::Arity(2))];
    let r_symbol = "r".as_bytes();
    r_path.push(item_byte(Tag::SymbolSize(r_symbol.len() as u8)));
    r_path.extend(r_symbol);
    let mut r_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&r_path[..]);

    r_zipper.descend_to(&[item_byte(Tag::SymbolSize(4 as u8))]);
    r_zipper.graft_map(BytesTrieMap::range::<true, u32>(1, n as u32, 1, ()));
    r_zipper.reset();

    let mut m35_path = vec![item_byte(Tag::Arity(2))];
    let m35_symbol = "m35".as_bytes();
    m35_path.push(item_byte(Tag::SymbolSize(m35_symbol.len() as u8)));
    m35_path.extend(m35_symbol);
    let mut m35_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m35_path[..]);

    m35_zipper.meet_2(&m3_zipper, &m5_zipper);

    let mut m3n5_path = vec![item_byte(Tag::Arity(2))];
    let m3n5_symbol = "m3n5".as_bytes();
    m3n5_path.push(item_byte(Tag::SymbolSize(m3n5_symbol.len() as u8)));
    m3n5_path.extend(m3n5_symbol);
    let mut m3n5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m3n5_path[..]);

    m3n5_zipper.graft(&m5_zipper);
    m3n5_zipper.subtract(&m3_zipper);

    let mut m5n3_path = vec![item_byte(Tag::Arity(2))];
    let m5n3_symbol = "m5n3".as_bytes();
    m5n3_path.push(item_byte(Tag::SymbolSize(m5n3_symbol.len() as u8)));
    m5n3_path.extend(m5n3_symbol);
    let mut m5n3_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m5n3_path[..]);

    m5n3_zipper.graft(&m3_zipper);
    m5n3_zipper.subtract(&m5_zipper);

    let mut m3m5_path = vec![item_byte(Tag::Arity(2))];
    let m3m5_symbol = "m3m5".as_bytes();
    m3m5_path.push(item_byte(Tag::SymbolSize(m3m5_symbol.len() as u8)));
    m3m5_path.extend(m3m5_symbol);
    let mut m3m5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m3m5_path[..]);

    m3m5_zipper.graft(&m3_zipper);
    m3m5_zipper.join(&m5_zipper);

    let mut n3n5_path = vec![item_byte(Tag::Arity(2))];
    let n3n5_symbol = "n3n5".as_bytes();
    n3n5_path.push(item_byte(Tag::SymbolSize(n3n5_symbol.len() as u8)));
    n3n5_path.extend(n3n5_symbol);
    let mut n3n5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&n3n5_path[..]);

    n3n5_zipper.graft(&r_zipper);
    n3n5_zipper.subtract(&m3m5_zipper);

    let mut wz = unsafe{ &mut *space_ptr }.write_zipper();

    let mut FizzBuzz_path = vec![item_byte(Tag::Arity(2))];
    let FizzBuzz_symbol = "FizzBuzz".as_bytes();
    FizzBuzz_path.push(item_byte(Tag::SymbolSize(FizzBuzz_symbol.len() as u8)));
    FizzBuzz_path.extend(FizzBuzz_symbol);
    wz.descend_to(FizzBuzz_path);
    wz.graft(&m35_zipper);
    wz.reset();
    let mut Nothing_path = vec![item_byte(Tag::Arity(2))];
    let Nothing_symbol = "Nothing".as_bytes();
    Nothing_path.push(item_byte(Tag::SymbolSize(Nothing_symbol.len() as u8)));
    Nothing_path.extend(Nothing_symbol);
    wz.descend_to(Nothing_path);
    wz.graft(&n3n5_zipper);
    wz.reset();
    let mut Fizz_path = vec![item_byte(Tag::Arity(2))];
    let Fizz_symbol = "Fizz".as_bytes();
    Fizz_path.push(item_byte(Tag::SymbolSize(Fizz_symbol.len() as u8)));
    Fizz_path.extend(Fizz_symbol);
    wz.descend_to(Fizz_path);
    wz.graft(&m3n5_zipper);
    wz.reset();
    let mut Buzz_path = vec![item_byte(Tag::Arity(2))];
    let Buzz_symbol = "Buzz".as_bytes();
    Buzz_path.push(item_byte(Tag::SymbolSize(Buzz_symbol.len() as u8)));
    Buzz_path.extend(Buzz_symbol);
    wz.descend_to(Buzz_path);
    wz.graft(&m5n3_zipper);
    wz.reset();

    println!("fizzbuzz took {} microseconds", t0.elapsed().as_micros());
    println!("space size {}", space.val_count());

    // let mut cs = space.cursor();
    // loop {
    //     match cs.next() {
    //         None => { break }
    //         Some((k, v)) => {
    //             println!("cursor {:?}", k);
    //             println!("cursor {:?}", unsafe { std::str::from_utf8_unchecked(k.as_ref()) });
    //             // ExprZipper::new(Expr{ ptr: unsafe { std::mem::transmute::<*const u8, *mut u8>(k.as_ptr()) } }).traverse(0); println!();
    //         }
    //     }
    // }
}
