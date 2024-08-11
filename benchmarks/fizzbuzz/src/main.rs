use std::ptr;
use std::time::Instant;
use mork_bytestring::*;
use ringmap::trie_map::BytesTrieMap;
use ringmap::zipper::{ReadZipper, WriteZipper, Zipper};
use ringmap::ring::Lattice;
use mork_frontend::bytestring_parser::Parser;

struct DataParser {
    count: u64,
    symbols: BytesTrieMap<String>,
}

impl DataParser {
    fn new() -> Self {
        Self {
            count: 3,
            symbols: BytesTrieMap::new(),
        }
    }
}

fn gen_key<'a>(i: u64, buffer: *mut u8) -> &'a [u8] {
    let ir = u64::from_be(i);
    unsafe { ptr::write_unaligned(buffer as *mut u64, ir) };
    let bs = (8 - ir.trailing_zeros()/8) as usize;
    let l = bs.max(1);
    unsafe { std::slice::from_raw_parts(buffer.byte_offset((8 - l) as isize), l) }
}

impl Parser for DataParser {
    fn tokenizer(&mut self, s: String) -> String {
        return s;
        if let Some(r) = self.symbols.get(s.as_bytes()) {
            r.clone()
        } else {
            self.count += 1;
            let mut buf: [u8; 8] = [0; 8];
            // let slice = gen_key(self.count, buf.as_mut_ptr());
            let slice = self.count.to_ne_bytes();
            let mut c = 8;
            while (c > 1) { if slice[c - 1] == 0 { c -= 1; } else { break; } }
            let string = String::from_utf8_lossy(&slice[0..c]).to_string();
            self.symbols.insert(s.as_bytes(), string.clone());
            string
        }
    }
}


fn main() {
    let n = 50;

    let mut parser = DataParser::new();

    let mut space = BytesTrieMap::<()>::new();
    let space_ptr = &mut space as *mut BytesTrieMap<()>;


    let t0 = Instant::now();
    let mut buf: [u8; 8] = [0; 8];

    let mut m3_path = vec![item_byte(Tag::Arity(2))];
    let m3_symbol = parser.tokenizer("m3".to_string());
    m3_path.push(item_byte(Tag::SymbolSize(m3_symbol.len() as u8)));
    m3_path.extend(m3_symbol.as_bytes());
    let mut m3_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m3_path[..]);

    for i in (3..n).step_by(3) {
        let slice = gen_key(i, buf.as_mut_ptr());
        m3_zipper.descend_to(&[item_byte(Tag::SymbolSize(slice.len() as u8))]);
        m3_zipper.descend_to(slice);
        m3_zipper.set_value(());
        m3_zipper.reset();
    }

    let mut m5_path = vec![item_byte(Tag::Arity(2))];
    let m5_symbol = parser.tokenizer("m5".to_string());
    m5_path.push(item_byte(Tag::SymbolSize(m5_symbol.len() as u8)));
    m5_path.extend(m5_symbol.as_bytes());
    let mut m5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m5_path[..]);

    for i in (5..n).step_by(5) {
        let slice = gen_key(i, buf.as_mut_ptr());
        m5_zipper.descend_to(&[item_byte(Tag::SymbolSize(slice.len() as u8))]);
        m5_zipper.descend_to(slice);
        m5_zipper.set_value(());
        m5_zipper.reset();
    }

    let mut r_path = vec![item_byte(Tag::Arity(2))];
    let r_symbol = parser.tokenizer("r".to_string());
    r_path.push(item_byte(Tag::SymbolSize(r_symbol.len() as u8)));
    r_path.extend(r_symbol.as_bytes());
    let mut r_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&r_path[..]);

    for i in 1..n {
        let slice = gen_key(i, buf.as_mut_ptr());
        r_zipper.descend_to(&[item_byte(Tag::SymbolSize(slice.len() as u8))]);
        r_zipper.descend_to(slice);
        r_zipper.set_value(());
        r_zipper.reset();
    }

    let mut m35_path = vec![item_byte(Tag::Arity(2))];
    let m35_symbol = parser.tokenizer("m35".to_string());
    m35_path.push(item_byte(Tag::SymbolSize(m35_symbol.len() as u8)));
    m35_path.extend(m35_symbol.as_bytes());
    let mut m35_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m35_path[..]);

    m35_zipper.meet_2(&m3_zipper, &m5_zipper);

    let mut m3n5_path = vec![item_byte(Tag::Arity(2))];
    let m3n5_symbol = parser.tokenizer("m3n5".to_string());
    m3n5_path.push(item_byte(Tag::SymbolSize(m3n5_symbol.len() as u8)));
    m3n5_path.extend(m3n5_symbol.as_bytes());
    let mut m3n5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m3n5_path[..]);

    m3n5_zipper.graft(&m5_zipper);
    m3n5_zipper.subtract(&m3_zipper);

    let mut m5n3_path = vec![item_byte(Tag::Arity(2))];
    let m5n3_symbol = parser.tokenizer("m5n3".to_string());
    m5n3_path.push(item_byte(Tag::SymbolSize(m5n3_symbol.len() as u8)));
    m5n3_path.extend(m5n3_symbol.as_bytes());
    let mut m5n3_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m5n3_path[..]);

    m5n3_zipper.graft(&m3_zipper);
    m5n3_zipper.subtract(&m5_zipper);

    let mut m3m5_path = vec![item_byte(Tag::Arity(2))];
    let m3m5_symbol = parser.tokenizer("m3m5".to_string());
    m3m5_path.push(item_byte(Tag::SymbolSize(m3m5_symbol.len() as u8)));
    m3m5_path.extend(m3m5_symbol.as_bytes());
    let mut m3m5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&m3m5_path[..]);

    m3m5_zipper.graft(&m3_zipper);
    m3m5_zipper.join(&m5_zipper);

    let mut n3n5_path = vec![item_byte(Tag::Arity(2))];
    let n3n5_symbol = parser.tokenizer("n3n5".to_string());
    n3n5_path.push(item_byte(Tag::SymbolSize(n3n5_symbol.len() as u8)));
    n3n5_path.extend(n3n5_symbol.as_bytes());
    let mut n3n5_zipper = unsafe{ &mut *space_ptr }.write_zipper_at_path(&n3n5_path[..]);

    n3n5_zipper.graft(&r_zipper);
    n3n5_zipper.subtract(&m3m5_zipper);

    let mut wz = unsafe{ &mut *space_ptr }.write_zipper();

    let mut FizzBuzz_path = vec![item_byte(Tag::Arity(2))];
    let FizzBuzz_symbol = parser.tokenizer("FizzBuzz".to_string());
    FizzBuzz_path.push(item_byte(Tag::SymbolSize(FizzBuzz_symbol.len() as u8)));
    FizzBuzz_path.extend(FizzBuzz_symbol.as_bytes());
    wz.descend_to(FizzBuzz_path);
    wz.graft(&m35_zipper);
    wz.reset();
    let mut Nothing_path = vec![item_byte(Tag::Arity(2))];
    let Nothing_symbol = parser.tokenizer("Nothing".to_string());
    Nothing_path.push(item_byte(Tag::SymbolSize(Nothing_symbol.len() as u8)));
    Nothing_path.extend(Nothing_symbol.as_bytes());
    wz.descend_to(Nothing_path);
    wz.graft(&n3n5_zipper);
    wz.reset();
    let mut Fizz_path = vec![item_byte(Tag::Arity(2))];
    let Fizz_symbol = parser.tokenizer("Fizz".to_string());
    Fizz_path.push(item_byte(Tag::SymbolSize(Fizz_symbol.len() as u8)));
    Fizz_path.extend(Fizz_symbol.as_bytes());
    wz.descend_to(Fizz_path);
    wz.graft(&m3n5_zipper);
    wz.reset();
    let mut Buzz_path = vec![item_byte(Tag::Arity(2))];
    let Buzz_symbol = parser.tokenizer("Buzz".to_string());
    Buzz_path.push(item_byte(Tag::SymbolSize(Buzz_symbol.len() as u8)));
    Buzz_path.extend(Buzz_symbol.as_bytes());
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
