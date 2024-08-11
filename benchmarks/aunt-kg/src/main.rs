use std::hint::black_box;
use std::io::Read;
use std::ops::Deref;
use std::process::exit;
use std::ptr;
use std::ptr::slice_from_raw_parts;
use std::time::Instant;
use mork_bytestring::*;
use mork_frontend::bytestring_parser::{Parser, BufferedIterator};
use ringmap::trie_map::BytesTrieMap;
use ringmap::zipper::{ReadZipper, WriteZipper, Zipper};
use ringmap::ring::Lattice;

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


static mut ARITIES: [u64; 4] = [0u64; 4];

struct CfIter<'a> {
    i: u8,
    w: u64,
    mask: &'a [u64; 4]
}

impl <'a> CfIter<'a> {
    fn new(mask: &'a [u64; 4]) -> Self {
        Self {
            i: 0,
            w: mask[0],
            mask: mask
        }
    }
}

impl <'a> Iterator for CfIter<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        loop {
            if self.w != 0 {
                let wi = self.w.trailing_zeros() as u8;
                self.w ^= 1u64 << wi;
                let index = self.i*64 + wi;
                return Some(index)
            } else if self.i < 3 {
                self.i += 1;
                self.w = *unsafe{ self.mask.get_unchecked(self.i as usize) };
            } else {
                return None
            }
        }
    }
}

fn mask_and(l: [u64; 4], r: [u64; 4]) -> [u64; 4] {
    [l[0] & r[0], l[1] & r[1], l[2] & r[2], l[3] & r[3]]
}

fn drop_symbol_head_2(loc: &mut WriteZipper<u64>) {
    let m = mask_and(loc.child_mask(), unsafe { ARITIES });
    let mut it = CfIter::new(&m);

    let p = loc.path().to_vec();
    while let Some(b) = it.next() {
        if let Tag::SymbolSize(s) = byte_item(b) {
            let buf = [b];
            assert!(loc.descend_to(buf));
            assert!(loc.drop_head(s as usize));
            assert!(loc.ascend(1));
        } else {
            unreachable!()
        }
    }
    loc.reset();
    loc.descend_to(&p[..]);
    loc.drop_head(1);
}

fn main() {
    for size in 1..64 {
        let k = item_byte(Tag::SymbolSize(size));
        unsafe { ARITIES[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111); }
    }

    // let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/toy.metta")
    let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92_simple.metta")
        .expect("Should have been able to read the file");
    let mut it = BufferedIterator{ file: file, buffer: [0; 4096], cursor: 4096, max: 4096 };
    let mut parser = DataParser::new();

    let t0 = Instant::now();
    let mut family = BytesTrieMap::new();
    let family_ptr = &mut family as *mut BytesTrieMap<u64>;
    let mut output = BytesTrieMap::new();
    let output_ptr = &mut output as *mut BytesTrieMap<u64>;
    let mut i = 0u64;
    let mut stack = Vec::with_capacity(100);
    let mut vs = Vec::with_capacity(100);
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            if parser.sexprUnsafe(&mut it, &mut vs, &mut ez) {
                stack.set_len(ez.loc);
                family.insert(&stack[..], i);
                // unsafe { println!("{}", std::str::from_utf8_unchecked(&stack[..])); }
                // println!("{:?}", stack);
                // ExprZipper::new(ez.root).traverse(0); println!();
                // black_box(ez.root);
            } else { break }
            i += 1;
            vs.set_len(0);
        }
    }
    println!("built {}", i);
    println!("parsing and loading took {} microseconds", t0.elapsed().as_micros());
    println!("total now {}", family.val_count());
    let t1 = Instant::now();

    // family |= family.subst((parent $x $y), (child $y $x))
    // let parent_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(6)), b'p', b'a', b'r', b'e', b'n', b't'];
    let mut parent_path = vec![item_byte(Tag::Arity(3))];
    let parent_symbol = parser.tokenizer("parent".to_string());
    parent_path.push(item_byte(Tag::SymbolSize(parent_symbol.len() as u8)));
    parent_path.extend(parent_symbol.as_bytes());
    // println!("parent prefix {:?}", parent_path);
    let mut parent_zipper = family.read_zipper_at_path(&parent_path[..]);
    // let child_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(5)), b'c', b'h', b'i', b'l', b'd'];
    let mut child_path = vec![item_byte(Tag::Arity(3))];
    let child_symbol = parser.tokenizer("child".to_string());
    child_path.push(item_byte(Tag::SymbolSize(child_symbol.len() as u8)));
    child_path.extend(child_symbol.as_bytes());
    let mut full_child_path = child_path.clone(); full_child_path.resize(128, 0);
    let mut child_zipper = unsafe{ &mut *family_ptr }.write_zipper_at_path(&child_path[..]);

    let mut j = 0;
    loop {
        match parent_zipper.to_next_val() {
            None => { break }
            Some(v) => {
                j += 1;
                // println!("iter {} value {}", j, v);
                debug_assert!(family.contains(parent_zipper.origin_path().unwrap()));
                // println!("zipper path {:?}", parent_zipper.path());
                // println!("sub path {:?}", full_parent_path);
                // println!("sub path {}", unsafe { std::str::from_utf8_unchecked(full_parent_path.as_ref()) });
                // should be read zipper
                let mut lhsz = ExprZipper::new(Expr{ ptr: unsafe { std::mem::transmute::<*const u8, *mut u8>(parent_zipper.origin_path().unwrap().as_ptr()) } });
                let mut rhsz = ExprZipper::new(Expr{ ptr: full_child_path.as_mut_ptr() });
                // print!("lhs: "); lhsz.traverse(0); println!();
                lhsz.next_child(); // parent
                lhsz.next_child(); let _1 = lhsz.subexpr(); let _1_span = unsafe { _1.span().as_ref().unwrap() }; // _1_span can actually be constructed from _2 without re-traversing
                lhsz.next_child(); let _2 = lhsz.subexpr(); let _2_span = unsafe { _2.span().as_ref().unwrap() };

                // print!("$1: "); ExprZipper::new(_1).traverse(0); println!();
                // print!("$2: "); ExprZipper::new(_2).traverse(0); println!();
                // println!("$1 span: {:?}", _1_span);
                // println!("$2 span: {:?}", _2_span);

                rhsz.next_child();
                rhsz.next_child();
                rhsz.write_move(_2_span);
                // println!("{}", rhsz.tag_str());
                // rhsz.next_child();
                // println!("{}", rhsz.tag_str());
                rhsz.write_move(_1_span);
                // println!("{:?}", &full_child_path[0..30]);
                // println!("{}", unsafe { std::str::from_utf8_unchecked(&full_child_path[0..30]) });
                // print!("rhs: "); ExprZipper::new(Expr{ ptr: full_child_path.as_mut_ptr() }).traverse(0); println!();

                // assumes rhsz is at the rhs of the expression
                let slice = unsafe { ptr::slice_from_raw_parts(rhsz.root.ptr.byte_offset(child_path.len() as isize), unsafe{&*Expr{ ptr: full_child_path.as_mut_ptr() }.span()}.len() - child_path.len()).as_ref().unwrap() };
                // println!("descending slice {:?}", unsafe { std::str::from_utf8_unchecked(slice.as_ref()) });
                // println!("child_zipper loc {:?}", child_zipper.fork_zipper().origin_path());
                // black_box(slice);
                child_zipper.descend_to(slice);
                child_zipper.set_value(!v);
                child_zipper.reset();
            }
        }
    }

    println!("creating extra index took (child) {} microseconds", t1.elapsed().as_micros());
    println!("total now {}", family.val_count());
    // let mut cs = family.cursor();
    // loop {
    //     match cs.next() {
    //         None => { break }
    //         Some((k, v)) => {
    //             println!("cursor {:?}", unsafe { std::str::from_utf8_unchecked(k.as_ref()) });
    //             println!("cursor {:?}", k)
    //         }
    //     }
    // }
    let t2 = Instant::now();

    let mut female_path = vec![item_byte(Tag::Arity(2))];
    let female_symbol = parser.tokenizer("female".to_string());
    female_path.push(item_byte(Tag::SymbolSize(female_symbol.len() as u8)));
    female_path.extend(female_symbol.as_bytes());
    let mut female_zipper = family.read_zipper_at_path(&female_path[..]);

    let mut male_path = vec![item_byte(Tag::Arity(2))];
    let male_symbol = parser.tokenizer("male".to_string());
    male_path.push(item_byte(Tag::SymbolSize(male_symbol.len() as u8)));
    male_path.extend(male_symbol.as_bytes());

    let male_zipper = family.read_zipper_at_path(&male_path[..]);

    let mut person_path = vec![item_byte(Tag::Arity(2))];
    let person_symbol = parser.tokenizer("person".to_string());
    person_path.push(item_byte(Tag::SymbolSize(person_symbol.len() as u8)));
    person_path.extend(person_symbol.as_bytes());

    let mut person_zipper = unsafe{ &mut *family_ptr }.write_zipper_at_path(&person_path[..]);

    person_zipper.graft(&female_zipper);
    unsafe{ &mut *family_ptr }.write_zipper_at_path(&person_path[..]).join(&male_zipper);

    println!("creating extra index took (person) {} microseconds", t2.elapsed().as_micros());
    println!("total now {}", family.val_count());

    let t3 = Instant::now();

    let mut parent_query_out_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'0'];
    let mut parent_query_out_zipper = unsafe{ &mut *output_ptr }.write_zipper_at_path(&parent_query_out_path[..]);

    assert!(family.read_zipper_at_path(&person_path[..]).path_exists());

    // unsafe{ &mut *family_ptr }.write_zipper().subtract(
    //     &family.read_zipper_at_path(& [3, 193, 48, 197, 76, 105, 122, 122, 121, 195, 84, 111, 109]));

    // println!("person path {:?}", person_path);
    // println!("person path {:?}", unsafe { std::str::from_utf8_unchecked(person_path.as_ref()) });
    // println!("child path {:?}", unsafe { std::str::from_utf8_unchecked(child_path.as_ref()) });
    // println!("child subtrie size {:?}", unsafe{ &mut *family_ptr }.read_zipper_at_path(&child_path[..]).val_count());
    parent_query_out_zipper.graft(&family.read_zipper_at_path(&child_path[..]));
    parent_query_out_zipper.reset();
    assert!(parent_query_out_zipper.restrict(&family.read_zipper_at_path(&person_path[..])));

    println!("getting all parents took {} microseconds", t3.elapsed().as_micros());
    println!("total out now {}", output.val_count());
    let t4 = Instant::now();
    let mut mother_query_out_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'1'];
    let mut mother_query_out_zipper = unsafe{ &mut *output_ptr }.write_zipper_at_path(&mother_query_out_path[..]);

    let mut person_rzipper = family.read_zipper_at_path(&person_path[..]);
    let mut child_rzipper = family.read_zipper_at_path(&child_path[..]);
    female_zipper.reset();

    // use ringmap::counters;
    // let C1 = counters::Counters::count_ocupancy(&output);
    // println!("previous tn count {}", C1.total_child_items() as f64/C1.total_nodes() as f64);
    // C1.print_histogram_by_depth();
    let mut j = 0;
    loop {
        match person_rzipper.to_next_val() {
            None => { break }
            Some(v) => {
                j += 1;
                // println!("iter {} value {}", j, v);
                // debug_assert!(family.contains(person_rzipper.origin_path().unwrap()));
                // println!("zipper path {:?}", person_rzipper.path());
                // println!("sub path {:?}", person_rzipper.origin_path().unwrap());
                // println!("sub path {}", unsafe { std::str::from_utf8_unchecked(person_rzipper.origin_path().unwrap()) });

                child_rzipper.reset();
                if !child_rzipper.descend_to(person_rzipper.path()) { continue }

                // println!("child zipper path {:?}", child_rzipper.path());
                // println!("child sub path {:?}", child_rzipper.origin_path().unwrap());
                // println!("child sub path {}", unsafe { std::str::from_utf8_unchecked(child_rzipper.origin_path().unwrap()) });
                mother_query_out_zipper.reset();
                mother_query_out_zipper.descend_to(person_rzipper.path());

                // mother_query_out_zipper.set_value(0);
                // mother_query_out_zipper.meet_2(&child_rzipper, &female_zipper);

                mother_query_out_zipper.graft(&child_rzipper);
                assert!(mother_query_out_zipper.meet(&female_zipper));
            }
        }
    }

    println!("getting all mothers took {} microseconds", t4.elapsed().as_micros());
    println!("j {}", j);
    println!("total out now {}", output.val_count());
    // let C2 = counters::Counters::count_ocupancy(&output);
    // println!("previous tn count {}", C2.total_child_items() as f64/C2.total_nodes() as f64);
    // C2.print_histogram_by_depth();

    // val r = ((family("parent") <| family(Concat("child", person))).tail /\ family("female")) \ Singleton(person)
    let t5 = Instant::now();

    let mut sister_query_out_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'2'];
    let mut sister_query_out_zipper = unsafe{ &mut *output_ptr }.write_zipper_at_path(&sister_query_out_path[..]);

    person_rzipper.reset();
    let mut j = 0;
    loop {
        match person_rzipper.to_next_val() {
            None => { break }
            Some(v) => {
                j += 1;
                // println!("iter {} value {}", j, v);
                // debug_assert!(family.contains(person_rzipper.origin_path().unwrap()));
                // println!("zipper path {:?}", person_rzipper.path());
                // println!("sub path {:?}", person_rzipper.origin_path().unwrap());
                // println!("sub path {}", unsafe { std::str::from_utf8_unchecked(person_rzipper.origin_path().unwrap()) });

                child_rzipper.reset();
                if !child_rzipper.descend_to(person_rzipper.path()) { continue }

                sister_query_out_zipper.reset();
                sister_query_out_zipper.descend_to(person_rzipper.path());
                sister_query_out_zipper.graft(&parent_zipper);
                sister_query_out_zipper.restrict(&child_rzipper);
                drop_symbol_head_2(&mut sister_query_out_zipper);
                assert!(sister_query_out_zipper.meet(&female_zipper));
                // todo remove person_rzipper.path() from sister_query_out_zipper
            }
        }
    }

    println!("getting all sisters took {} microseconds", t5.elapsed().as_micros());
    println!("j {}", j);
    println!("total out now {}", output.val_count());

    // let mut cs = output.cursor();
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
