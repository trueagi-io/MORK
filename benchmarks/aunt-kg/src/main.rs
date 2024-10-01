use std::hint::black_box;
use std::io::Read;
use std::time::Instant;
use mork_bytestring::*;
use mork_frontend::bytestring_parser::{Parser, Context, ParserError};
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{ReadZipper, WriteZipper, Zipper};
use pathmap::ring::{Lattice, PartialDistributiveLattice};

struct DataParser {
    count: u64,
    symbols: BytesTrieMap<u64>,
}

impl DataParser {
    fn new() -> Self {
        Self {
            count: 3,
            symbols: BytesTrieMap::new(),
        }
    }

    const EMPTY: &'static [u8] = &[];
}

impl Parser for DataParser {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        // return unsafe { std::mem::transmute(s) };
        if s.len() == 0 { return Self::EMPTY }
        let mut z = self.symbols.write_zipper_at_path(s);
        let r = z.get_value_or_insert_with(|| {
            self.count += 1;
            u64::from_be(self.count)
        });
        let bs = (8 - r.trailing_zeros()/8) as usize;
        let l = bs.max(1);
        unsafe { std::slice::from_raw_parts_mut((r as *mut u64 as *mut u8).byte_offset((8 - l) as isize), l) }
    }
}


static mut SIZES: [u64; 4] = [0u64; 4];

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

fn drop_symbol_head_2(loc: &mut WriteZipper<()>) {
    let m = mask_and(loc.child_mask(), unsafe { SIZES });
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
        unsafe { SIZES[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111); }
    }

    // let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/toy.metta")
    let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92_simple.metta")
        .expect("Should have been able to read the file");
    let mut buf = vec![];
    file.read_to_end(&mut buf);
    let mut it = Context::new(&buf[..]);
    let mut parser = DataParser::new();

    let t0 = Instant::now();
    let mut family = BytesTrieMap::new();
    let mut output = BytesTrieMap::new();
    let mut i = 0u64;
    let mut stack = [0u8; 1 << 19];
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            match parser.sexpr(&mut it, &mut ez) {
                Ok(()) => {
                    family.insert(&stack[..ez.loc], ());
                }
                Err(ParserError::InputFinished) => { break }
                Err(other) => { panic!("{:?}", other) }
            }

            i += 1;
            it.variables.clear();
        }
    }
    println!("built {}", i);
    println!("parsing and loading took {} microseconds", t0.elapsed().as_micros());
    println!("total now {}", family.val_count());
    let t1 = Instant::now();

    // family |= family.subst((parent $x $y), (child $y $x))
    let mut parent_path = vec![item_byte(Tag::Arity(3))];
    let parent_symbol = parser.tokenizer(b"parent");
    parent_path.push(item_byte(Tag::SymbolSize(parent_symbol.len() as u8)));
    parent_path.extend(parent_symbol);
    let mut parent_zipper = family.read_zipper_at_path(&parent_path[..]);
    let mut child_path = vec![item_byte(Tag::Arity(3))];
    let child_symbol = parser.tokenizer(b"child");
    child_path.push(item_byte(Tag::SymbolSize(child_symbol.len() as u8)));
    child_path.extend(child_symbol);
    let mut full_child_path = child_path.clone(); full_child_path.resize(128, 0);
    let mut child_zipper = unsafe{ family.write_zipper_at_exclusive_path_unchecked(&child_path[..]) };

    let mut patternv = vec![item_byte(Tag::Arity(3))];
    patternv.push(item_byte(Tag::SymbolSize(parent_symbol.len() as u8)));
    patternv.extend(parent_symbol); patternv.push(item_byte(Tag::NewVar)); patternv.push(item_byte(Tag::NewVar));
    let pattern = Expr{ ptr: patternv.as_mut_ptr() };
    let mut templatev = vec![item_byte(Tag::Arity(3))];
    templatev.push(item_byte(Tag::SymbolSize(child_symbol.len() as u8)));
    templatev.extend(child_symbol); templatev.push(item_byte(Tag::VarRef(1))); templatev.push(item_byte(Tag::VarRef(0)));
    let template = Expr{ ptr: templatev.as_mut_ptr() };

    let mut j = 0;
    loop {
        match parent_zipper.to_next_val() {
            None => { break }
            Some(v) => {
                j += 1;
                debug_assert!(family.contains(parent_zipper.origin_path().unwrap()));

                let lhs = Expr{ ptr: parent_zipper.origin_path().unwrap().as_ptr().cast_mut() };
                let mut rhs = Expr{ ptr: full_child_path.as_mut_ptr() };
                let mut rhsz = ExprZipper::new(rhs);

                // (parent $ $) => (child _2 _1)
                lhs.transformData(pattern, template, &mut rhsz).unwrap();

                let slice = &rhsz.span()[child_path.len()..];

                child_zipper.descend_to(slice);
                child_zipper.set_value(());
                child_zipper.reset();
            }
        }
    }

    println!("creating extra index took (child) {} microseconds", t1.elapsed().as_micros());
    println!("total now {}", family.val_count());

    let t2 = Instant::now();

    let mut female_path = vec![item_byte(Tag::Arity(2))];
    let female_symbol = parser.tokenizer(b"female");
    female_path.push(item_byte(Tag::SymbolSize(female_symbol.len() as u8)));
    female_path.extend(female_symbol);
    let mut female_zipper = family.read_zipper_at_path(&female_path[..]);

    let mut male_path = vec![item_byte(Tag::Arity(2))];
    let male_symbol = parser.tokenizer(b"male");
    male_path.push(item_byte(Tag::SymbolSize(male_symbol.len() as u8)));
    male_path.extend(male_symbol);

    let male_zipper = family.read_zipper_at_path(&male_path[..]);

    let mut person_path = vec![item_byte(Tag::Arity(2))];
    let person_symbol = parser.tokenizer(b"person");
    person_path.push(item_byte(Tag::SymbolSize(person_symbol.len() as u8)));
    person_path.extend(person_symbol);

    let mut person_zipper = unsafe{ family.write_zipper_at_exclusive_path_unchecked(&person_path[..]) };

    person_zipper.graft(&female_zipper);
    person_zipper.join(&male_zipper);
    drop(person_zipper);

    println!("creating extra index took (person) {} microseconds", t2.elapsed().as_micros());
    println!("total now {}", family.val_count());

    let t3 = Instant::now();

    let mut parent_query_out_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'0'];
    let mut parent_query_out_zipper = unsafe{ output.write_zipper_at_exclusive_path_unchecked(&parent_query_out_path[..]) };

    assert!(family.read_zipper_at_path(&person_path[..]).path_exists());

    parent_query_out_zipper.graft(&child_zipper);
    parent_query_out_zipper.reset();
    assert!(parent_query_out_zipper.restrict(&family.read_zipper_at_path(&person_path[..])));

    println!("getting all parents took {} microseconds", t3.elapsed().as_micros());
    println!("total out now {}", output.val_count());
    let t4 = Instant::now();
    let mut mother_query_out_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'1'];
    let mut mother_query_out_zipper = unsafe{ output.write_zipper_at_exclusive_path_unchecked(&mother_query_out_path[..]) };

    let mut person_rzipper = family.read_zipper_at_path(&person_path[..]);
    let mut child_rzipper = child_zipper.fork_zipper();
    female_zipper.reset();

    // use pathmap::counters;
    // let C1 = counters::Counters::count_ocupancy(&output);
    // println!("previous tn count {}", C1.total_child_items() as f64/C1.total_nodes() as f64);
    // C1.print_histogram_by_depth();
    let mut j = 0;
    loop {
        match person_rzipper.to_next_val() {
            None => { break }
            Some(v) => {
                j += 1;

                child_rzipper.reset();
                if !child_rzipper.descend_to(person_rzipper.path()) { continue }
                mother_query_out_zipper.reset();
                mother_query_out_zipper.descend_to(person_rzipper.path());
                mother_query_out_zipper.graft(&child_rzipper);
                assert!(mother_query_out_zipper.meet(&female_zipper));
            }
        }
    }

    println!("getting all mothers took {} microseconds", t4.elapsed().as_micros());
    // println!("j {}", j);
    println!("total out now {}", output.val_count());
    // let C2 = counters::Counters::count_ocupancy(&output);
    // println!("previous tn count {}", C2.total_child_items() as f64/C2.total_nodes() as f64);
    // C2.print_histogram_by_depth();

    // val r = ((family("parent") <| family(Concat("child", person))).tail /\ family("female")) \ Singleton(person)
    let t5 = Instant::now();

    let mut sister_query_out_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'2'];
    let mut sister_query_out_zipper = unsafe{ output.write_zipper_at_exclusive_path_unchecked(&sister_query_out_path[..]) };

    person_rzipper.reset();
    let mut j = 0;
    loop {
        match person_rzipper.to_next_val() {
            None => { break }
            Some(v) => {
                j += 1;

                child_rzipper.reset();
                if !child_rzipper.descend_to(person_rzipper.path()) { continue }
                sister_query_out_zipper.reset();
                sister_query_out_zipper.descend_to(person_rzipper.path());
                sister_query_out_zipper.graft(&parent_zipper);
                assert!(sister_query_out_zipper.restrict(&child_rzipper));
                drop_symbol_head_2(&mut sister_query_out_zipper);
                assert!(sister_query_out_zipper.meet(&female_zipper));
                if sister_query_out_zipper.descend_to(person_rzipper.path()) {
                    sister_query_out_zipper.remove_value();
                }
            }
        }
    }

    println!("getting all sisters took {} microseconds", t5.elapsed().as_micros());
    // println!("j {}", j);
    println!("total out now {}", output.val_count());

    //         val parents = family(Concat("child", person))
    //         val grandparents = (family("child") <| parents).tail
    //         val parent_siblings = (family("parent") <| grandparents).tail \ parents
    //         val aunts = parent_siblings /\ family("female")
    let t6 = Instant::now();

    let mut aunt_query_out_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(1)), b'3'];
    let mut aunt_query_out_zipper = unsafe{ output.write_zipper_at_exclusive_path_unchecked(&aunt_query_out_path[..]) };

    person_rzipper.reset();
    parent_zipper.reset();
    let mut j = 0;
    loop {
        match person_rzipper.to_next_val() {
            None => { break }
            Some(v) => {
                j += 1;

                child_rzipper.reset();
                if !child_rzipper.descend_to(person_rzipper.path()) { continue }
                aunt_query_out_zipper.reset();
                aunt_query_out_zipper.descend_to(person_rzipper.path());
                aunt_query_out_zipper.graft(&child_zipper);
                assert!(aunt_query_out_zipper.restrict(&child_rzipper));
                drop_symbol_head_2(&mut aunt_query_out_zipper);
                if !aunt_query_out_zipper.restricting(&parent_zipper) { continue }
                drop_symbol_head_2(&mut aunt_query_out_zipper);
                assert!(aunt_query_out_zipper.subtract(&child_rzipper));
                assert!(aunt_query_out_zipper.meet(&female_zipper));
            }
        }
    }


    println!("getting all aunts took {} microseconds", t6.elapsed().as_micros());
    // println!("j {}", j);
    println!("total out now {}", output.val_count());

    /*
built 11809
parsing and loading took 26447 microseconds
total now 11809
creating extra index took (child) 4216 microseconds
total now 14619
creating extra index took (person) 88 microseconds
total now 17616
getting all parents took 298 microseconds
total out now 2788
getting all mothers took 2220 microseconds
total out now 4155
getting all sisters took 7655 microseconds
total out now 7167
getting all aunts took 8615 microseconds
total out now 10140

     */

    // let mut cs = output.read_zipper();
    // loop {
    //     match cs.to_next_val() {
    //         None => { break }
    //         Some(_) => {
    //             let k = cs.path();
    //             println!("cursor {:?}", k);
    //             println!("cursor {:?}", unsafe { std::str::from_utf8_unchecked(k.as_ref()) });
    //             // ExprZipper::new(Expr{ ptr: unsafe { std::mem::transmute::<*const u8, *mut u8>(k.as_ptr()) } }).traverse(0); println!();
    //         }
    //     }
    // }

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
