use std::io::Read;
use std::time::Instant;
use mork_bytestring::*;
use mork_frontend::bytestring_parser::{ParseContext, Parser, ParserErrorType};
use pathmap::PathMap;
use pathmap::zipper::*;

struct DataParser {
    count: u64,
    symbols: PathMap<u64>,
}

impl DataParser {
    fn new() -> Self {
        Self {
            count: 3,
            symbols: PathMap::new(),
        }
    }

    const EMPTY: &'static [u8] = &[];
}

impl Parser for DataParser {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        // return unsafe { std::mem::transmute(s) };
        if s.len() == 0 { return Self::EMPTY }
        let mut z = self.symbols.write_zipper_at_path(s);
        let r = z.get_val_or_set_mut_with(|| {
            self.count += 1;
            u64::from_be(self.count)
        });
        let bs = (8 - r.trailing_zeros()/8) as usize;
        let l = bs.max(1);
        unsafe { std::slice::from_raw_parts_mut((r as *mut u64 as *mut u8).byte_offset((8 - l) as isize), l) }
    }
}


static mut SIZES: [u64; 4] = [0u64; 4];

fn drop_symbol_head_2<Z: Zipper + ZipperMoving + ZipperWriting<()>>(loc: &mut Z) {
    let m = loc.child_mask() & unsafe { SIZES }.into();
    let mut it = m.iter();

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

fn main() -> Result<(),&'static str> {
    for size in 1..64 {
        let k = Tag::SymbolSize(size).byte();
        unsafe { SIZES[((k & 0b11000000) >> 6) as usize] |= 1u64 << (k & 0b00111111); }
    }

    // let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/toy.metta")
    // let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92_simple.metta")
    let mut file = std::fs::File::open("/Users/admin/Desktop/royal92_simple.metta")
    // let mut file = std::fs::File::open("/Users/admin/Desktop/royal92_chopped.metta")
        .expect("Should have been able to read the file");
    let mut buf = vec![];
    file.read_to_end(&mut buf).unwrap();
    let mut it = ParseContext::new(&buf[..]);
    let mut parser = DataParser::new();

    let t0 = Instant::now();
    let mut family = PathMap::new();
    let mut output = PathMap::new();
    let mut i = 0u64;
    let mut stack = [0u8; 1 << 19];
    loop {
        let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
        match parser.sexpr_(&mut it, &mut ez) {
            Ok(()) => {
                family.set_val_at(&stack[..ez.loc], ());
            }
            Err(err) => if err.error_type == ParserErrorType::InputFinished {
                break
            } else {
                panic!("{:?}", err)
            }
        }

        i += 1;
    }
    println!("built {}", i);
    println!("parsing and loading took {} microseconds", t0.elapsed().as_micros());
    println!("total now {}", family.val_count());
    let t1 = Instant::now();

    let family_head = family.zipper_head();

    // family |= family.subst((parent $x $y), (child $y $x))
    let mut parent_path = vec![Tag::Arity(3).byte()];
    let parent_symbol = parser.tokenizer(b"parent");
    parent_path.push(Tag::SymbolSize(parent_symbol.len() as u8).byte());
    parent_path.extend(parent_symbol);
    let mut parent_zipper = family_head.read_zipper_at_path(&parent_path[..]).map_err(|_|concat!("failed to make parent zipper at", line!(), "in main"))?;
    let mut child_path = vec![Tag::Arity(3).byte()];
    let child_symbol = parser.tokenizer(b"child");
    child_path.push(Tag::SymbolSize(child_symbol.len() as u8).byte());
    child_path.extend(child_symbol);
    let mut full_child_path = child_path.clone(); full_child_path.resize(128, 0);

    let mut child_zipper = family_head.write_zipper_at_exclusive_path(&child_path[..]).map_err(|_|concat!("failed to make child zipper at", line!(), "in main"))?;

    let mut patternv = vec![Tag::Arity(3).byte()];
    patternv.push(Tag::SymbolSize(parent_symbol.len() as u8).byte());
    patternv.extend(parent_symbol); patternv.push(Tag::NewVar.byte()); patternv.push(Tag::NewVar.byte());
    let pattern = Expr{ ptr: patternv.as_mut_ptr() };
    let mut templatev = vec![Tag::Arity(3).byte()];
    templatev.push(Tag::SymbolSize(child_symbol.len() as u8).byte());
    templatev.extend(child_symbol); templatev.push(Tag::VarRef(1).byte()); templatev.push(Tag::VarRef(0).byte());
    let template = Expr{ ptr: templatev.as_mut_ptr() };

    let mut _j = 0;
    while parent_zipper.to_next_val() {
        _j += 1;

        let lhs = Expr{ ptr: parent_zipper.origin_path().as_ptr().cast_mut() };
        let rhs = Expr{ ptr: full_child_path.as_mut_ptr() };
        let mut rhsz = ExprZipper::new(rhs);

        // (parent $ $) => (child _2 _1)
        lhs.transformData(pattern, template, &mut rhsz).unwrap();

        let slice = &rhsz.span()[child_path.len()..];

        child_zipper.descend_to(slice);
        child_zipper.set_val(());
        child_zipper.reset();
    }
    drop(child_zipper);

    println!("creating extra index took (child) {} microseconds", t1.elapsed().as_micros());
    println!("total now {}", family_head.read_zipper_at_borrowed_path(&[]).map_err(|_|concat!("failed to make a read zipper for `family_head` as line ", line!(), " in main."))?.val_count());

    let t2 = Instant::now();

    let child_zipper = unsafe{ family_head.read_zipper_at_borrowed_path_unchecked(&child_path[..]) };

    let mut female_path = vec![Tag::Arity(2).byte()];
    let female_symbol = parser.tokenizer(b"female");
    female_path.push(Tag::SymbolSize(female_symbol.len() as u8).byte());
    female_path.extend(female_symbol);
    let mut female_zipper = family_head.read_zipper_at_path(&female_path[..]).map_err(|_|concat!("failed to make `female_zipper` from `family_head` at line ", line!(), " in main"))?;

    let mut male_path = vec![Tag::Arity(2).byte()];
    let male_symbol = parser.tokenizer(b"male");
    male_path.push(Tag::SymbolSize(male_symbol.len() as u8).byte());
    male_path.extend(male_symbol);

    let male_zipper = family_head.read_zipper_at_path(&male_path[..]).map_err(|_|concat!("failed to make `male_zipper` from `family_head` at line ", line!(), " in main"))?;

    let mut person_path = vec![Tag::Arity(2).byte()];
    let person_symbol = parser.tokenizer(b"person");
    person_path.push(Tag::SymbolSize(person_symbol.len() as u8).byte());
    person_path.extend(person_symbol);

    let mut person_zipper = unsafe{ family_head.write_zipper_at_exclusive_path_unchecked(&person_path[..]) };

    person_zipper.graft(&female_zipper);
    person_zipper.join(&male_zipper);
    drop(person_zipper);

    println!("creating extra index took (person) {} microseconds", t2.elapsed().as_micros());
    println!("total now {}", family_head.read_zipper_at_borrowed_path(&[]).map_err(|_|concat!("failed to make read_zipper from `family_head` at line ", line!(), " in main"))?.val_count());

    let t3 = Instant::now();

    let parent_query_out_path = &[Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'0'];
    let output_head = output.zipper_head();
    let mut parent_query_out_zipper = unsafe{ output_head.write_zipper_at_exclusive_path_unchecked(&parent_query_out_path[..]) };

    assert!(family_head.read_zipper_at_path(&person_path[..]).map_err(|_|concat!("failed to make read_zipper from `family_head` with `person_path` at line ", line!(), " in main"))?.path_exists());

    parent_query_out_zipper.graft(&child_zipper);
    parent_query_out_zipper.reset();
    parent_query_out_zipper.restrict(&family_head.read_zipper_at_path(&person_path[..]).map_err(|_|concat!("failed to make read_zipper from `family_head` with `person_path` at line ", line!(), " in main"))?);
    drop(parent_query_out_zipper);

    println!("getting all parents took {} microseconds", t3.elapsed().as_micros());
    println!("total out now {}", output_head.read_zipper_at_borrowed_path(&[]).map_err(|_|concat!("failed to make read_zipper from `output_head` at line ", line!(), " in main"))?.val_count());

    let t4 = Instant::now();
    let mother_query_out_path = &[Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'1'];
    let mut mother_query_out_zipper = unsafe{ output_head.write_zipper_at_exclusive_path_unchecked(&mother_query_out_path[..]) };

    let mut person_rzipper = family_head.read_zipper_at_path(&person_path[..]).map_err(|_|concat!("failed to make read_zipper from `family_head` with `person_path` at line ", line!(), " in main"))?;
    let mut child_rzipper = child_zipper.fork_read_zipper();
    female_zipper.reset();

    // use pathmap::counters;
    // let C1 = counters::Counters::count_ocupancy(&output);
    // println!("previous tn count {}", C1.total_child_items() as f64/C1.total_nodes() as f64);
    // C1.print_histogram_by_depth();
    let mut _j = 0;
    while person_rzipper.to_next_val() {
        _j += 1;

        child_rzipper.reset();
        if !child_rzipper.descend_to(person_rzipper.path()) { continue }
        mother_query_out_zipper.reset();
        mother_query_out_zipper.descend_to(person_rzipper.path());
        mother_query_out_zipper.graft(&child_rzipper);
        mother_query_out_zipper.meet(&female_zipper);
    }
    drop(mother_query_out_zipper);

    println!("getting all mothers took {} microseconds", t4.elapsed().as_micros());
    // println!("j {_j}");
    println!("total out now {}", output_head.read_zipper_at_borrowed_path(&[]).map_err(|_|concat!("failed to make read_zipper from `output_head` at line ", line!(), " in main"))?.val_count());
    // let C2 = counters::Counters::count_ocupancy(&output);
    // println!("previous tn count {}", C2.total_child_items() as f64/C2.total_nodes() as f64);
    // C2.print_histogram_by_depth();

    // val r = ((family("parent") <| family(Concat("child", person))).tail /\ family("female")) \ Singleton(person)
    let t5 = Instant::now();

    let sister_query_out_path = &[Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'2'];
    let mut sister_query_out_zipper = unsafe{ output_head.write_zipper_at_exclusive_path_unchecked(&sister_query_out_path[..]) };

    person_rzipper.reset();
    let mut _j = 0;
    while person_rzipper.to_next_val() {
        _j += 1;

        child_rzipper.reset();
        if !child_rzipper.descend_to(person_rzipper.path()) { continue }
        sister_query_out_zipper.reset();
        sister_query_out_zipper.descend_to(person_rzipper.path());
        sister_query_out_zipper.graft(&parent_zipper);
        sister_query_out_zipper.restrict(&child_rzipper);
        drop_symbol_head_2(&mut sister_query_out_zipper);
        sister_query_out_zipper.meet(&female_zipper);
        if sister_query_out_zipper.descend_to(person_rzipper.path()) {
            sister_query_out_zipper.remove_val();
        }
    }
    drop(sister_query_out_zipper);

    println!("getting all sisters took {} microseconds", t5.elapsed().as_micros());
    // println!("j {_j}");
    println!("total out now {}", output_head.read_zipper_at_borrowed_path(&[]).map_err(|_|concat!("failed to make read_zipper from `output_head` at line ", line!(), " in main"))?.val_count());

    //         val parents = family(Concat("child", person))
    //         val grandparents = (family("child") <| parents).tail
    //         val parent_siblings = (family("parent") <| grandparents).tail \ parents
    //         val aunts = parent_siblings /\ family("female")
    let t6 = Instant::now();

    let aunt_query_out_path = &[Tag::Arity(3).byte(), Tag::SymbolSize(1).byte(), b'3'];
    let mut aunt_query_out_zipper = unsafe{ output_head.write_zipper_at_exclusive_path_unchecked(&aunt_query_out_path[..]) };

    person_rzipper.reset();
    parent_zipper.reset();
    let mut _j = 0;
    while person_rzipper.to_next_val() {
        _j += 1;

        child_rzipper.reset();
        if !child_rzipper.descend_to(person_rzipper.path()) { continue }
        aunt_query_out_zipper.reset();
        aunt_query_out_zipper.descend_to(person_rzipper.path());
        aunt_query_out_zipper.graft(&child_zipper);
        aunt_query_out_zipper.restrict(&child_rzipper);
        drop_symbol_head_2(&mut aunt_query_out_zipper);
        if !aunt_query_out_zipper.restricting(&parent_zipper) { continue }
        drop_symbol_head_2(&mut aunt_query_out_zipper);
        aunt_query_out_zipper.subtract(&child_rzipper);
        aunt_query_out_zipper.meet(&female_zipper);
    }
    drop(aunt_query_out_zipper);

    println!("getting all aunts took {} microseconds", t6.elapsed().as_micros());
    // println!("j {_j}");
    println!("total out now {}", output_head.read_zipper_at_borrowed_path(&[]).map_err(|_|concat!("failed to make read_zipper from `output_head` at line ", line!(), " in main"))?.val_count());

    /*
    iter-optimization (interning, all-dense-nodes)
    built 11809
    parsing and loading took 12764 microseconds
    total now 11809
    creating extra index took (child) 1319 microseconds
    total now 14619
    creating extra index took (person) 32 microseconds
    total now 17616
    getting all parents took 21 microseconds
    total out now 2788
    getting all mothers took 877 microseconds
    total out now 4155
    getting all sisters took 3125 microseconds
    total out now 7167
    getting all aunts took 4177 microseconds
    total out now 10140
    real    0m0.028s
    user    0m0.024s
    sys     0m0.003s

    iter-optimization (interning)
    built 11809
    parsing and loading took 4185 microseconds
    total now 11809
    creating extra index took (child) 669 microseconds
    total now 14619
    creating extra index took (person) 29 microseconds
    total now 17616
    getting all parents took 20 microseconds
    total out now 2788
    getting all mothers took 388 microseconds
    total out now 4155
    getting all sisters took 3320 microseconds
    total out now 7167
    getting all aunts took 5656 microseconds
    total out now 10140
    real    0m0.017s
    user    0m0.014s
    sys     0m0.003s

    iter-optimization (no interning)
    built 11809
    parsing and loading took 3323 microseconds
    total now 11809
    creating extra index took (child) 933 microseconds
    total now 14619
    creating extra index took (person) 65 microseconds
    total now 17616
    getting all parents took 89 microseconds
    total out now 2788
    getting all mothers took 862 microseconds
    total out now 4155
    getting all sisters took 4627 microseconds
    total out now 7167
    getting all aunts took 6597 microseconds
    total out now 10140
    real    0m0.021s
    user    0m0.017s
    sys     0m0.004s

    master (interning, all-dense-nodes)
    built 11809
    parsing and loading took 10048 microseconds
    total now 11809
    creating extra index took (child) 1115 microseconds
    total now 14619
    creating extra index took (person) 29 microseconds
    total now 17616
    getting all parents took 17 microseconds
    total out now 2788
    getting all mothers took 821 microseconds
    total out now 4155
    getting all sisters took 2610 microseconds
    total out now 7167
    getting all aunts took 3580 microseconds
    total out now 10140
    real    0m0.023s
    user    0m0.018s
    sys     0m0.005s

    master (interning)
    built 11809
    parsing and loading took 5189 microseconds
    total now 11809
    creating extra index took (child) 1000 microseconds
    total now 14619
    creating extra index took (person) 32 microseconds
    total now 17616
    getting all parents took 25 microseconds
    total out now 2788
    getting all mothers took 514 microseconds
    total out now 4155
    getting all sisters took 4057 microseconds
    total out now 7167
    getting all aunts took 7099 microseconds
    total out now 10140
    real    0m0.021s
    user    0m0.018s
    sys     0m0.003s

    master (no interning)
    built 11809
    parsing and loading took 3525 microseconds
    total now 11809
    creating extra index took (child) 1277 microseconds
    total now 14619
    creating extra index took (person) 68 microseconds
    total now 17616
    getting all parents took 89 microseconds
    total out now 2788
    getting all mothers took 1147 microseconds
    total out now 4155
    getting all sisters took 4921 microseconds
    total out now 7167
    getting all aunts took 6915 microseconds
    total out now 10140
    real    0m0.022s
    user    0m0.018s
    sys     0m0.004s
     */

    // drop(aunt_query_out_zipper);
    // drop(sister_query_out_zipper);
    // drop(parent_query_out_zipper);
    // drop(mother_query_out_zipper);
    // let mut cs = output.read_zipper();
    // loop {
    //     match cs.to_next_val() {
    //         None => { break }
    //         Some(_) => {
    //             let k = cs.path();
    //             println!("cursor {:?}", k);
    //             println!("cursor {:?}", unsafe { std::str::from_utf8_unchecked(k.as_ref()) });
    //             ExprZipper::new(Expr{ ptr: unsafe { std::mem::transmute::<*const u8, *mut u8>(k.as_ptr()) } }).traverse(0); println!();
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

    Ok(())
}
