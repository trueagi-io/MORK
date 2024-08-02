use std::io::Read;
use std::ptr;
use std::time::Instant;
use mork::bytestring_parser::{Expr, ExprZipper, Parser, item_byte, BufferedIterator, Tag};
use ringmap::trie_map::BytesTrieMap;
use ringmap::zipper::Zipper;

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
            let slice = gen_key(self.count, buf.as_mut_ptr());
            let string = String::from_utf8_lossy(slice).to_string();
            self.symbols.insert(s.as_bytes(), string.clone());
            string
        }
    }
}

fn main() {
    let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/toy.metta")
    // let mut file = std::fs::File::open("/home/adam/Projects/metta-examples/aunt-kg/royal92_simple.metta")
        .expect("Should have been able to read the file");
    let mut it = BufferedIterator{ file: file, buffer: [0; 4096], cursor: 4096, max: 4096 };
    let mut parser = DataParser::new();

    let t0 = Instant::now();
    let mut family = BytesTrieMap::new();
    let family_ptr = &mut family as *mut BytesTrieMap<i32>;
    let mut i = 0;
    let mut stack = Vec::with_capacity(100);
    let mut vs = Vec::with_capacity(100);
    loop {
        unsafe {
            let mut ez = ExprZipper::new(Expr{ptr: stack.as_mut_ptr()});
            if parser.sexprUnsafe(&mut it, &mut vs, &mut ez) {
                stack.set_len(ez.loc);
                family.insert(&stack[..], i);
                // unsafe { println!("{}", std::str::from_utf8_unchecked(&stack[..])); }
                println!("{:?}", stack);
                ExprZipper::new(ez.root).traverse(0); println!();
                // black_box(ez.root);
            } else { break }
            i += 1;
            vs.set_len(0);
        }
    }
    println!("built {}", i);
    println!("parsing and loading took {} ms", t0.elapsed().as_millis()); // 7ms
    let t1 = Instant::now();

    // family |= family.subst((parent $x $y), (child $y $x))
    let parent_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(6)), b'p', b'a', b'r', b'e', b'n', b't'];
    let mut full_parent_path = parent_path.clone();
    println!("parent prefix {:?}", parent_path);
    let mut parent_zipper = family.read_zipper_at_path(&parent_path[..]);
    let child_path = vec![item_byte(Tag::Arity(3)), item_byte(Tag::SymbolSize(5)), b'c', b'h', b'i', b'l', b'd'];
    let mut full_child_path = child_path.clone(); full_child_path.resize(128, 0);
    let mut child_zipper = unsafe{ &mut *family_ptr }.write_zipper_at_path(&child_path[..]);

    let mut cs = family.cursor();
    loop {
        match cs.next() {
            None => { break }
            Some((k, v)) => { println!("cursor {:?}", k) }
        }
    }

    loop {
        match parent_zipper.to_next_val() {
            None => { break }
            Some(v) => {
                full_parent_path.extend(parent_zipper.path());
                assert!(family.contains(full_parent_path.clone()));
                println!("zipper path {:?}", parent_zipper.path());
                println!("sub path {:?}", full_parent_path);
                println!("sub path {}", unsafe { std::str::from_utf8_unchecked(full_parent_path.as_ref()) });
                // should be read zipper
                let lhsz = ExprZipper::new(Expr{ ptr: unsafe { std::mem::transmute::<*const u8, *mut u8>(full_parent_path.as_ptr()) } });
                println!("lhs {}", lhsz.traverse(0));
                let mut rhsz = ExprZipper::new(Expr{ ptr: full_child_path.as_mut_ptr() });
                rhsz.next_child();
                println!("rhs {}", rhsz.traverse(0));

                // assumes rhsz is at the rhs of the expression
                let slice = unsafe { ptr::slice_from_raw_parts(rhsz.root.ptr.byte_offset(child_path.len() as isize), rhsz.loc - child_path.len()).as_ref().unwrap() };
                child_zipper.descend_to(slice);
                child_zipper.set_value(-v);
                child_zipper.reset();

                full_parent_path = parent_path.clone();
            }
        }
    }

    println!("creating extra indices took {} ms", t1.elapsed().as_millis()); // ms
}
