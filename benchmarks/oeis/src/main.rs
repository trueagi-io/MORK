use std::io::Read;
use std::time::Instant;
use mork_bytestring::*;
use ringmap::trie_map::BytesTrieMap;
use ringmap::zipper::{Zipper, ReadZipper, WriteZipper};
use num::{BigInt, zero};


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

fn drop_symbol_head_byte(loc: &mut WriteZipper<usize>) {
    let m = loc.child_mask();
    let mut it = CfIter::new(&m);

    let p = loc.path().to_vec();
    while let Some(b) = it.next() {
        if b == 0 { continue }
        assert!(loc.descend_to(&[b]));
        loc.drop_head(b as usize);
        assert!(loc.ascend(1));
    }
    loc.reset();
    loc.descend_to(&p[..]);
    loc.drop_head(1);
}

fn encode_seq<F : Iterator<Item=BigInt>>(iter: F) -> Vec<u8> {
    let mut v = vec![];
    for n in iter {
        let bs = n.to_signed_bytes_be();
        let bsl = bs.len();
        v.push(bsl as u8);
        v.extend(bs);
    }
    v
}

fn decode_seq(s: &[u8]) -> Vec<BigInt> {
    let mut v = vec![];
    let mut i = 0;
    while i < s.len() {
        let j = s[i] as usize;
        i += 1;
        v.push(BigInt::from_signed_bytes_be(&s[i..i + j]));
        i += j;
    }
    v
}

fn main() {
    let mut file = std::fs::File::open("/run/media/adam/14956caa-2539-4de7-bac9-d5d8416f5f11/OEIS/stripped")
        .expect("Should have been able to read the file");
    let mut s = String::new();
    file.read_to_string(&mut s).unwrap();
    let mut sequences = vec![vec![]];
    let mut i = 0;
    for l in s.lines() {
        if l.starts_with("#") { continue }
        let mut cs = l.split(",").map(|c| {
            let mut cs = c.to_string();
            cs.retain(|c| !c.is_whitespace());
            cs
        });
        let first = cs.next().unwrap();
        let a_number = first.strip_prefix("A").expect("First not A").parse::<usize>().expect("A not followed by a number");
        let numbers = cs.filter(|n| !n.is_empty()).map(|n| n.parse::<BigInt>().expect(format!("not a number {}", n).as_str()));
        let seq = encode_seq(numbers);
        if a_number > sequences.len() { sequences.resize(a_number + 1, vec![]) }
        sequences.insert(a_number, seq);
        i += 1;
    }

    println!("#sequences {}", i);

    let t0 = Instant::now();
    let mut m = BytesTrieMap::new();
    let mut buildz = m.write_zipper_at_path(&[0]);
    for (i, s) in sequences.iter().enumerate() {
        if s.len() == 0 { continue }
        buildz.descend_to(&s[..]);
        match buildz.get_value() {
            None => { buildz.set_value(i); }
            Some(v) => { /* keep the smallest integer sequence */ }
        }
        buildz.ascend(s.len());
    }
    drop(buildz);

    println!("building took {} ms", t0.elapsed().as_millis());

    const MAX_OFFSET: u8 = 10;
    for i in 1..(MAX_OFFSET + 1) {
        let k = &[i];
        let t1 = Instant::now();
        let mut z1 = unsafe{ m.write_zipper_at_exclusive_path_unchecked(k) };

        z1.graft(&m.read_zipper_at_path(&[i - 1]));
        drop_symbol_head_byte(&mut z1);

        println!("drophead {i} took {} ms", t1.elapsed().as_millis());
    }

    for i in 0..(MAX_OFFSET + 1) {
        println!("total seqs from {} {}", i, m.read_zipper_at_path(&[i]).val_count());
    }

    const QSEQ: [u64; 6] = [1, 2, 3, 5, 8, 13];
    let qseq = encode_seq(QSEQ.into_iter().map(BigInt::from));
    let mut q = BytesTrieMap::new();
    let mut qz = q.write_zipper();
    for i in 0..(MAX_OFFSET + 1) {
        qz.descend_to(&[i]);
        qz.descend_to(&qseq[..]);
        qz.set_value(0usize);
        qz.ascend(qseq.len() + 1);
    }
    drop(qz);

    let t2 = Instant::now();
    let qresult = m.restrict(&q);
    println!("query took {} microseconds", t2.elapsed().as_micros());

    println!("{}", qresult.val_count());
    // for (k, v) in qresult.iter() {
    //     println!("off. {}", k[0]);
    //     println!("seq# {}", *v);
    //     println!("seq: {:?}", decode_seq(&k[1..]));
    // }
}
