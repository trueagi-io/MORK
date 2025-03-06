use std::io::Read;
use std::time::Instant;
use std::usize;
use pathmap::trie_map::BytesTrieMap;
use pathmap::zipper::{Zipper, ZipperMoving, ZipperWriting, ZipperCreation};
use num::BigInt;


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

fn drop_symbol_head_byte<Z: ZipperWriting<usize> + Zipper<usize> + ZipperMoving>(loc: &mut Z) {
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

#[allow(unused)]
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
    // let mut file = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/oeis/stripped")
    let mut file = std::fs::File::open("/Users/admin/Desktop/stripped")
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
        match buildz.value() {
            None => { buildz.set_value(i); }
            Some(_v) => { /* keep the smallest integer sequence */ }
        }
        buildz.ascend(s.len());
    }
    drop(buildz);

    println!("building took {} ms", t0.elapsed().as_millis());

    const MAX_OFFSET: u8 = 10;
    let map_head = m.zipper_head();
    for i in 1..(MAX_OFFSET + 1) {
        let k = &[i];
        let t1 = Instant::now();
        let mut z1 = unsafe{ map_head.write_zipper_at_exclusive_path_unchecked(k) };

        z1.graft(&map_head.read_zipper_at_path(&[i - 1]).unwrap());
        drop_symbol_head_byte(&mut z1);

        println!("drophead {i} took {} ms", t1.elapsed().as_millis());
    }
    drop(map_head);

    for i in 0..(MAX_OFFSET + 1) {
        println!("total seqs from {} {}", i, m.read_zipper_at_path(&[i]).val_count());
    }

    const QSEQ: [u64; 6] = [1, 2, 3, 5, 8, 13];
    let mut qseq = encode_seq(QSEQ.into_iter().map(BigInt::from));
    qseq.insert(0, 0);
    let mut q = BytesTrieMap::new();
    for i in 0..(MAX_OFFSET + 1) {
        qseq[0] = i;
        q.insert(&qseq[..], 0usize);
    }

    let t2 = Instant::now();
    let qresult = m.restrict(&q);
    println!("query took {} microseconds", t2.elapsed().as_micros());

    println!("{}", qresult.val_count());
    // for (k, v) in qresult.iter() {
    //     println!("off. {}", k[0]);
    //     println!("seq# {}", *v);
    //     println!("seq: {:?}", decode_seq(&k[1..]));
    // }
    /*
    iter-optimization
    #sequences 375842
    building took 286 ms
    drophead 1 took 84 ms
    drophead 2 took 108 ms
    drophead 3 took 134 ms
    drophead 4 took 158 ms
    drophead 5 took 174 ms
    drophead 6 took 172 ms
    drophead 7 took 175 ms
    drophead 8 took 180 ms
    drophead 9 took 182 ms
    drophead 10 took 183 ms
    total seqs from 0 373311
    total seqs from 1 372919
    total seqs from 2 372375
    total seqs from 3 371402
    total seqs from 4 369349
    total seqs from 5 366400
    total seqs from 6 362984
    total seqs from 7 359506
    total seqs from 8 355119
    total seqs from 9 350419
    total seqs from 10 345056
    query took 119 microseconds
    222
    real    0m6.776s
    user    0m6.424s
    sys     0m0.332s

    master
    #sequences 375842
    building took 262 ms
    drophead 1 took 78 ms
    drophead 2 took 98 ms
    drophead 3 took 124 ms
    drophead 4 took 146 ms
    drophead 5 took 159 ms
    drophead 6 took 170 ms
    drophead 7 took 177 ms
    drophead 8 took 180 ms
    drophead 9 took 184 ms
    drophead 10 took 179 ms
    total seqs from 0 373311
    total seqs from 1 372919
    total seqs from 2 372375
    total seqs from 3 371402
    total seqs from 4 369349
    total seqs from 5 366400
    total seqs from 6 362984
    total seqs from 7 359506
    total seqs from 8 355119
    total seqs from 9 350419
    total seqs from 10 345056
    query took 118 microseconds
    222
    real    0m6.698s
    user    0m6.350s
    sys     0m0.331s
     */
}
