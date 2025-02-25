#![allow(unused)]
#![cfg_attr(rustfmt, rustfmt::skip)]


// let cif = (fn) => (a) => (b) => (x) => (fn(x) ? a : b)(x);



use std::{any::type_name, cell::RefCell, hash::Hasher, io::{BufRead, BufReader, BufWriter, IoSliceMut, Read, Seek, Write}, path::PathBuf};


use pathmap::{morphisms::Catamorphism, trie_map::BytesTrieMap};
extern crate alloc;
use alloc::collections::BTreeMap;
use gxhash::{self, GxHasher};


// Serialization requirements:
// Should at least maintain the current sharing
// Serialization should not traverse all paths (i.e. use pointer caching)
// Needn't be finance/security correct
// Somewhat fast to (de)serialize
// Stable across machines
// Instant verification if serialized trees are the same (plus if this is true for subtrees, too)
// Version, val count, total path bytes count, and longest path in meta-data
// I added a few, let me know what you think @Luke Peterson @Remy_Clarke
// Big plus if we have skip-ahead (which allows for search, even better if it allows for partial deserialization) (modifié)


#[repr(u8)]
#[derive(Debug, Clone, Copy)]
enum Tag {
  Path       = Tag::PATH,
  Value      = Tag::VALUE,
  ChildMask  = Tag::CHILD_MASK,
  Branches   = Tag::BRANCHES,
  PathNode   = Tag::PATH_NODE,
  ValueNode  = Tag::VALUE_NODE,
  BranchNode = Tag::BRANCH_NODE,
}

impl Tag {
  const PATH        : u8 = b'p';
  const VALUE       : u8 = b'v';
  const CHILD_MASK  : u8 = b'c';
  const BRANCHES    : u8 = b'b';
  const PATH_NODE   : u8 = b'P';
  const VALUE_NODE  : u8 = b'V';
  const BRANCH_NODE : u8 = b'B';
}

const OFFSET_LEN     : usize = 8;
const HEX_OFFSET_LEN : usize = OFFSET_LEN*2+1;
type Offset    = [u8;     OFFSET_LEN];
/// the leading byte of a hex offset is an b'x'
type HexOffset = [u8; HEX_OFFSET_LEN];


pub trait ZipperValue : Clone + Send + Sync + Unpin + 'static {}
impl<T> ZipperValue for T where T : Clone + Send + Sync + Unpin + 'static {}


pub struct SeOutputs {
  pub data_path : PathBuf,
  pub data_file : std::fs::File,
  pub meta_path : PathBuf,
  pub meta_file : std::fs::File,
}

pub fn write_trie<V : ZipperValue>(
  memo            : impl AsRef<str>, 
  trie            : BytesTrieMap<V>,
  serialize_value : impl Fn(&V, &mut Vec<u8>),
  out_dir_path    : impl AsRef<std::path::Path>
) -> Result<SeOutputs,std::io::Error>
{
  core::debug_assert_eq!(
    core::alloc::Layout::new::<Offset>().align(), 
    core::alloc::Layout::new::<u8>().align()
  );

  let mut data_path = out_dir_path.as_ref().to_path_buf();
  data_path.push("raw_hex.data");

  let mut meta_path = out_dir_path.as_ref().to_path_buf();
  meta_path.push("meta.data");
  
  
  let mut data_file = std::fs::File::create(&data_path)?;
  data_file.write_fmt(format_args!("{:?} :: {:?}\n", type_name::<BytesTrieMap<V>>(), memo.as_ref()));
  let mut meta_file = std::fs::File::create(&meta_path)?;

  let pos = data_file.stream_position()?;

  // threading a context between the closures
  let ctx = RefCell::new(Ctx {
    count             : 0,
    values            : BTreeMap::new(),
    value_offsets     : Vec::from([pos]),
    data_file,
    algf_scratch      : AlgFScratch::zeroed(),
    serialize_scratch : Vec::with_capacity(4096),
  });

  // Threading the context is tedious, and error prone, so I've delagted to an outside function
  let Accumulator { hash_idx, max_len, val_count, paths_count } = trie.into_cata_jumping_side_effect::<Result<Accumulator, std::io::Error>, _,_,_,_>(
    |     value,       origin_path| register(&mut ctx.borrow_mut(), CataCase::Mapf     (MapF      { origin_path,      value       }), &serialize_value),
    |     value,  acc, origin_path| register(&mut ctx.borrow_mut(), CataCase::CollapseF(CollapseF { origin_path,      value, acc  }), &serialize_value),
    |child_mask, accs, origin_path| register(&mut ctx.borrow_mut(), CataCase::AlgF     (AlgF      { origin_path, child_mask, accs }), &serialize_value),
    |  sub_path,  acc, origin_path| register(&mut ctx.borrow_mut(), CataCase::JumpF    (JumpF     { origin_path,   sub_path, acc  }), &serialize_value),
  )?;

  let Ctx { values, value_offsets, data_file, .. } = ctx.into_inner();

  let mut values_as_vec = values.into_iter().collect::<Vec<_>>();
  values_as_vec.sort_unstable_by(|(_,idx_l), (_,idx_r)| idx_l.cmp(idx_r));



  let values = values_as_vec
    .into_iter()
    .map( |(h,_)| hash_to_hex_string(h) )
    .collect::<Vec<_>>();

  meta_file.write_fmt(format_args!("\
    \nHASHES       : {values:#?},\
    \nFILE_OFFSETS : {value_offsets:?},\
    \nROOT         : {:?}\
    \nMAX_PATH_LEN : {max_len:?},\
    \nVAL_COUNT    : {val_count:?},\
    \nPATHS_COUNT  : {paths_count:?},\
    \n",
    (hash_to_hex_string(hash_idx.0), hash_idx.1)
  ))?;


  Ok(SeOutputs {
    data_path,
    data_file,
    meta_path,
    meta_file,
  })
}

fn hash_to_hex_string(h : u128)->String {
  h.to_be_bytes()
      .map(byte_to_hex)
      .into_iter()
      .fold(String::new(), |mut acc, [t,b]| { acc.push(t as char); acc.push(b as char); acc})
}

// this being true means we need to add the nil hash to the map
#[cfg(test)]#[test] fn gxhash_finish_zero_is_zero() {
  core::assert!(gxhash::GxHasher::with_seed(0).finish_u128() != 0)
}

type ChildMask      = [u64;4];
type OriginPath<'a> = &'a[u8];
type SubPath<'a>    = &'a[u8];
struct MapF     <'a, V     >{ origin_path : OriginPath<'a>, value : &'a V }
struct CollapseF<'a, V, Acc>{ origin_path : OriginPath<'a>, value : &'a V, acc : Acc }
struct AlgF     <'a,    Acc>{ origin_path : OriginPath<'a>, child_mask : &'a ChildMask, accs : &'a mut[Acc]}
struct JumpF    <'a,    Acc>{ origin_path : OriginPath<'a>, sub_path : SubPath<'a>, acc : Acc }
enum CataCase<'a, V, Acc> {
  Mapf     (MapF     <'a,V    >),
  CollapseF(CollapseF<'a,V,Acc>),
  AlgF     (AlgF     <'a,  Acc>),
  JumpF    (JumpF    <'a,  Acc>),
}


type Index = usize;
struct Ctx{
  count             : usize,
  values            : BTreeMap<u128, Index>,
  value_offsets     : Vec<FilePos>,
  data_file         : std::fs::File,
  algf_scratch      : AlgFScratch,
  serialize_scratch : Vec<u8>,
}


struct AlgFScratch {
  buffer : [ HexOffset; 256],
  len    : usize,
}
impl  AlgFScratch {
  const fn zeroed() -> Self { AlgFScratch { buffer: [[0; HEX_OFFSET_LEN];256], len: 0 } }
}

struct Accumulator {
  hash_idx    : (u128, Index),
  max_len     : usize,
  val_count   : usize,
  paths_count : usize,
}
impl Accumulator {
  const fn zeroed() -> Self {  Accumulator { hash_idx: (0,0), max_len: 0, val_count: 0, paths_count: 0}}
}

fn byte_to_hex(b : u8) -> [u8;2] {
  let top = b >> 4;
  let bot = b & 0x_f;
  let unchecked_to_hex = |b : u8| {
    match b {
      0..=9 => b + b'0',
      10..=16 => b - 10 + b'A',
      _ => panic!("found {b}, as char{}", b as char)
    }
  };
  [top, bot].map(unchecked_to_hex)
}
fn offset_to_hex(bytes : Offset) -> HexOffset {
  unsafe { 
    let mut hex = core::mem::transmute::<_,[u8;OFFSET_LEN*2]>( bytes.map( byte_to_hex ) );
    let mut out = [0; HEX_OFFSET_LEN];
    out[0] = b'x';
    (&mut out[1..]).copy_from_slice(&mut hex);
    out
  }

}

enum SerializationStyle {
  Bytes,
  OffsetHexBytes,
  HexBytes,
}
type FilePos = u64;



/// this constant exists purely for debugging compression of zeros
const INCR : usize = 0x_1;

fn register<V>(
  ctx             : &mut Ctx,
  cata_case       : CataCase<'_, V, Result<Accumulator, std::io::Error>>,
  serialize_value : &impl Fn(&V, &mut Vec<u8>),
) -> Result<Accumulator, std::io::Error>
{
  let rollback_or_advance = |context : &mut Ctx, hash : u128, rollback_pos : FilePos | -> Result<(u128, Index), std::io::Error> 
      {

        Ok(
          if let Some(&offset) = context.values.get(&hash) {
            // rollback and use lookup value

            
            let cur_pos = context.data_file.stream_position()?;
            // dbg!(("ROLLBACK", cur_pos, rollback_pos));
            context.data_file.seek_relative(rollback_pos as i64 - cur_pos as i64)?;
            (hash, offset)
          } else {
            // advance

            // dbg!(("ADVANCE", rollback_pos));
            let idx = context.count;
            context.values.insert(hash, idx);
            context.count += INCR;

            context.value_offsets.push(context.data_file.stream_position()?);
            (hash, idx)
          }
        )
      };

  let serialize_with_rollback = |context : &mut Ctx, tag : Tag, i : &mut dyn Iterator<Item = u8>, style :SerializationStyle| -> Result<(u128, Index), std::io::Error>
      {
        let rollback_pos = *context.value_offsets.last().unwrap();
        let mut hasher = GxHasher::with_seed(0);

        hasher.write_u8(tag as u8);
        context.data_file.write(&[tag as u8, b' '])?;
        for b in i {
          // dbg!(b as char);
          

          hasher.write_u8(b);
          // context.data_file.write(
          // )?;
          match style {
            SerializationStyle::Bytes    => context.data_file.write(&[b])?,
            SerializationStyle::HexBytes | SerializationStyle::OffsetHexBytes => context.data_file.write( &byte_to_hex(b) )?
          };
        }
        let hash = hasher.finish_u128();
        context.data_file.write(&[b'\n'])?;

        rollback_or_advance(context, hash, rollback_pos)
      };

  // Val ::=                     Tag,               SeIdx,             SeIdx
  // Val === seed(0) -> write_u8(Tag) -> write_u128(Hash) -> write_u128(Hash)
  let write_node = |context : &mut Ctx, tag : Tag,(value_hash, value_idx) : (u128, Index), (cont_hash, cont_idx) : (u128, Index)| -> Result<(u128, Index), std::io::Error>
      {
        // dbg!((tag, (value_hash, value_idx), (cont_hash, cont_idx)));
        // dbg!(&context.values);
        // dbg!(&context.value_offsets);
        debug_assert_eq!( context.values.get(&value_hash), Some(&value_idx) );
        debug_assert_eq!( context.values.get(&cont_hash),  Some(&cont_idx)  );

        let mut hasher = gxhash::GxHasher::with_seed(0);
        hasher.write_u8(tag as u8);
        hasher.write_u128(value_hash);
        hasher.write_u128(cont_hash);
        let hash = hasher.finish_u128();

        match context.values.get(&hash) {
          Some(&offset) => Ok((hash, offset)),
          None          => {
                             let cur_idx = context.count;
                             let v_offset = value_idx.to_be_bytes();
                            
                             let c_offset = cont_idx.to_be_bytes();
                             let _type_check : [Offset; 2] = [v_offset, c_offset];
                             
                             context.data_file.write(&[tag as u8, b' '])?;
                             context.data_file.write(&offset_to_hex( v_offset ))?;
                             context.data_file.write(&offset_to_hex( c_offset ))?;
                             context.data_file.write(&[b'\n'])?;

                             context.values.insert(hash, cur_idx);
                             context.count += INCR;
                             
                             let new_pos = context.data_file.stream_position()?;
                             context.value_offsets.push(new_pos);
                             Ok((hash, cur_idx))
                           }
        }
      };


  let acc_out = match cata_case {
    CataCase::Mapf(map_f)           => { let MapF { origin_path, value } = map_f;
                                         let nil      = register(ctx, CataCase::AlgF(AlgF { origin_path, child_mask: &[0;4], accs: &mut [] }), serialize_value)?.hash_idx;
                                         
                                         let mut tmp = Vec::new();
                                         core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                         serialize_value(value, &mut tmp);
                                         
                                         let v        = serialize_with_rollback( ctx, Tag::Value,
                                                                                 &mut tmp.drain(..),
                                                                                 SerializationStyle::HexBytes
                                                                               )?;
                                         let hash_idx = write_node(ctx, Tag::ValueNode, v, nil)?;
                                         
                                         tmp.clear();                   
                                         core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                         
                                         Accumulator {
                                             hash_idx,
                                             max_len     : origin_path.len(),
                                             val_count   : 1,
                                             paths_count : 1,
                                         }
                                       }
    CataCase::CollapseF(collapse_f) => { let CollapseF { value, acc, .. } = collapse_f;
                                         
                                         let mut tmp = Vec::new();
                                         core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                         serialize_value(value, &mut tmp);
                                         
                                         let v = serialize_with_rollback( ctx,
                                                                          Tag::Value,
                                                                          &mut tmp.drain(..),
                                                                          SerializationStyle::HexBytes
                                                                        )?;

                                         tmp.clear();                   
                                         core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                         
                                         let cont = acc?;
                                         let hash_idx = write_node(ctx, Tag::ValueNode, v, cont.hash_idx)?;
                                         
                                         
                                         Accumulator {
                                           hash_idx,
                                           val_count : cont.val_count+1, 
                                           .. cont
                                         }
                                       }
    CataCase::AlgF(alg_f)           => { let AlgF { child_mask, accs, origin_path } = alg_f;
                                         
                                         
                                         // compute the hash : seed(0) -> forall branchhash . write_u128(branch hash)
                                         
                                         // reset the scratch buffer
                                         ctx.algf_scratch.len = 0;
                                         
                                         let mut acc = Accumulator {
                                            hash_idx: (gxhash::GxHasher::with_seed(0).finish_u128(), ctx.count),
                                            max_len: origin_path.len(),
                                            val_count: 0,
                                            paths_count: 0,
                                        };


                                         let mut hasher = gxhash::GxHasher::with_seed(0);
                                         
                                         for each in accs {
                                           let Accumulator { hash_idx, max_len, val_count, paths_count } = core::mem::replace(each, Ok(Accumulator::zeroed()))?;
                                         
                                           hasher.write_u128(hash_idx.0);
                                          //  let [ _, _, offset @ .. ] = acc.hash_idx.1.to_be_bytes();
                                           let offset = hash_idx.1.to_be_bytes();
                                           let _type_check : Offset = offset;
                                           
                                           ctx.algf_scratch.buffer[ctx.algf_scratch.len] = offset_to_hex(offset);
                                           
                                           acc.max_len      = acc.max_len.max(max_len);
                                           acc.val_count   += val_count;
                                           acc.paths_count += paths_count;
                                           
                                           ctx.algf_scratch.len+=1;
                                         }
                                         let branches_hash = hasher.finish_u128();
                                         // we now have all needed hashes
                                       
                                         // find correct offset
                                         let branches_idx =
                                             if let Some(&offset) = ctx.values.get(&branches_hash) {
                                                offset
                                             } else {
                                               // it does not exist we write it to the file
                                               let Ctx { count, values, value_offsets, data_file, algf_scratch, .. } = ctx;
                                               
                                               let cur_idx = *count;
                                               data_file.write(&[Tag::Branches as u8, b' '])?;
                                               data_file.write_all(algf_scratch.buffer[0..algf_scratch.len].as_flattened())?;
                                               data_file.write(&[b'\n'])?;
                                               
                                               let new_pos = data_file.stream_position()?;
                                              //  dbg!(new_pos);
                                               value_offsets.push(new_pos);
                                               

                                               values.insert(branches_hash, cur_idx);
                                               *count += INCR;
                                               
                                               cur_idx
                                             };
                                       
                                       
                                         let branches_hash_idx = (branches_hash, branches_idx);
                                       
                                         
                                         let child_mask_hash_idx = serialize_with_rollback( ctx,
                                                                                            Tag::ChildMask,
                                                                                            &mut child_mask.map(|word| word.reverse_bits().to_be_bytes()).as_flattened().into_iter().copied(),
                                                                                            SerializationStyle::HexBytes
                                                                                          )?;

                                         let hash_idx = write_node(ctx, Tag::BranchNode, child_mask_hash_idx, branches_hash_idx)?;
                                         Accumulator {
                                           hash_idx,
                                           .. acc
                                         }
                                       }
    CataCase::JumpF(jump_f)         => { let JumpF { sub_path, acc, .. } = jump_f;
                                        //  currently, it does not appear to be conditional
                                         core::debug_assert!(!sub_path.is_empty());
                                         let p = serialize_with_rollback( ctx,
                                                                          Tag::Path,
                                                                          &mut sub_path.into_iter().copied(),
                                                                          SerializationStyle::HexBytes,
                                                                        )?;
                                         let cont = acc?;
                                         let hash_idx = write_node(ctx, Tag::PathNode, p, cont.hash_idx)?;
                                         Accumulator {
                                           hash_idx, 
                                           val_count: cont.val_count+1,
                                           .. cont
                                         }
                                       }
  };

  Ok(acc_out)
}

pub struct ZeroCompressedFile {
  pub data : std::fs::File,
  pub path : PathBuf,
}
fn offset_and_childmask_zero_compressor(f : &std::fs::File, out_dir_path: impl AsRef<std::path::Path>) -> Result<ZeroCompressedFile, std::io::Error> {

  let mut path = out_dir_path.as_ref().to_path_buf();
  path.push("zero_compressed_hex.data");
  let mut out_file = std::fs::File::create(&path)?;
  let mut out = BufWriter::new(out_file);


  let reader = BufReader::new(f);
  let mut bytes = reader.bytes();
  
  // get past header
  while let Some(byte) = bytes.next() {
    let x = byte?;
    out.write(&[x])?;
    if x == b'\n' {break}
  }


  let write_zeroes = |z : &mut _, file : &mut BufWriter<_>, boundary : bool| -> Result<(), std::io::Error>{
    let dummy = [b'0'; 4];
    let mut n = *z;
    *z = 0;
    match n {
      0..=3 => { 
        file.write(&dummy[0..n])?; 
      }
      4..=64 => { 
                  if !boundary {
                    n -= 1;
                  }
                  let hex = byte_to_hex((n) as u8);
                  file.write(&[b'/', hex[0], hex[1],])?;
                  if !boundary {
                    file.write(&[b'0'])?;
                  }
                },
      _       => core::unreachable!("This case should only arise"),
    }
    Ok(())
  };
  
  let mut byte_boundary = true;

  let zeroes = &mut 0;
  let mut skip = false;
  let mut hit_x = false;
  while let Some(each) = bytes.next() {
    byte_boundary = !byte_boundary;
    let ascii = each?;
    core::debug_assert!(ascii.is_ascii_alphanumeric() || ascii.is_ascii_whitespace());
    match ascii {
      b'v' 
    | b'p'  => { skip = true;
                 out.write(&[ascii])?;
               },
      b'\n' => {
                 skip = false;
                 if *zeroes > 0 {
                   write_zeroes(zeroes, &mut out, byte_boundary)?;
                 }
                 if hit_x {
                  out.write(&[b'0'])?;
                 }
                 byte_boundary = false;
                 out.write(b"\n")?;
               }
      b'0'  => {
                 if hit_x {
                   debug_assert!(*zeroes == 0);
                   continue;
                 }
                 if skip {
                   core::debug_assert!(*zeroes == 0);
                   out.write(b"0")?;
                 } else if !byte_boundary && *zeroes == 0 {
                   out.write(b"0")?;
                 } else {
                   *zeroes += 1;
                 }
                 
               }
      _     => {
                 if let b'x' = ascii {
                   byte_boundary = false
                 }
                 if *zeroes > 0 {
                   write_zeroes(zeroes, &mut out, byte_boundary)?;
                 }
                 hit_x = ascii == b'x';
                 out.write(&[ascii])?;
               }
    };
  }
  Ok(
    ZeroCompressedFile { 
      data: out.into_inner().unwrap(),
      path: path }
  )
}

fn dbg_hex_line_numbers(f : &std::fs::File, path : impl AsRef<std::path::Path>)->Result<std::fs::File, std::io::Error> {
  let mut line_number : u64 = 0;
  let read_buffer = BufReader::new(f);

  let mut path : PathBuf = path.as_ref().to_path_buf();
  path.push("line_number.dbg");

  let out_file = std::fs::File::create(&path)?;
  let mut out : BufWriter<std::fs::File> = BufWriter::new(out_file);


  let leading_offset =
      | line : u64 | 
      {
        let mut keep = false;
        let h = offset_to_hex(line.to_be_bytes());
        let last = h[HEX_OFFSET_LEN-1];
        let mut out = h.map(|b| {
          match b {
              b'x' => b'x',
              b'0' => if keep { b'0'} else {b'_'},
              _    => { keep = true; 
                        b
                      }
          }
        });
        out[HEX_OFFSET_LEN-1] = last;
        out
      };

  out.write(b"|   hex index   |")?;
  out.write(b" ")?;


  for b in read_buffer.bytes() {
    let c = b?;
    out.write(&[c])?;
    if let b'\n' = c {
      out.write(&leading_offset(line_number))?;
      out.write(b" ")?;
      line_number += INCR as u64;
    }
  }

  Ok(out.into_inner().unwrap())
}







fn deserialize_file<V : ZipperValue>(file_path : impl AsRef<std::path::Path>, de : impl Fn(&[u8])->V)-> Result<BytesTrieMap<V>, std::io::Error> {
  let f = std::fs::File::open(file_path.as_ref())?;
  let mut reader = BufReader::new(f);

  let mut line = String::with_capacity(4096);

  // strip header
  reader.read_line(&mut line)?;
  line.clear();

  let buffer = Vec::with_capacity(4096);

  let mut acc = BytesTrieMap::new();
  while let Ok(length) = reader.read_line(&mut line) {
    let [bytes @ .. , b'\n'] = line.as_bytes() else {break};
    let [ t @ &( Tag::PATH 
               | Tag::VALUE 
               | Tag::CHILD_MASK 
               | Tag::BRANCHES 
               | Tag::PATH_NODE 
               | Tag::VALUE_NODE 
               | Tag::BRANCH_NODE
               ),
          b' ',data @ ..] = bytes else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected `<tag byte><space>`")); };

          
    todo!("make iterator for uncompressing offsets that are b'x' separated"); // use the same thing for child mask?


    match t {
      // these tags currently have no compression
      Tag::PATH         => {}
      Tag::VALUE        => {}

      // child mask has compression but no b'x' bytes
      Tag::CHILD_MASK   => {}

      // the rest have ofset compression with b'x' bytes
      Tag::BRANCHES     => {}
      Tag::PATH_NODE    => {}
      Tag::VALUE_NODE   => {}
      Tag::BRANCH_NODE  => {}

      _ => core::unreachable!()
    }


    println!("{:?}", std::str::from_utf8(data));
    


    line.clear();
  }


  Ok(acc)

  
}

// // clears the buffer before decompressing
// fn decompress_zeros_compression(mut encoded_hex : &[u8], buffer : &mut Vec<u8>) {
//   buffer.clear();

//   loop {
//     match encoded_hex {
//       [b'x', rest @ .. ] => {}
//       [b'/', top, bot, .. ] => {}

//     }
//   }

// }

























#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn trivial() {
    const LEN : usize = 0x_100;
    #[allow(long_running_const_eval)]
    const ARR : [u8; LEN]= {
      let mut arr = [0_u8 ; LEN];
      let mut i = 0;
      while i != LEN {
        arr[i] = i as u8;
        i += 1;
      }
      arr
    };

    let mut trie = BytesTrieMap::new();

    let as_arc = |bs : &[u8]| alloc::sync::Arc::<[u8]>::from(bs);

    trie.insert(b"desf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"desF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"desG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"desH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"desI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"desJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"desK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"desM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"abesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"abesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"abesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"abesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"abesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"abesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"abesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"abesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"abcd", as_arc(b"xyz"));
    trie.insert(b"abce", as_arc(b"xyz"));
    trie.insert(b"abcf", as_arc(b"xyz"));
    trie.insert(b"abcg", as_arc(b"xyz"));
    trie.insert(b"agbcd", as_arc(b"xyz"));
    trie.insert(b"agbce", as_arc(b"xyz"));
    trie.insert(b"agbcf", as_arc(b"xyz"));
    trie.insert(b"agbcg", as_arc(b"xyz"));


    // #[cfg(not(debug_assertions))]
    for l in 0..LEN {
      trie.insert(&ARR[..l], as_arc(&ARR[..l]));
    }
    for l in 0..LEN {
      trie.insert(&ARR[l..], as_arc(&ARR[..l]));
    }


    let path = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(".tmp");

    let serialized =  write_trie(
      format!("(file : \"{}\", module : \"{}\", line : \"{}\")", file!(), module_path!(), line!()),
      trie.clone(),
      |bs, v|{ v.extend_from_slice(bs); }, &path
    ).unwrap();
    
    let read = std::fs::File::open(serialized.data_path).unwrap();
    let compressed = offset_and_childmask_zero_compressor(&read, &path).unwrap();

    let read = std::fs::File::open(compressed.path).unwrap();
    let dbg = dbg_hex_line_numbers(&read, &path).unwrap();

    let de_path = path.join("zero_compresed_hex.data");
    let de = deserialize_file(&de_path, |b|as_arc(b)).unwrap();



  }
}




// flate2