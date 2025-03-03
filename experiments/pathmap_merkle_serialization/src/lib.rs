#![allow(unused)]
#![cfg_attr(rustfmt, rustfmt::skip)]


macro_rules! hex { () => { b'A'..=b'F' | b'0'..=b'9'}; }

use std::{any::type_name, cell::RefCell, collections::VecDeque, hash::Hasher, io::{BufRead, BufReader, BufWriter, IoSliceMut, Read, Seek, Write}, path::PathBuf};


use pathmap::{morphisms::Catamorphism, trie_map::BytesTrieMap, zipper::{Zipper, ZipperMoving, ZipperWriting}};
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
  serialize_value : impl for<'read, 'encode> Fn(&'read V, &'encode mut Vec<u8>)->ValueSlice<'read, 'encode>,
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
    data_file         : BufWriter::new(data_file),
    algf_scratch      : AlgFScratch::zeroed(),
    serialize_scratch : Vec::with_capacity(4096),
    compression_scratch : Vec::with_capacity(4096),

    lost_bytes_pool   : Vec::new(), 
  });

  // // how to keep the root val?
  let (trie, strip)  = if trie.get(&[]).is_some() {
    let mut input = BytesTrieMap::new();
    let mut wz = input.write_zipper();
    wz.descend_to_byte(0);
    wz.graft_map(trie);
    drop(wz);
    (input, true)
  } else {
    (trie, false)
  };

  // Threading the context is tedious, and error prone, so I've delagted to an outside function
  let Accumulator { hash_idx, mut max_len, val_count, paths_count, lost_bytes : _ } = trie.into_cata_jumping_side_effect::<Result<Accumulator, std::io::Error>, _,_,_,_>(
    |     value,       origin_path| register(&mut ctx.borrow_mut(), CataCase::Mapf     (MapF      { origin_path,      value       }), &serialize_value),
    |     value,  acc, origin_path| register(&mut ctx.borrow_mut(), CataCase::CollapseF(CollapseF { origin_path,      value, acc  }), &serialize_value),
    |child_mask, accs, origin_path| register(&mut ctx.borrow_mut(), CataCase::AlgF     (AlgF      { origin_path, child_mask, accs }), &serialize_value),
    |  sub_path,  acc, origin_path| register(&mut ctx.borrow_mut(), CataCase::JumpF    (JumpF     { origin_path,   sub_path, acc  }), &serialize_value),
  )?;

  let Ctx { values, value_offsets, mut data_file, .. } = ctx.into_inner();

  data_file.flush();

  

  let pos = data_file.stream_position()?;
  let data_file = data_file.into_inner()?;

  if strip {

    max_len -= 1;


    const TAG_SPACE      : u64 = 2;
    const NL             : u64 = 1;
    const CHILD_MASK_HEX : u64 = 0x40;
  
    data_file.set_len(
      pos 
    - ( (TAG_SPACE +   HEX_OFFSET_LEN as u64 + NL) 
      + (TAG_SPACE +   CHILD_MASK_HEX as u64 + NL) 
      + (TAG_SPACE + 2*HEX_OFFSET_LEN as u64 + NL)
      )
    )?;
  };


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
  count               : usize,
  values              : BTreeMap<u128, Index>,
  value_offsets       : Vec<FilePos>,
  data_file           : BufWriter<std::fs::File>,
  algf_scratch        : AlgFScratch,
  serialize_scratch   : Vec<u8>,
  compression_scratch : Vec<u8>,
  
  // the current version of cata loses info of the origin path because of the operational semantics of collapse
  lost_bytes_pool   : Vec<Vec<u8>>,
}

struct LostBytes { origin_trailing_byte : Option<u8>, jump_sub_slice : Vec<u8> , was_mapf : bool}


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

  // the current version of cata loses info of the origin path because of the operational semantics of collapse
  lost_bytes : LostBytes,
}
impl Accumulator {
  const fn zeroed() -> Self {  
    Accumulator { 
      hash_idx: (0,0),
      max_len: 0,
      val_count: 0,
      paths_count: 0,

      lost_bytes : LostBytes { origin_trailing_byte: None, jump_sub_slice: Vec::new(), was_mapf : false },
    }}
}

fn hex_pair_to_byte(pair : [u8;2])->u8{
  core::debug_assert!(matches!(pair, [hex!(),hex!()]));

  let [top,bot] = pair.map(|h|
    match h {
      b'0'..=b'9' => h - b'0',
      b'A'..=b'F' => h - b'A' + 10,
      _ => panic!("found {h}, as char '{}'", h as char)
    }
  );
  (top << 4) | bot
}

fn byte_to_hex(b : u8) -> [u8;2] {
  let top = b >> 4;
  let bot = b & 0x_f;
  let unchecked_to_hex = |b : u8| {
    match b {
      0..=9   => b + b'0',
      10..=16 => b + b'A' - 10 ,
      _ => panic!("found {b}, as char '{}'", b as char)
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

type FilePos = u64;


pub enum ValueSlice<'read, 'encode> {
  // if a value can transparently reveal a slice of bytes that represents enough data to serialize the data this variant can be used
  Read(&'read [u8]),
  /// if the value cannot be trivially read as bytes, one can encode it into the mutable buffer
  Encode(&'encode mut Vec<u8>),
}

/// this constant exists purely for debugging compression of zeros
#[cfg(not(debug_assertions))]
const INCR : usize = 0x_1;
#[cfg(debug_assertions)]
const INCR : usize = 0x_1;
// const INCR : usize = 0x_100000;

fn register<V>(
  ctx             : &mut Ctx,
  cata_case       : CataCase<'_, V, Result<Accumulator, std::io::Error>>,
  serialize_value : &impl for< 'read, 'encode> Fn(&'read V, &'encode mut Vec<u8>)->ValueSlice<'read, 'encode>,
) -> Result<Accumulator, std::io::Error>
{
  let rollback_or_advance = |context : &mut Ctx, hash : u128, rollback_pos : FilePos | -> Result<(u128, Index), std::io::Error> 
      {

        Ok(
          if let Some(&offset) = context.values.get(&hash) {
            // rollback and use lookup value

            
            let cur_pos = context.data_file.stream_position()?;
            context.data_file.seek_relative(rollback_pos as i64 - cur_pos as i64)?;
            (hash, offset)
          } else {
            // advance

            let idx = context.count;
            context.values.insert(hash, idx);
            context.count += INCR;

            context.value_offsets.push(context.data_file.stream_position()?);
            (hash, idx)
          }
        )
      };

  let serialize_with_rollback = |context : &mut Ctx, tag : Tag, i : &mut dyn Iterator<Item = u8>| -> Result<(u128, Index), std::io::Error>
      {
        let rollback_pos = *context.value_offsets.last().unwrap();
        let mut hasher = GxHasher::with_seed(0);


        hasher.write_u8(tag as u8);
        context.data_file.write(&[tag as u8, b' '])?;
        for b in i {

          

          hasher.write_u8(b);
          // context.data_file.write(
          // )?;
          context.data_file.write( &byte_to_hex(b) )?;
          
        }
        let hash = hasher.finish_u128();
        context.data_file.write(&[b'\n'])?;

        rollback_or_advance(context, hash, rollback_pos)
      };

  // Val ::=                     Tag,               SeIdx,             SeIdx
  // Val === seed(0) -> write_u8(Tag) -> write_u128(Hash) -> write_u128(Hash)
  let write_node = |context : &mut Ctx, tag : Tag,(value_hash, value_idx) : (u128, Index), (cont_hash, cont_idx) : (u128, Index)| -> Result<(u128, Index), std::io::Error>
      {
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

  let maybe_make_path_node = | ctx : &mut Ctx, sub_path : &[u8], cont_hash_idx : (u128, usize)  | -> Result<(u128, usize), std::io::Error>
      {
        if sub_path.is_empty() {
          // don't make a new node
          return Ok(cont_hash_idx);
        }
        let p = serialize_with_rollback( ctx,
                                         Tag::Path,
                                         &mut sub_path.into_iter().copied(),
                                       )?;
        write_node(ctx, Tag::PathNode, p, cont_hash_idx)
      };

  let acc_out = match cata_case {
    CataCase::Mapf(map_f)           => { let MapF { origin_path, value } = map_f;

                                         let nil      = register(ctx, CataCase::AlgF(AlgF { origin_path : &[], child_mask: &[0;4], accs: &mut [] }), serialize_value)?.hash_idx;
                                         
                                         let value = {

                                           let mut tmp = Vec::new();
                                           core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                           
                                           let slice = serialize_value(value, &mut tmp);
                                           let slice = match slice {
                                                                      ValueSlice::Encode(items) => { &*items},
                                                                      ValueSlice::Read(items) => items,
                                                                    };
                                           let v        = serialize_with_rollback( ctx, Tag::Value,
                                                                                    &mut slice.into_iter().copied(),
                                                                                  )?;
                                           
                                           tmp.clear();                   
                                           core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                          
                                           v
                                         };

                                         let hash_idx = write_node(ctx, Tag::ValueNode, value, nil)?;
                                         
                                         let lost_bytes = {
                                           let mut jump_sub_slice = ctx.lost_bytes_pool.pop().unwrap_or(Vec::new());
                                           jump_sub_slice.clear();

                                           LostBytes {
                                             origin_trailing_byte : origin_path.last().copied(),
                                             jump_sub_slice,
                                             was_mapf : true
                                           }
                                         };

                                         Accumulator {
                                             hash_idx,
                                             max_len     : origin_path.len(),
                                             val_count   : 1,
                                             paths_count : 1,
                                             lost_bytes
                                         }
                                       }
    CataCase::CollapseF(collapse_f) => { let CollapseF { value, acc, origin_path } = collapse_f;


                                         
                                         let value = {

                                           let mut tmp = Vec::new();
                                           core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                           
                                           let slice = serialize_value(value, &mut tmp);
                                           let slice = match slice {
                                                                      ValueSlice::Encode(items) => { &*items},
                                                                      ValueSlice::Read(items) => items,
                                                                    };
                                           let v        = serialize_with_rollback( ctx, Tag::Value,
                                                                                    &mut slice.into_iter().copied(),
                                                                                  )?;
                                           
                                           tmp.clear();                   
                                           core::mem::swap(&mut ctx.serialize_scratch, &mut tmp);
                                          
                                           v
                                         };


                                         let mut cont = acc?;
                                         '_deal_with_lost_bytes : {
                                           let mut lost_bytes = core::mem::replace( &mut cont.lost_bytes, 
                                                                                    LostBytes { origin_trailing_byte: None, 
                                                                                                jump_sub_slice: Vec::new(),
                                                                                                was_mapf : false
                                                                                              }
                                                                                  );

                                           let LostBytes { mut origin_trailing_byte, mut jump_sub_slice, was_mapf } = lost_bytes;
                                           origin_trailing_byte = origin_trailing_byte.and_then(|b| {
                                                                    jump_sub_slice.insert(0, b); 
                                                                    origin_path.last().copied()
                                                                  } );
                                           cont.hash_idx = maybe_make_path_node(ctx, &jump_sub_slice, cont.hash_idx)?;                                            
                                           
                                           jump_sub_slice.clear();

                                           cont.lost_bytes = LostBytes { origin_trailing_byte, jump_sub_slice , was_mapf : false};
                                         };
                                         
                                         let hash_idx = write_node(ctx, Tag::ValueNode, value, cont.hash_idx)?;
                                         

                                         
                                         Accumulator {
                                           hash_idx,
                                           val_count  : cont.val_count+1,
                                           .. cont
                                         }
                                       }
    CataCase::AlgF(alg_f)           => { let AlgF { child_mask, accs, origin_path } = alg_f;
                                        //  let non_branch_root = if let ([acc], []) = acc, origin_path { true
                                        //  } else {false};


                                         // compute the hash : seed(0) -> forall branchhash . write_u128(branch hash)
                                         
                                         // reset the scratch buffer
                                         ctx.algf_scratch.len = 0;
                                         
                                         let mut jump_sub_slice = ctx.lost_bytes_pool.pop().unwrap_or(Vec::new());
                                         jump_sub_slice.clear();
                                         let mut acc = Accumulator {
                                            hash_idx: (gxhash::GxHasher::with_seed(0).finish_u128(), ctx.count),
                                            max_len: origin_path.len(),
                                            val_count: 0,
                                            paths_count: 0,
                                            lost_bytes: LostBytes { origin_trailing_byte : None, jump_sub_slice, was_mapf : false },
                                        };


                                         let mut hasher = gxhash::GxHasher::with_seed(0);
                                         
                                         for each in accs {
                                           let Accumulator { mut hash_idx, max_len, val_count, paths_count, mut lost_bytes } = core::mem::replace(each, Ok(Accumulator::zeroed()))?;

                                           '_deal_with_lost_bytes : {

                                             hash_idx = maybe_make_path_node(ctx, &lost_bytes.jump_sub_slice, hash_idx)?;
                                             ctx.lost_bytes_pool.push(lost_bytes.jump_sub_slice);
                                           };
                                         
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

                                               value_offsets.push(new_pos);
                                               

                                               values.insert(branches_hash, cur_idx);
                                               *count += INCR;
                                               
                                               cur_idx
                                             };
                                       
                                       
                                         let branches_hash_idx = (branches_hash, branches_idx);
                                       
                                         
                                         let child_mask_hash_idx = serialize_with_rollback( ctx,
                                                                                            Tag::ChildMask,
                                                                                            &mut child_mask.map(|word| word.reverse_bits().to_be_bytes()).as_flattened().into_iter().copied(),
                                                                                          )?;

                                         let hash_idx = write_node(ctx, Tag::BranchNode, child_mask_hash_idx, branches_hash_idx)?;
                                         Accumulator {
                                           hash_idx,
                                           .. acc
                                         }
                                       }
    CataCase::JumpF(jump_f)         => { let JumpF { origin_path, sub_path, acc, .. } = jump_f;

                                         core::debug_assert!(!sub_path.is_empty());

                                         let mut cont = acc?;

                                         cont.lost_bytes = {
                                           let LostBytes { origin_trailing_byte, mut jump_sub_slice, was_mapf } = cont.lost_bytes;

                                            if !jump_sub_slice.is_empty() { core::unreachable!() }
                                                                        
                                            jump_sub_slice.extend_from_slice(sub_path);
                                            origin_trailing_byte.map( |b| if !was_mapf {jump_sub_slice.push(b)} );
                                            
                                            
                                            LostBytes {
                                              origin_trailing_byte: origin_path.last().copied(),
                                              jump_sub_slice,
                                              was_mapf: false
                                            }
                                         };
                                         
                                         Accumulator {
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
                 if *zeroes > 0 && !hit_x {
                   write_zeroes(zeroes, &mut out, byte_boundary)?;
                 }
                 if hit_x {
                   // only happens once for "nil"
                   out.write(b"00")?;
                 }
                 hit_x = false;
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
                   hit_x = false;
                 } else {
                   *zeroes += 1;
                 }
                 
               }
      b'x'  => { 
                 if *zeroes > 0 {
                   core::debug_assert!(!hit_x);
                   write_zeroes(zeroes, &mut out, byte_boundary)?;
                 }
                if hit_x {panic!()}
                 out.write(b"x")?;
                 byte_boundary = false;
                 hit_x = true;
                 *zeroes = 0;
                 
               }
      _     => {
                 if *zeroes > 0 {
                   core::debug_assert!(!hit_x);
                   write_zeroes(zeroes, &mut out, byte_boundary)?;
                 }
                 if hit_x && !byte_boundary {
                   out.write(b"0")?;
                 }
                 
                 out.write(&[ascii])?;
                 hit_x = false
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

  // ~ 1 gigabyte virtual allocation to start
  let mut paths_buffer = Vec::with_capacity(2_usize.pow(30));
  let mut branches_buffer = Vec::with_capacity(2_usize.pow(30)/U64_BYTES);
  
  // we pay the price of looking at a tag, but it should pay off as we get constant lookup
  enum Deserialized<V> {
    Path(std::ops::Range<usize>),
    Value(V),
    ChildMask(ChildMask),
    Branches(std::ops::Range<usize>),
    Node(BytesTrieMap<V>),
  }

  impl<V : ZipperValue> core::fmt::Debug for Deserialized<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      match self {
        Deserialized::Path(range)           => write!(f,"Path({}..{})", range.start, range.end),
        Deserialized::Value(bytes_trie_map) => write!(f,"Value"),
        Deserialized::ChildMask(mask)       => {
                                                  let s = mask.into_iter().flat_map(|n|format!("{:.>64b} ",n.reverse_bits()).chars().collect::<Vec<_>>()).collect::<String>();
                                                  write!(f,"ChildMask({:?})",s)
                                               },
        Deserialized::Branches(range)       => write!(f,"Branches({}..{})", range.start, range.end),
        Deserialized::Node(bytes_trie_map)  => write!(f,"Node(empty?{})",bytes_trie_map.is_empty()),
      }
    }
  }

  let mut deserialized = Vec::with_capacity(4096);
  let mut val_scratch = Vec::with_capacity(4096);

  while let Ok(length) = reader.read_line(&mut line) {
    let [bytes @ .. , b'\n'] = line.as_bytes() else {break};
    let [  t @ ( Tag::PATH 
               | Tag::VALUE 
               | Tag::CHILD_MASK 
               | Tag::BRANCHES
               | Tag::PATH_NODE
               | Tag::VALUE_NODE
               | Tag::BRANCH_NODE
               ),
          b' ',data @ ..] = bytes else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected `<tag byte><space>`")); };

          

    
  // println!("0x{:_>16x} {} {:?}\n{:#?}", deserialized.len(), *t as char, std::str::from_utf8(data), deserialized);
  println!("0x{:_>16x} {} {:?}", deserialized.len(), *t as char, std::str::from_utf8(data));



    match *t {
      // paths currently have no compression yet
      Tag::PATH         => { 
                             let start = paths_buffer.len();
                             
                             let mut cur = data;
                             loop {
                               match cur {
                                []                   => break,
                                [top,bot, rest @ ..] => {
                                                          let b = hex_pair_to_byte([*top,*bot]);
                                                          paths_buffer.push(b);
                                                          cur = rest
                                                        }
                                _                    => return Err(std::io::Error::other("Malformed serialized ByteTrie, expected path as `(<hex_top><Hex_bot>)*`"))
                               }
                             }
                             
                             let end = paths_buffer.len();


                             deserialized.push(Deserialized::Path(start..end));
                           }
      // values currently have no compression yet
      Tag::VALUE        => { 
                             val_scratch.clear();

                             let mut cur = data;

                             loop {
                               match cur {
                                []                   => break,
                                [top,bot, rest @ ..] => {
                                                          let b = hex_pair_to_byte([*top,*bot]);
                                                          val_scratch.push(b);
                                                          cur = rest
                                                        }
                                _                    => { 
                                                          return Err(std::io::Error::other("Malformed serialized ByteTrie, expected value as `(<hex_top><Hex_bot>)*`"))
                                                        }
                               }
                             }
                            
                             let mut value = de(&val_scratch);

                             val_scratch.clear();
                            
                             deserialized.push(Deserialized::Value(value));
                           }

      // child mask has compression but no b'x' bytes
      Tag::CHILD_MASK   => { 
                             let mut mask_buf = decompress_zeros_compression_child_mask(data)?;
                             let mask = mask_buf.map(u64::from_be_bytes).map(u64::reverse_bits);

                            deserialized.push(Deserialized::ChildMask(mask));
                           }

      // the rest have ofset compression with b'x' bytes
      Tag::BRANCHES     => { 
                             let mut children_buf = [0_u64 ; 256];
                             let mut x_count      = decompress_zeros_compression_offset(data, &mut children_buf)?;

                            let start = branches_buffer.len();
                            branches_buffer.extend_from_slice(&children_buf[0..x_count]);
                            let end   = branches_buffer.len();

                            deserialized.push(Deserialized::Branches(start..end));

                           }
      Tag::PATH_NODE    => { let mut node_buf     = [0_u64 ; 2];
                             decompress_zeros_compression_offset(data, &mut node_buf)?;
                             
                             let [path_idx, node_idx] = node_buf.map(|x| x as usize);
                             
                             let Deserialized::Path(path) = &deserialized[path_idx] else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected path")); };
                             let Deserialized::Node(node) = &deserialized[node_idx] else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected node")); };

                             let mut path_node = BytesTrieMap::new();
                             
                             let mut wz        = path_node.write_zipper();
                             wz.descend_to(&paths_buffer[path.start..path.end]);
                             wz.graft(&node.read_zipper());
                             drop(wz);

                             core::debug_assert!(!path_node.is_empty());

                             deserialized.push(Deserialized::Node(path_node));

                           }
      Tag::VALUE_NODE   => { let mut node_buf     = [0_u64 ; 2];

                             decompress_zeros_compression_offset(data, &mut node_buf)?;

                             let [val_idx, node_idx] = node_buf.map(|x| x as usize);

                             let Deserialized::Value(value) = &deserialized[val_idx]  else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected value")); };
                             let Deserialized::Node(node)   = &deserialized[node_idx] else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected node")); };

                             
                             let mut value_node = node.clone();
                             value_node.insert(&[], value.clone());
                  
                             deserialized.push(Deserialized::Node(value_node));
                           } 
                           
      Tag::BRANCH_NODE  => { let mut node_buf     = [0_u64 ; 2];
                             decompress_zeros_compression_offset(data, &mut node_buf)?;

                             let [mask_idx, branches_idx] = node_buf.map(|x| x as usize);
                             
                             let Deserialized::ChildMask(mask) = &deserialized[mask_idx] else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected childmask as `(/?<hex_top><Hex_bot>)*`")); };
                             let iter = pathmap::utils::ByteMaskIter::new(*mask);

                             let Deserialized::Branches(r) = &deserialized[branches_idx] else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected branches")); };
                             let branches = &branches_buffer[r.start..r.end];
                             
                             core::debug_assert_eq!(mask.into_iter().copied().map(u64::count_ones).sum::<u32>() as usize, branches.len());

                             let mut branch_node = BytesTrieMap::new();
                             let mut wz = branch_node.write_zipper();

                             for (byte, &idx) in iter.into_iter().zip(branches) {
                               let Deserialized::Node(node) = &deserialized[idx as usize] else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected node")); };
                               
                               core::debug_assert!(!node.is_empty());

                               wz.descend_to_byte(byte);
                               wz.graft(&node.read_zipper());
                               wz.ascend_byte();
                             }

                             drop(wz);


                             deserialized.push(Deserialized::Node(branch_node));
                           }

      _ => core::unreachable!()
    }


    


    line.clear();
  }

  let Some(Deserialized::Node(n)) = deserialized.pop() else { return Err(std::io::Error::other("Malformed serialized ByteTrie, expected root node")); };

  Ok(n)
}


// clears the buffer before decompressing
fn decompress_zeros_compression_offset(mut encoded_hex : &[u8], buffer : &mut [u64])->Result<usize, std::io::Error> {

  for each in buffer.iter_mut() {
    *each = 0;
  }

  const U64_BYTES : usize = u64::BITS as usize /8;

  let mut bytes = 0;
  let mut count = 0;
  let mut x = false;

  loop {
    match encoded_hex {
      []                                             => { 
                                                          if x { count +=1; }
                                                          break
                                                        }
      [b'x',                             rest @ .. ] => {
                                                          if x { count += 1; }
                                                          x = true;
                                                          encoded_hex = rest;
                                                        }
      [b'/', top @ hex!(), bot @ hex!(), rest @ .. ] => { let hex_zeros = hex_pair_to_byte([*top,*bot]);
                                                          
                                                         
                                                          // whole bytes
                                                          let mut zeroes = hex_zeros/2;
                                                          
                                                          debug_assert!(zeroes <= 6 );
                                                          buffer[count] <<= zeroes * u8::BITS as u8;

                                                          encoded_hex = rest;
                                                        }
      [      top @ hex!(), bot @ hex!(), rest @ .. ] => { let b = hex_pair_to_byte([*top,*bot]);

                                                          buffer[count] <<= u8::BITS;
                                                          buffer[count] |= b as u64;

                                                          encoded_hex = rest;
                                                        }
      _                                              => { return Err(std::io::Error::other("Malformed serialized ByteTrie")); }

    }
  }

  #[cfg(debug_assertions)]
  if INCR != 1 {
    for each in buffer.iter_mut() {
      *each >>= INCR.trailing_zeros();
    }
  }

  Ok(count)
}







const U64_BYTES : usize = u64::BITS as usize /8;



fn decompress_zeros_compression_child_mask(mut encoded_hex : &[u8], )->Result<[[u8;U64_BYTES];4], std::io::Error> {
  let mut buffer = [[0_u8;U64_BYTES];4];

  
  

  let mut bytes = 0;
  let mut count = 0;

  loop {
    match encoded_hex {
      []                                             => { 
                                                          break
                                                        }
      [b'/', top @ hex!(), bot @ hex!(), rest @ .. ] => { let hex_zeros = hex_pair_to_byte([*top,*bot]);
                                                         
                                                          // whole bytes
                                                          let mut zeroes = hex_zeros/2;                                                        
                                                          
                                                          let total :usize = bytes + zeroes as usize + count * U64_BYTES;
                                                          (count,bytes) = (total / U64_BYTES, total % U64_BYTES);
                                                          encoded_hex = rest;
                                                        }
      [      top @ hex!(), bot @ hex!(), rest @ .. ] => { let b = hex_pair_to_byte([*top,*bot]);

                                                          buffer[count][bytes] = b;

                                                          bytes += 1;
                                                          count += bytes as usize / U64_BYTES;
                                                          bytes %= U64_BYTES;
                                                          
                                                          encoded_hex = rest;
                                                        }
      _                                              => { return Err(std::io::Error::other("Malformed serialized ByteTrie, childmask")); }

    }
  }
  Ok(buffer)
}














#[cfg(test)]
mod test {
  use std::sync::Arc;

use super::*;

  #[test]
  fn trivial() {
    const LEN : usize = 0x_80;
    // const LEN : usize = 0x_02;
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

    let mut trie = BytesTrieMap::<Arc<[u8]>>::new();

    let as_arc = |bs : &[u8]| alloc::sync::Arc::<[u8]>::from(bs);
    trie.insert(b"a", as_arc(b""));
    trie.insert(b"abc", as_arc(b""));
   
    trie.insert(b"ab", as_arc(b""));
    trie.insert(b"abcd", as_arc(b""));


    trie.insert(b"ab", as_arc(b""));
    trie.insert(b"abc", as_arc(b""));
    trie.insert(b"abd", as_arc(b""));



    trie.insert(b"", as_arc(b""));     // VALUE NOT PRESENT
    trie.insert(b"ab", as_arc(b""));
    trie.insert(b"abce", as_arc(b""));
    trie.insert(b"abcf", as_arc(b""));


    trie.insert(b"", as_arc(b""));
    trie.insert(b"a", as_arc(b""));   // 
    trie.insert(b"b", as_arc(b""));   // c<-c0
    trie.insert(b"axb", as_arc(b""));  // c1<-a
    trie.insert(b"axbxc", as_arc(b"")); // m
    trie.insert(b"axbxd", as_arc(b"")); // m
    trie.insert(b"axc", as_arc(b"")); // m
    trie.insert(b"axb", as_arc(b"")); // m
    trie.insert(b"axbf", as_arc(b"")); // m
    trie.insert(b"axbe", as_arc(b"")); // m
    trie.insert(b"axbexy", as_arc(b"")); // m
    trie.insert(b"axbexyb", as_arc(b"")); // m
    trie.insert(b"axbxxxxxxxxxxxxxxxxxxd", as_arc(b"")); // m
    trie.insert(b"axbxexz", as_arc(b"")); // m
    trie.insert(b"axbexyzccca", as_arc(b"")); // m
    trie.insert(b"axbexyz", as_arc(b"")); // m
    
    // // FAIL (does not catch the value)
    trie.insert(b"", as_arc(b"abc"));



    trie.insert(b"a", as_arc(b""));
    trie.insert(b"ab", as_arc(b""));
    trie.insert(b"b", as_arc(b""));


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


    trie.insert(b"dxxxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"dxxxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"dxxxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"dxxxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"dxxxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"dxxxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"dxxxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"dxxxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"axxxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"axxxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"axxxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"axxxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"axxxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"axxxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"axxxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"axxxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"axxxbcd", as_arc(b"xyz"));
    trie.insert(b"axxxbce", as_arc(b"xyz"));
    trie.insert(b"axxxbcf", as_arc(b"xyz"));
    trie.insert(b"axxxbcg", as_arc(b"xyz"));
    trie.insert(b"axxxgbcd", as_arc(b"xyz"));
    trie.insert(b"axxxgbce", as_arc(b"xyz"));
    trie.insert(b"axxxgbcf", as_arc(b"xyz"));
    trie.insert(b"axxxgbcg", as_arc(b"xyz"));


    trie.insert(b"123dzxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123dzxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123dzxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123dzxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123dzxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123dzxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123dzxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123dzxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123azxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123azxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123azxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123azxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"123azxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"123azxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"123azxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"123azxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"123azxbcd", as_arc(b"xyz"));
    trie.insert(b"123azxbce", as_arc(b"xyz"));
    trie.insert(b"123azxbcf", as_arc(b"xyz"));
    trie.insert(b"123azxbcg", as_arc(b"xyz"));
    trie.insert(b"123azxgbcd", as_arc(b"xyz"));
    trie.insert(b"123azxgbce", as_arc(b"xyz"));
    trie.insert(b"123azxgbcf", as_arc(b"xyz"));
    trie.insert(b"123azxgbcg", as_arc(b"xyz"));





    trie.insert(b"", as_arc(b""));     // VALUE NOT PRESENT
    trie.insert(b"ab", as_arc(b""));
    trie.insert(b"abce", as_arc(b""));
    trie.insert(b"abcf", as_arc(b""));


    trie.insert(b"", as_arc(b""));
    trie.insert(b"a", as_arc(b""));   // 
    trie.insert(b"b", as_arc(b""));   // c<-c0
    trie.insert(b"axb", as_arc(b""));  // c1<-a
    trie.insert(b"axbxc", as_arc(b"")); // m
    trie.insert(b"axbxd", as_arc(b"")); // m
    trie.insert(b"axc", as_arc(b"")); // m
    trie.insert(b"axb", as_arc(b"")); // m
    trie.insert(b"axbf", as_arc(b"")); // m
    trie.insert(b"axbe", as_arc(b"")); // m
    trie.insert(b"axbexy", as_arc(b"")); // m
    trie.insert(b"axbexyb", as_arc(b"")); // m
    trie.insert(b"axbxxxxxxxxxxxxxxxxxxd", as_arc(b"")); // m
    trie.insert(b"axbxexz", as_arc(b"")); // m
    trie.insert(b"axbexyzccca", as_arc(b"")); // m
    trie.insert(b"axbexyz", as_arc(b"")); // m
    
    trie.insert(b"a", as_arc(b""));
    trie.insert(b"ab", as_arc(b""));
    trie.insert(b"b", as_arc(b""));


    trie.insert(b"57desf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57desF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57desG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57desH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57desI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57desJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57desK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57desM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57abesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57abesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57abesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57abesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57abesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"57abesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"57abesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"57abesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"57abcd", as_arc(b"xyz"));
    trie.insert(b"57abce", as_arc(b"xyz"));
    trie.insert(b"57abcf", as_arc(b"xyz"));
    trie.insert(b"57abcg", as_arc(b"xyz"));
    trie.insert(b"57agbcd", as_arc(b"xyz"));
    trie.insert(b"57agbce", as_arc(b"xyz"));
    trie.insert(b"57agbcf", as_arc(b"xyz"));
    trie.insert(b"57agbcg", as_arc(b"xyz"));
    trie.insert(b"57dxxxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57dxxxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57dxxxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57dxxxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57dxxxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57dxxxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57dxxxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57dxxxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57axxxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57axxxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57axxxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57axxxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57axxxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"57axxxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"57axxxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"57axxxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"57axxxbcd", as_arc(b"xyz"));
    trie.insert(b"57axxxbce", as_arc(b"xyz"));
    trie.insert(b"57axxxbcf", as_arc(b"xyz"));
    trie.insert(b"57axxxbcg", as_arc(b"xyz"));
    trie.insert(b"57axxxgbcd", as_arc(b"xyz"));
    trie.insert(b"57axxxgbce", as_arc(b"xyz"));
    trie.insert(b"57axxxgbcf", as_arc(b"xyz"));
    trie.insert(b"57axxxgbcg", as_arc(b"xyz"));
    trie.insert(b"57123dzxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123dzxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123dzxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123dzxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123dzxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123dzxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123dzxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123dzxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123azxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123azxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123azxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123azxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57123azxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"57123azxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"57123azxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"57123azxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"57123azxbcd", as_arc(b"xyz"));
    trie.insert(b"57123azxbce", as_arc(b"xyz"));
    trie.insert(b"57123azxbcf", as_arc(b"xyz"));
    trie.insert(b"57123azxbcg", as_arc(b"xyz"));
    trie.insert(b"57123azxgbcd", as_arc(b"xyz"));
    trie.insert(b"57123azxgbce", as_arc(b"xyz"));
    trie.insert(b"57123azxgbcf", as_arc(b"xyz"));
    trie.insert(b"57123azxgbcg", as_arc(b"xyz"));




    trie.insert(b"fgsfdgsfdgfds57desf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57desF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57desG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57desH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57desI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57desJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57desK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57desM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57abesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57abesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57abesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57abesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57abesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57abesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57abesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57abesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57abcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57abce", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57abcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57abcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57agbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57agbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57agbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57agbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57dxxxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57axxxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57axxxbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57axxxbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57axxxbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57axxxbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57axxxgbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57axxxgbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57axxxgbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57axxxgbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123dzxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57123azxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdgsfdgfds57123azxbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123azxbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123azxbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123azxbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123azxgbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123azxgbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123azxgbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdgsfdgfds57123azxgbcg", as_arc(b"xyz"));







    trie.insert(b"57gfdgsfgfdgfsdggsdesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbcd", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbce", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbcf", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdbcg", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdgbcd", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdgbce", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdgbcf", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdgbcg", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbcd", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbce", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbcf", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxbcg", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxgbcd", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxgbce", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxgbcf", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsdxxxgbcg", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23dzxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbcd", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbce", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbcf", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxbcg", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxgbcd", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxgbce", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxgbcf", as_arc(b"xyz"));
    trie.insert(b"57gfdgsfgfdgfsdggsd23azxgbcg", as_arc(b"xyz"));


    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57desM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abce", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57abcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57agbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57agbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57agbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57agbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57dxxxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxgbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxgbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxgbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57axxxgbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesI", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesJ", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesK", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123dzxesM", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesf", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesF", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesG", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesH", as_arc(b"lmnopqrstuv"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesI", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesJ", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesK", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbesM", as_arc(b"lmnopqrstu"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxbcg", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxgbcd", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxgbce", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxgbcf", as_arc(b"xyz"));
    trie.insert(b"fgsfdfdsafssfdsfsdgsfdgfds57123azxgbcg", as_arc(b"xyz"));



    for l in 0..LEN {
      trie.insert(&ARR[..l], as_arc(&ARR[..l]));
      if l >= 1 {trie.insert(&ARR[1..l], as_arc(&ARR[..15]));};
    }
    for l in 0..LEN {
      trie.insert(&ARR[l..], as_arc(&ARR[..l]));
      if l <= LEN {trie.insert(&ARR[l..LEN], as_arc(&ARR[..25]));};
    }
    for l in 0..LEN {
      trie.insert(&ARR[l..], as_arc(&ARR[..LEN]));
    }


    let trie_clone = trie.clone();

    let path = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join(".tmp");

    let serialized =  write_trie(
      format!("(file : \"{}\", module : \"{}\", line : \"{}\")", file!(), module_path!(), line!()),
      trie.clone(),
      |bs, v|{ v.extend_from_slice(bs); ValueSlice::Encode(
        v
      )}, &path
    ).unwrap();
    
    let read = std::fs::File::open(serialized.data_path).unwrap();
    let compressed = offset_and_childmask_zero_compressor(&read, &path).unwrap();

    let read = std::fs::File::open(compressed.path).unwrap();
    let dbg = dbg_hex_line_numbers(&read, &path).unwrap();

    let de_path = path.join("zero_compressed_hex.data");
    let de = deserialize_file(&de_path, |b|as_arc(b)).unwrap();

    // trace(trie_clone.clone());
    let [src,de_] = [string_pathmap_as_btree_dbg(trie_clone), string_pathmap_as_btree_dbg(de)];

    core::assert!(src == de_);

  }

  fn string_pathmap_as_btree_dbg(mut map : BytesTrieMap<Arc<[u8]>>)->BTreeMap<String,String> {
    unsafe {
      let top = map.remove(&[]);
      let out = if let Some(e) = top { 
        BTreeMap::from([ (String::new(), format!("{:?}",std::str::from_utf8_unchecked(&e))) ])
      } else {
        BTreeMap::new()
      };

      let rcell = RefCell::new(out);
      map.into_cata_side_effect(
        |v,  o| drop(rcell.borrow_mut().insert(std::str::from_utf8_unchecked(o).to_owned(), format!("{:?}",std::str::from_utf8_unchecked(v)))),
        |v,_,o| drop(rcell.borrow_mut().insert(std::str::from_utf8_unchecked(o).to_owned(), format!("{:?}",std::str::from_utf8_unchecked(v)))), 
        |_,_,_| ()
      );
      rcell.into_inner()
    }
  }

  fn trace<V : ZipperValue>(trie : BytesTrieMap<V>) {
    let counter = core::sync::atomic::AtomicUsize::new(0);
    trie.into_cata_jumping_side_effect(
      | _,       o | {let n =  counter.fetch_add(1, core::sync::atomic::Ordering::SeqCst);   println!("{n} MAP_F     \n\t\t{{ origin_path : {:?} }}",   std::str::from_utf8(o).unwrap()); n}, 
      | _,  acc, o | {let n =  counter.fetch_add(1, core::sync::atomic::Ordering::SeqCst);   println!("{n} COLLAPSE_F\n\t\t{{ origin_path : {:?},\
                                                                                                                      \n\t\t  acc_id : {acc},\
                                                                                                                     \n\t\t}}", std::str::from_utf8(o).unwrap()); n}, 
      | cm, accs, o | { let n =  counter.fetch_add(1, core::sync::atomic::Ordering::SeqCst); println!("{n} ALG_F     \n\t\t{{ origin_path   : {:?},\
                                                                                                                      \n\t\t  child_bytes   : {:?},\
                                                                                                                      \n\t\t  child_acc_ids : {accs:?}\
                                                                                                                     \n\t\t}}", std::str::from_utf8(o).unwrap(), &pathmap::utils::ByteMaskIter::new(*cm).map(|x| x as char).collect::<Vec<_>>(), ); 
                        n}, 
      | sp,  acc, o | {let n =  counter.fetch_add(1, core::sync::atomic::Ordering::SeqCst);  println!("{n} JUMP_F  \n\t\t{{ origin_path : {:?},\
                                                                                                                    \n\t\t  sub_path    : {:?},\
                                                                                                                    \n\t\t  acc_id      : {acc},\
                                                                                                                   \n\t\t}}", std::str::from_utf8(o).unwrap(), std::str::from_utf8(sp).unwrap(), ); n}, 
    );

  }
}

