// #![allow(unused)]
#![cfg_attr(rustfmt, rustfmt::skip)]


// let cif = (fn) => (a) => (b) => (x) => (fn(x) ? a : b)(x);



use std::{cell::RefCell, hash::Hasher, io::{Seek, Write}, path::PathBuf};


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
  Path       = 0b_001,
  Value      = 0b_010,
  ChildMask  = 0b_011,
  Branches   = 0b_000,
  PathNode   = 0b_101,
  ValueNode  = 0b_110,
  BranchNode = 0b_100,
}

// impl Tag {
//   const PATH        : u8 = Tag::Path       as u8;
//   const VALUE       : u8 = Tag::Value      as u8;
//   const CHILD_MASK  : u8 = Tag::ChildMask  as u8;
//   const BRANCHES    : u8 = Tag::Branches   as u8;
//   const PATH_NODE   : u8 = Tag::PathNode   as u8;
//   const VALUE_NODE  : u8 = Tag::ValueNode  as u8;
//   const BRANCH_NODE : u8 = Tag::BranchNode as u8;
// }

const OFFSET_LEN : usize = 6;
// values and paths must be shorter than a 256 tebibyte.
type Offset      = [u8; OFFSET_LEN];


pub trait ZipperValue : Clone + Send + Sync + Unpin + 'static {}
impl<T> ZipperValue for T where T : Clone + Send + Sync + Unpin + 'static {}


pub struct SeOutputs {
  pub data_path : PathBuf,
  pub data_file : std::fs::File,
  pub meta_path : PathBuf,
  pub meta_file : std::fs::File,
}

pub fn write_trie<V : ZipperValue, I>(
  trie            : BytesTrieMap<V>,
  serialize_value : impl Fn(&V) -> I,
  out_dir_path    : impl AsRef<std::path::Path>
) -> Result<SeOutputs,std::io::Error>
  where I : IntoIterator<Item = u8>,
{
  core::debug_assert_eq!(
    core::alloc::Layout::new::<Offset>().align(), 
    core::alloc::Layout::new::<u8>().align()
  );

  let mut data_path = out_dir_path.as_ref().to_path_buf();
  data_path.push("binary.data");

  let mut meta_path = out_dir_path.as_ref().to_path_buf();
  meta_path.push("meta.data");

  
  let data_file = std::fs::File::create_new(&data_path)?;
  let mut meta_file = std::fs::File::create_new(&meta_path)?;

  // threading a context between the closures
  let ctx = RefCell::new(Ctx {
    values : BTreeMap::new(),
    value_offsets: Vec::from([0]),
    data_file,
    algf_scratch : AlgFScratch::zeroed()
  });

  // Threading the context is tedious, and error prone, so I've delagted to an outside function
  let Accumulator { hash_idx, max_len, val_count, paths_count } = trie.into_cata_jumping_side_effect::<Result<Accumulator, std::io::Error>, _,_,_,_>(
    |     value,       origin_path| register(&mut ctx.borrow_mut(), CataCase::Mapf     (MapF      { origin_path,      value       }), &serialize_value),
    |     value,  acc, origin_path| register(&mut ctx.borrow_mut(), CataCase::CollapseF(CollapseF { _origin_path: origin_path,      value, acc  }), &serialize_value),
    |child_mask, accs, origin_path| register(&mut ctx.borrow_mut(), CataCase::AlgF     (AlgF      { _origin_path: origin_path, child_mask, accs }), &serialize_value),
    |  sub_path,  acc, origin_path| register(&mut ctx.borrow_mut(), CataCase::JumpF    (JumpF     { _origin_path: origin_path,   sub_path, acc  }), &serialize_value),
  )?;

  let Ctx { values, value_offsets, data_file, .. } = ctx.into_inner();

  // todo!("Write good metadata");
  meta_file.write_fmt(format_args!(
    "{{\
    \nVALUES        : {values:?},\
    \nVALUE_OFFSETS : {value_offsets:?},\
    \nROOT          : {hash_idx:?},\
    \nMAX_PATH_LEN  : {max_len:?},\
    \nVAL_COUNT     : {val_count:?},\
    \nPATHS_COUNT   : {paths_count:?},\
    \n}}"))?;


  Ok(SeOutputs {
    data_path,
    data_file,
    meta_path,
    meta_file,
  })
}

// this being true means we need to add the nil hash to the map
#[cfg(test)]#[test] fn gxhash_finish_zero_is_zero() {
  core::assert!(gxhash::GxHasher::with_seed(0).finish_u128() != 0)
}

type ChildMask      = [u64;4];
type OriginPath<'a> = &'a[u8];
type SubPath<'a>    = &'a[u8];
struct MapF     <'a, V     >{ origin_path : OriginPath<'a>, value : &'a V }
struct CollapseF<'a, V, Acc>{ _origin_path : OriginPath<'a>, value : &'a V, acc : Acc }
struct AlgF     <'a,    Acc>{ _origin_path : OriginPath<'a>, child_mask : &'a ChildMask, accs : &'a mut[Acc]}
struct JumpF    <'a,    Acc>{ _origin_path : OriginPath<'a>, sub_path : SubPath<'a>, acc : Acc }
enum CataCase<'a, V, Acc> {
  Mapf     (MapF     <'a,V    >),
  CollapseF(CollapseF<'a,V,Acc>),
  AlgF     (AlgF     <'a,  Acc>),
  JumpF    (JumpF    <'a,  Acc>),
}

struct Ctx{
  values        : BTreeMap<u128, FilePos>,  
  value_offsets : Vec<FilePos>,
  data_file     : std::fs::File,
  algf_scratch  :AlgFScratch,
}


struct AlgFScratch {
  buffer : [ Offset; 256],
  len    : usize,
}
impl  AlgFScratch {
  const fn zeroed() -> Self { AlgFScratch { buffer: [[0; OFFSET_LEN];256], len: 0 } }
}

struct Accumulator {
  hash_idx    : (u128, FilePos),
  max_len     : usize,
  val_count   : usize,
  paths_count : usize,
}
impl Accumulator {
  const fn zeroed() -> Self {  Accumulator { hash_idx: (0,0), max_len: 0, val_count: 0, paths_count: 0}}
}



type FilePos = u64;

fn register<V, I>(
  ctx             : &mut Ctx,
  cata_case       : CataCase<'_, V, Result<Accumulator, std::io::Error>>,
  serialize_value : impl Fn(&V) -> I,
) -> Result<Accumulator, std::io::Error>
  where 
    I : IntoIterator<Item = u8>
{
  let rollback_or_advance = |context : &mut Ctx, hash : u128, rollback_pos : FilePos | -> Result<(u128, FilePos), std::io::Error> 
      {
            Ok(
          if let Some(&offset) = context.values.get(&hash) {
            // rollback and use lookup value
            let cur_pos = context.data_file.stream_position()?;
            context.data_file.seek_relative(cur_pos as i64 - rollback_pos as i64)?;
            (hash, offset)
          } else {
            // advance
            context.values.insert(hash, rollback_pos);
            context.value_offsets.push(context.data_file.stream_position()?);
            (hash, rollback_pos)
          }
        )
      };

  let serialize_with_rollback = |context : &mut Ctx, tag : Tag, i : &mut dyn Iterator<Item = u8>| -> Result<(u128, FilePos), std::io::Error>
      {
        let rollback_pos = *context.value_offsets.last().unwrap();
        let mut hasher = GxHasher::with_seed(0);

        hasher.write_u8(tag as u8);
        context.data_file.write(&[tag as u8])?;

        
        for b in i {
          hasher.write_u8(b);
          context.data_file.write(&[b])?;
        }
        let hash = hasher.finish_u128();

        rollback_or_advance(context, hash, rollback_pos)
      };

  // Val ::=                     Tag,               SeIdx,             SeIdx
  // Val === seed(0) -> write_u8(Tag) -> write_u128(Hash) -> write_u128(Hash)
  let write_node = |context : &mut Ctx, tag : Tag,(value_hash, value_idx) : (u128, FilePos), (cont_hash, cont_idx) : (u128, FilePos)| -> Result<(u128, u64), std::io::Error>
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
                             let cur_pos = context.data_file.stream_position()?;
                             let [ _, _, v_offset @ .. ] = value_idx.to_be_bytes();
                             let [ _, _, c_offset @ .. ] = cont_idx.to_be_bytes();
                             let _type_check : [Offset; 2] = [v_offset, c_offset];
                             
                             context.data_file.write(&[tag as u8])?;
                             context.data_file.write(&v_offset)?;
                             context.data_file.write(&c_offset)?;
                             
                             let new_pos = context.data_file.stream_position()?;
                             context.value_offsets.push(new_pos);
                             Ok((hash, cur_pos))
                           }
        }
      };


  let acc_out = match cata_case {
    CataCase::Mapf(MapF { origin_path, value })        => { let v = serialize_with_rollback(ctx, Tag::Value, &mut serialize_value(value).into_iter())?;
                                                            let nil = register(ctx, CataCase::AlgF(AlgF { _origin_path: origin_path, child_mask: &[0;4], accs: &mut [] }), &serialize_value)?.hash_idx;
                                                            let hash_idx = write_node(ctx, Tag::ValueNode, v, nil)?;
                                                            Accumulator {
                                                                hash_idx,
                                                                max_len     : origin_path.len(),
                                                                val_count   : 1,
                                                                paths_count : 1,
                                                            }
                                                          }
    CataCase::CollapseF(CollapseF { value, acc, .. })  => { let v = serialize_with_rollback(ctx, Tag::Value, &mut serialize_value(value).into_iter())?;
                                                            let cont = acc?;
                                                            let hash_idx = write_node(ctx, Tag::ValueNode, v, cont.hash_idx)?;
                                                            Accumulator { 
                                                              hash_idx,
                                                              val_count   : cont.val_count+1, 
                                                              ..cont
                                                            }
                                                          }
    CataCase::AlgF(AlgF { child_mask, accs, .. })      => { 
                                                            let child_mask_hash_idx = serialize_with_rollback(ctx, Tag::ChildMask, &mut child_mask.map(|word| word.to_be_bytes()).as_flattened().into_iter().copied())?;
                                                            
                                                            
                                                            // compute the hash : seed(0) -> forall branchhash . write_u128(branch hash)

                                                            // reset the scratch buffer
                                                            ctx.algf_scratch.len = 0;
                                                            
                                                            let mut acc = Accumulator::zeroed();
                                                            let mut hasher = gxhash::GxHasher::with_seed(0);
                                                            
                                                            for each in accs {
                                                              let Accumulator { hash_idx, max_len, val_count, paths_count } = core::mem::replace(each, Ok(Accumulator::zeroed()))?;
                                                            
                                                              hasher.write_u128(hash_idx.0);
                                                              let [ _, _, offset @ .. ] = acc.hash_idx.1.to_be_bytes();
                                                              let _type_check : Offset = offset;

                                                              ctx.algf_scratch.buffer[ctx.algf_scratch.len] = offset;
                                                            
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
                                                                  let Ctx { values, value_offsets, data_file, algf_scratch } = ctx;
                                                                  
                                                                  let cur_pos = data_file.stream_position()?;
                                                                  data_file.write(&[Tag::Branches as u8])?;
                                                                  data_file.write_all(algf_scratch.buffer[0..algf_scratch.len].as_flattened())?;
                                                                  value_offsets.push(data_file.stream_position()?);
                                                                  values.insert(branches_hash, cur_pos);
                                                                  
                                                                  cur_pos
                                                                };

                                                            let branches_hash_idx = (branches_hash, branches_idx);

                                                            let hash_idx = write_node(ctx, Tag::BranchNode, child_mask_hash_idx, branches_hash_idx)?;
                                                            Accumulator {
                                                              hash_idx,
                                                              .. acc
                                                            }
                                                            
                                                          }
    CataCase::JumpF(JumpF { sub_path, acc, .. })       => { core::debug_assert!(!sub_path.is_empty());
                                                            let p = serialize_with_rollback(ctx, Tag::Path, &mut sub_path.into_iter().copied())?;
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
