use std::{os::linux::raw::stat, sync::Arc};

use pathmap::{trie_map::BytesTrieMap, zipper::{ReadZipperUntracked, WriteZipper, WriteZipperUntracked, Zipper}};

// 0 ^ ExtractSpaceMention(family)(): space
// 1 ^ ExtractSpaceMention(people)(): space
// 2 ^.person NextPath(1): path
// 3 ^.person NextSubspace(1): space
// 4 ^.person Constant(parent)(): path
// 5 ^.person Unwrap(0, 4): space
// 6 ^.person Constant(child)(): path
// 7 ^.person Unwrap(0, 6): space
// 8 ^.person Constant(child)(): path
// 9 ^.person Concat(8, 2): path
// 10 ^.person Unwrap(0, 9): space
// 11 ^.person Restriction(7, 10): space
// 12 ^.person DropHead(11): space
// 13 ^.person Restriction(5, 12): space
// 14 ^.person DropHead(13): space
// 15 ^.person Constant(child)(): path
// 16 ^.person Concat(15, 2): path
// 17 ^.person Unwrap(0, 16): space
// 18 ^.person Subtraction(14, 17): space
// 19 ^.person Constant(female)(): path
// 20 ^.person Unwrap(0, 19): space
// 21 ^.person Intersection(18, 20): space
// 22 ^.person Wrap(21, 2): space
// 23 ^ Constant(Aunt)(): path
// 24 ^ Wrap(22, 23): space




//  reg | path     | Op                  | const-arg | ssa-arg  | output type
// +----+----------+---------------------+-----------+-----------------------
// |  0 | ^        | ExtractSpaceMention | (family)  | (   ,   ,   ,   ) : space
// |  1 | ^        | ExtractSpaceMention | (people)  | (   ,   ,   ,   ) : space
// |  2 | ^.person | NextPath            |           | (  1,   ,   ,   ) : path 
// |  3 | ^.person | NextSubspace        |           | (  1,   ,   ,   ) : space
// |  4 | ^.person | Constant            | (parent)  | (   ,   ,   ,   ) : path 
// |  5 | ^.person | Unwrap              |           | (  0,  4,   ,   ) : space
// |  6 | ^.person | Constant            | (child)   | (   ,   ,   ,   ) : path 
// |  7 | ^.person | Unwrap              |           | (  0,  6,   ,   ) : space
// |  8 | ^.person | Constant            | (child)   | (   ,   ,   ,   ) : path 
// |  9 | ^.person | Concat              |           | (  8,  2,   ,   ) : path 
// | 10 | ^.person | Unwrap              |           | (  0,  9,   ,   ) : space
// | 11 | ^.person | Restriction         |           | (  7, 10,   ,   ) : space
// | 12 | ^.person | DropHead            |           | ( 11,   ,   ,   ) : space
// | 13 | ^.person | Restriction         |           | (  5, 12,   ,   ) : space
// | 14 | ^.person | DropHead            |           | ( 13,   ,   ,   ) : space
// | 15 | ^.person | Constant            | (child)   | (   ,   ,   ,   ) : path 
// | 16 | ^.person | Concat              |           | ( 15,  2,   ,   ) : path 
// | 17 | ^.person | Unwrap              |           | (  0, 16,   ,   ) : space
// | 18 | ^.person | Subtraction         |           | ( 14, 17,   ,   ) : space
// | 19 | ^.person | Constant            | (female)  | (   ,   ,   ,   ) : path 
// | 20 | ^.person | Unwrap              |           | (  0, 19,   ,   ) : space
// | 21 | ^.person | Intersection        |           | ( 18, 20,   ,   ) : space
// | 22 | ^.person | Wrap                |           | ( 21,  2,   ,   ) : space
// | 23 | ^        | Constant            | (Aunt)    | (   ,   ,   ,   ) : path 
// | 24 | ^        | Wrap                |           | ( 22, 23,   ,   ) : space


// load args? constant mentions?
//
// // the constant memory for paths
// "familypeopleparentchildfemaleAunt.person"
//
//
//  // const-arg is a half open range, that actually has the values below
//  // (family)  = 0..6
//  // (people)  = 6..12
//  // (parent)  = 12..18
//  // (child)   = 18..23
//  // (female)  = 23..29
//  // (Aunt)    = 29..33
//  // (.person) = 33..40
//
//  // this example does not need it, but we also need a basic "Space literal" representation
//  // the initial representation would likely be a range of ranges.
//  // 
//  // so, cat.{dog | cow.{rat | sheep}} starting at offset `n`
//  // would be   ..."cat.dogcat.cow.ratcat.cow.sheep"
//  // and        ...[n, n+7, n+17, n+30]
//  // index      ...[i, i+1, i+2,  i+3]
//  // implicitly ...[n..n+7, n+7..n+17, n+17..n+30]
//  // the space ref would be a range i..i+3 
//  //
//  // note, this could all be encoded into the path slice entirely, using read unaligned big endian
//  // in that case it would be a byte offset, and a length ( 8 bytes * number of paths )
//
//  // the output is implicitly ordered
//
//    Implicit         Explicit
//    output           | pathDif        | Op                  | const  | ssa-arg
//                     +----------------+---------------------+--------+------------------
//    0 : space        | "^"            | ExtractSpaceMention |  0.. 6 | [   ,   ,   ,   ]
//    1 : space        | .              | ExtractSpaceMention |  6..12 | [   ,   ,   ,   ]
//    2 : path         | ..{0}/(33..40) | NextPath            |        | [  1,   ,   ,   ]
//    3 : space        | .              | NextSubspace        |        | [  1,   ,   ,   ]
//    4 : path         | .              | Constant            | 12..18 | [   ,   ,   ,   ]
//    5 : space        | .              | Unwrap              |        | [  0,  4,   ,   ]
//    6 : path         | .              | Constant            | 18..23 | [   ,   ,   ,   ]
//    7 : space        | .              | Unwrap              |        | [  0,  6,   ,   ]
//    8 : path         | .              | Constant            | 18..23 | [   ,   ,   ,   ]
//    9 : path         | .              | Concat              |        | [  8,  2,   ,   ]
//   10 : space        | .              | Unwrap              |        | [  0,  9,   ,   ]
//   11 : space        | .              | Restriction         |        | [  7, 10,   ,   ]
//   12 : space        | .              | DropHead            |        | [ 11,   ,   ,   ]
//   13 : space        | .              | Restriction         |        | [  5, 12,   ,   ]
//   14 : space        | .              | DropHead            |        | [ 13,   ,   ,   ]
//   15 : path         | .              | Constant            | 18..23 | [   ,   ,   ,   ]
//   16 : path         | .              | Concat              |        | [ 15,  2,   ,   ]
//   17 : space        | .              | Unwrap              |        | [  0, 16,   ,   ]
//   18 : space        | .              | Subtraction         |        | [ 14, 17,   ,   ]
//   19 : path         | .              | Constant            | 23..29 | [   ,   ,   ,   ]
//   20 : space        | .              | Unwrap              |        | [  0, 19,   ,   ]
//   21 : space        | .              | Intersection        |        | [ 18, 20,   ,   ]
//   22 : space        | .              | Wrap                |        | [ 21,  2,   ,   ]
//   23 : path         | "^"            | Constant            | 29..40 | [   ,   ,   ,   ]
//   24 : space        | .              | Wrap                |        | [ 22, 23,   ,   ]

// my understanding of how to make this work is to use "co-routining zippers"
//
// there is the "register-zipper", and the "focus-zipper"
// the co-routine goes like this :
// instruction -> focus-zipper
//             -> get "ssa-arg"s[0..n : register] 
//             -> register-zipper 
//             -> give "ssa-arg" vals[0..n : space|path] // where path = 1 element space
//             -> focus-zipper
//             -> do instruction
//             -> write to register-zipper

// should "path" be ignored?
// perhaps path should include "unmoved", "delta", and "goto" ?
// given the imperative semantics of the zippers, perhaps deltas can be computed before doing direct calls?
// should the scala code do this?




enum Op {
  Empty,
  // is there no obvious indicator that somthing is a Call atm?
  Call,
  /// are these optimized out?
  Mention,
  Singleton,
  /// what is the space value representation? a list of paths?
  Literal,
  Union,
  Intersection,
  Subtraction,
  Restriction,
  Composition,
  Wrap,
  Unwrap,
  DropHead,
  Transformation,
  Iteration,

  // ?
  ExtractPathRef,
  ExtractSpaceMention,

  // ?
  Constant,
  Concat,
  LeftResidual,
  RightResidual,
}

/// a [`Routine`] is only a description, it should be passed around immutably (usually as an Arc<Routine>) once built.
///
/// the path_store and the space store can be made the same if the share a resource with an Arc<_>
pub struct Routine<CH : ConstantHandles = DefaultRoutine> {
  path_store     : <CH as ConstantHandles>::PathStore,
  space_store    : <CH as ConstantHandles>::SpaceStore,
  instructions   : Vec<Instruction<CH>>,
}
struct DefaultRoutine;

mod sealed {
  // I'm conservatively making this sealed
  use pathmap::trie_map::BytesTrieMap;
  use crate::{PathConstant, SpaceLiteral, PathLookupFailure, SpaceLookupFailure};
  pub trait ConstantHandles : Sized {
    type PathStore;
    type PathHandle : Copy;
    type SpaceStore;
    type SpaceHandle : Copy;
    type ConstArg : Copy;
    fn lookup_path(store : &Self::PathStore, handle : PathConstant<Self>)->Result<&[u8], PathLookupFailure>;
    fn lookup_space(store : &Self::SpaceStore, handle : SpaceLiteral<Self>)->Result<BytesTrieMap<()>, SpaceLookupFailure>;
    fn coerce_path_handle(arg : Self::ConstArg)->PathConstant<Self>;
    fn coerce_space_handle(arg : Self::ConstArg)->SpaceLiteral<Self>;
  }
}
use sealed::ConstantHandles;

#[derive(Debug)]
struct PathLookupFailure;
#[derive(Debug)]
struct SpaceLookupFailure;




#[derive(Clone,Copy)]
struct PathRange{ start : usize, end : usize}
#[derive(Clone,Copy)]
struct SpaceRange{ byte_offset : usize, path_count : usize}

impl ConstantHandles for DefaultRoutine {
  type PathStore  = Arc<[u8]>;
  type PathHandle = PathRange;

  // the default Routine assumes that the SpaceStore is represented with the same store type as PathStore.
  type SpaceStore = Arc<[u8]>;
  type SpaceHandle = SpaceRange;

  type ConstArg = (usize,usize);

  fn lookup_path(store : &Self::PathStore, handle : PathConstant<Self>)->Result<&[u8],PathLookupFailure> {
    let PathConstant(PathRange { start, end }) = handle;
    if store.len() < end { return Err(PathLookupFailure); }
    Ok(&store[start..end])
  }

  fn lookup_space(store : &Self::SpaceStore, handle : SpaceLiteral<Self>)->Result<BytesTrieMap<()>, SpaceLookupFailure> {
      let SpaceLiteral(SpaceRange { byte_offset, path_count }) = handle;
      
      const U64_BYTES : usize= (u64::BITS/8) as usize;
      let bounds = byte_offset+(U64_BYTES * (path_count+1 /* ranges are described with sliding window, so we need one more value */));

      // we can't do unsafe reads if out store is too small
      if bounds > store.len() {return Err(SpaceLookupFailure);}

      let mut unaligned_header =  &raw const store[byte_offset] as *const u64;

      let mut space = BytesTrieMap::new();
      for _ in 0..path_count {
        // Safety: we checked to avoid going out of bounds
        let handle = unsafe {
          let start = u64::from_be((unaligned_header).read_unaligned()) as usize;

          unaligned_header = unaligned_header.add(1);
          let end = u64::from_be((unaligned_header).read_unaligned()) as usize;
          
          PathConstant::<Self>(PathRange { start , end })
        };
        
        let Ok(path) = Self::lookup_path(store, handle) else {return Err(SpaceLookupFailure);};
        space.insert(path, ());
      }
      Ok(space)
  }
  fn coerce_path_handle(arg : Self::ConstArg)->PathConstant<Self> {
      let (start, end) = arg;
      PathConstant(PathRange { start, end })
  }
  fn coerce_space_handle(arg : Self::ConstArg)->SpaceLiteral<Self> {
      let (byte_offset, path_count) = arg;
      SpaceLiteral(SpaceRange { byte_offset, path_count })
  }
}


// represents a zipper operation to change path
#[derive(Clone, Copy)]
enum PathDif<CH : ConstantHandles> {
  Goto(PathConstant<CH>),
  Root,
  Relative(Relative<CH>),
  Noop,
}

#[derive(Clone,Copy)]
struct Relative<CH : ConstantHandles> { accend : usize, decend : Option<PathConstant<CH>>}

type Register = u32;
struct SpaceLiteral<CH : ConstantHandles>(CH::SpaceHandle);
impl<CH : ConstantHandles> Clone for SpaceLiteral<CH> { fn clone(&self) -> Self {Self(self.0.clone())}}
impl<CH : ConstantHandles> Copy  for SpaceLiteral<CH> {}
struct PathConstant<CH : ConstantHandles>(CH::PathHandle);
impl<CH : ConstantHandles> Clone for PathConstant<CH> { fn clone(&self) -> Self {Self(self.0.clone())}}
impl<CH : ConstantHandles> Copy  for PathConstant<CH> {}

struct Instruction<CH : ConstantHandles> {
  focus_op        : PathDif<CH>,
  op              : Op,
  const_arg       : CH::ConstArg,
  input_registers : [Register;4],
}

#[derive(Debug)]
pub enum RoutineErrorCode {
  PathDifAccendingAboveRoot,
  RegisterZipperNotAtRoot,
  FocusZipperNotAtRoot,
  ConstantPathNonExistant,
  RegisterExprectedSpace,
  SpaceLiteralNonExistant,
}
type IntructionLine = usize;
pub struct RoutineError {
  code : RoutineErrorCode,
  instruction : IntructionLine,
}

impl<CH : ConstantHandles> Routine<CH> {
  fn lookup_constant_path(&self, handle : PathConstant<CH>) -> Result<&[u8], PathLookupFailure> { <CH as ConstantHandles>::lookup_path(&self.path_store, handle) }
  fn lookup_constant_space(&self, handle : SpaceLiteral<CH>) -> Result<BytesTrieMap<()>, SpaceLookupFailure> { <CH as ConstantHandles>::lookup_space(&self.space_store, handle) }

  /// in order for this to run efficiently, we require that the zippers are already at their zipper root ()
  pub fn run<'a1, 'a2, 'b1, 'b2>(
    &self,
    register_zipper : &mut pathmap::zipper::WriteZipperTracked<'a1, 'a2, ()>, 
    focus_zipper    : &mut pathmap::zipper::WriteZipperTracked<'b1, 'b2, ()>,
  ) -> Result<(), RoutineError> {
    #![cfg_attr(rustfmt, rustfmt::skip)]

    if !register_zipper.at_root() { return Err(RoutineError { code: RoutineErrorCode::RegisterZipperNotAtRoot, instruction: 0 }); }
    if !focus_zipper.at_root()    { return Err(RoutineError { code: RoutineErrorCode::FocusZipperNotAtRoot, instruction: 0 }); }

    let reg_zh = register_zipper.zipper_head();

    // registers assume that data has been assigned correctly
    struct RegisterSlot<'a,'b>{path : Vec<u8>, space : core::cell::RefCell<Option<WriteZipperUntracked<'a,'b, ()>>>}

    let mut registers = Vec::<RegisterSlot>::with_capacity(self.instructions.len());
    (0..self.instructions.len()).for_each(|_| registers.push(RegisterSlot{path:Vec::new(), space : core::cell::RefCell::new(None)}));

    for (instruction, Instruction {focus_op, op, const_arg, input_registers }) in (&self.instructions).iter().enumerate() {
      macro_rules! acquire_const_path { 
        (let $PATH:ident : ConstArg = $HANDLE:expr) => {
            acquire_const_path!{let $PATH : PathConstant = <CH as ConstantHandles>::coerce_path_handle($HANDLE)}
        };
        (let $PATH:ident : PathConstant = $HANDLE:expr) => {
            let Ok($PATH) = self.lookup_constant_path($HANDLE)  else { return Err(RoutineError { code: RoutineErrorCode::ConstantPathNonExistant, instruction }); };
        };
      }

      let tmp_ = (instruction as u32).to_ne_bytes(/* if we want to export register memoization, we should use another encoding like Big Endian */);
      let out_path = tmp_.as_slice();

      // ///////////////
      // Change Focus //
      // ///////////////

      match *focus_op {
        PathDif::Goto(handle) => {
            acquire_const_path!{let path : PathConstant = handle};
            focus_zipper.reset();
            focus_zipper.descend_to(path);
          }

        PathDif::Relative(Relative { accend, decend }) => {
            if !focus_zipper.ascend(accend) { return Err(RoutineError { code: RoutineErrorCode::PathDifAccendingAboveRoot, instruction }); }
            
            let found  = decend
              .and_then(   |handle| self.lookup_constant_path(handle).ok())
              .map(|path|   {focus_zipper.descend_to(path) }).is_some();
            if !found {
              return Err(RoutineError { code: RoutineErrorCode::ConstantPathNonExistant, instruction })
            }
          }
        PathDif::Root => focus_zipper.reset(),
        PathDif::Noop => {}
      }

      // ////////
      // Do OP //
      // ////////
      let mut out = unsafe { reg_zh.write_zipper_at_exclusive_path_unchecked(out_path) };
      macro_rules! save_output_space {() => {
        #[allow(unreachable_code)]
        {
          out.reset();
          *registers[instruction].space.borrow_mut() = Some(out);
        }
      };}

      macro_rules! acquire_reg {
        (let $SPACE:ident : Space = $REG:expr) => {
              let mut __tmp = registers[$REG as usize].space.borrow();
              let Some($SPACE) = __tmp.as_ref() else {
                return Err(RoutineError { code: RoutineErrorCode::RegisterExprectedSpace, instruction });
              };
            };
        (let $PATH:ident : Path = $REG:expr) => { 
            let $PATH = &registers[$REG as usize].path[..];
          };
      }

      match op {
        Op::Empty => {
            out.set_value(());
            save_output_space!()
          }
        Op::Call      => todo!("Ref to other routine"),
        Op::Mention   => {
            todo!("I'm not sure what this is ... ")
          }

        Op::Singleton => {
            let &[arg_0,..] = input_registers;
            acquire_reg!{let path : Path = arg_0}
            
            out.descend_to(path);
            out.set_value(());
            save_output_space!{}
          }

        Op::Literal => {
            let Ok(space) = self.lookup_constant_space(CH::coerce_space_handle(*const_arg)) else {return Err(RoutineError { code: RoutineErrorCode::SpaceLiteralNonExistant, instruction });};
            out.graft_map(space);

            save_output_space!{}
          }

        Op::Union => {
            let &[arg_0, arg_1, ..] = input_registers;
            acquire_reg!{let arg_0_z : Space = arg_0}
            acquire_reg!{let arg_1_z : Space = arg_1}

            out.graft(arg_0_z);
            out.join(arg_1_z);
            save_output_space!{}
          }
        Op::Intersection => {
            let &[arg_0, arg_1, ..] = input_registers;
            acquire_reg!{let arg_0_z : Space = arg_0}
            acquire_reg!{let arg_1_z : Space = arg_1}

            out.graft(&*arg_0_z);
            out.meet(&*arg_1_z);
            save_output_space!{}
          }
        Op::Subtraction => {
            let &[arg_0, arg_1, ..] = input_registers;
            acquire_reg!{let arg_0_z : Space = arg_0}
            acquire_reg!{let arg_1_z : Space = arg_1}

            out.graft(&*arg_0_z);
            out.subtract(&*arg_1_z);
            save_output_space!{}
          }
        Op::Restriction => {
            let &[arg_0, arg_1, ..] = input_registers;
            acquire_reg!{let arg_0_z  : Space = arg_0}
            acquire_reg!{let arg_1_z  : Space = arg_1}

            out.graft(arg_0_z);
            out.restrict(arg_1_z);
            save_output_space!{}
          }
        Op::Composition => todo!(),
        Op::Wrap => {
            let &[arg_0, arg_1, .. ] = input_registers;
            acquire_reg!{let space : Space = arg_0}
            acquire_reg!{let path  : Path  = arg_1}
            out.descend_to(path);
            out.graft(&*space);
            save_output_space!{}
          }
        Op::Unwrap => {
            let &[arg_0, arg_1, .. ] = input_registers;
            acquire_reg!{let space : Space = arg_0}
            acquire_reg!{let path  : Path  = arg_1}
            let mut z = space.fork_read_zipper();
            z.descend_to(path);
            out.graft(&*space);
            save_output_space!{}

          }
        Op::DropHead            => todo!(),
        Op::Transformation      => todo!(),
        Op::Iteration           => todo!(),
        Op::ExtractPathRef      => {
            acquire_const_path!{let path : ConstArg = *const_arg}

            let extracted = todo!("extract path ... {:?},", path);
            registers[instruction as usize].path.reserve_exact(path.len());
            registers[instruction as usize].path.extend_from_slice(extracted);
          }
        Op::ExtractSpaceMention => {
            acquire_const_path!{let path : ConstArg = *const_arg}

            let extracted = todo!("extract space ... {:?}", path);
            out.graft_map(extracted);
            save_output_space!{}
          }
        Op::Constant => {
            acquire_const_path!(let path : ConstArg = *const_arg);

            registers[instruction as usize].path.reserve_exact(path.len());
            registers[instruction as usize].path.extend_from_slice(path);
          }
        Op::Concat => {
            let &[arg_0, arg_1, ..] = input_registers;
            acquire_reg!{let left  : Path = arg_0}
            acquire_reg!{let right : Path = arg_1}

            let mut out_path = Vec::with_capacity(left.len() + right.len());
            out_path.extend_from_slice(left);
            out_path.extend_from_slice(right);
            
            registers[instruction as usize].path = out_path;
          }
        Op::LeftResidual        => todo!(),
        Op::RightResidual       => todo!(),
      }
    }

    drop(registers);
    drop(reg_zh);
    register_zipper.reset();
    focus_zipper.reset();

    Ok(())
  }
}
















// enum PathItem<BytesHandle> {
//   Symbol(BytesHandle),
//   Variable(BytesHandle),
//   Arity(usize)
// }



// #[test]
// fn h() {
//   let mut t = BytesTrieMap::new();
//   t.insert(b"aaa", 1);
//   t.insert(b"aab", 2);
//   t.insert(b"aac", 3);

//   '_zippers : {
//     let mut zh = t.zipper_head();
//     let mut src = zh.write_zipper_at_exclusive_path(b"aa");
//     let mut dest = zh.write_zipper_at_exclusive_path(b"ab");
    
//     dest.graft(&src);
//   }

//   let c = t.iter().map(|(v,i)| (v.clone(), *i)).collect::<Vec<_>>();
//   println!("{:?}", c)
  
// }