#![cfg_attr(rustfmt, rustfmt::skip)]
use std::sync::Arc;

use pathmap::{ring::{DistributiveLattice, Lattice}, trie_map::BytesTrieMap, zipper::{ReadOnlyZipper, ReadZipperTracked, ReadZipperUntracked, WriteZipper, WriteZipperTracked, WriteZipperUntracked, Zipper}};

mod cf_iter;
use cf_iter::CfIter;

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






#[derive(Debug,Clone, Copy)]
enum Op {
  /// `() -> Space`
  Empty,
  Mention,
  /// `(Path) -> Space`
  Call,
  Singleton,
  
  // /// `<const LIT: Space>() -> Space`
  // Literal,

  /// `(Space, Space) -> Space`
  Union,
  /// `(Space, Space) -> Space`
  Intersection,
  /// `(Space, Space) -> Space`
  Subtraction,
  /// `(minutend : Space, subtrahend Space) -> Space`
  Restriction,
  /// `(src : Space, filter : Space) -> Space`
  Composition,
  /// `(src : Space, path : Path) -> Space`
  Wrap,
  /// `(src : Space, path : Path) -> Space`
  Unwrap,
  /// `(Space) -> Space`
  DropHead,
  /// `(src : Space, pattern : Path, template : Path) -> Space`
  Transformation,

  Iteration,
  /// this is relative to the focus
  /// `(Space) -> Path`
  //  change name to NextSymbol?
  NextPath,
  /// this is relative to the focus
  /// `(Space) -> Space`
  //  change
  NextSubspace,

  // ? should this only extract values that have alreay been memoed ?
  ExtractPathRef,
  // ? should this only extract values that have alreay been memoed ?
  ExtractSpaceMention,

  // `<const LIT : Path>() -> `
  Constant,
  Concat,
  LeftResidual,
  RightResidual,

  // Subroutine Ops
  IterSubRoutine,
  Exit,

}

// /// a [`Routine`] is only a description, it should be passed around immutably (usually as an Arc<Routine>) once built.
// ///
// /// the path_store and the space store can be made the same if the share a resource with an Arc<_>
// pub struct Routine<CH : ConstantHandles = DefaultRoutine> {
//   store     : <CH as ConstantHandles>::Store,
//   instructions   : Vec<Instruction<CH>>,
//   max_subroutine_depth : usize,
// }
// struct DefaultRoutine;

// mod sealed {
//   // I'm conservatively making this sealed
//   use pathmap::trie_map::BytesTrieMap;
//   use crate::{PathConstant, /* SpaceLiteral, */ PathLookupFailure, /* SpaceLookupFailure */};
//   pub trait ConstantHandles : Sized {
//     type Store;
//     type PathHandle: Copy;
//     // type SpaceHandle : Copy;
//     type ConstArg : Copy;
//     fn lookup_path(store : &Self::Store, handle : PathConstant<Self>)->Result<&[u8], PathLookupFailure>;
//     // fn lookup_space(store : &Self::Store, handle : SpaceLiteral<Self>)->Result<BytesTrieMap<()>, SpaceLookupFailure>;
//     fn coerce_path_handle(arg : Self::ConstArg)->PathConstant<Self>;
//     // fn coerce_space_handle(arg : Self::ConstArg)->SpaceLiteral<Self>;
//   }
// }
// use sealed::ConstantHandles;

// #[derive(Debug)]
// struct PathLookupFailure;
// // #[derive(Debug)]
// // struct SpaceLookupFailure;


// #[derive(Clone,Copy)]
// struct PathRange{ start : usize, end : usize}
// // #[derive(Clone,Copy)]
// // struct SpaceRange{ byte_offset : usize, path_count : usize}

// impl ConstantHandles for DefaultRoutine {
//   type Store  = Arc<[u8]>;
//   type PathHandle = PathRange;

//   // type SpaceHandle = SpaceRange;

//   type ConstArg = (usize,usize);

//   fn lookup_path(store : &Self::Store, handle : PathConstant<Self>)->Result<&[u8],PathLookupFailure> {
//     let PathConstant(PathRange { start, end }) = handle;
//     if store.len() < end { return Err(PathLookupFailure); }
//     Ok(&store[start..end])
//   }

//   // fn lookup_space(store : &Self::Store, handle : SpaceLiteral<Self>)->Result<BytesTrieMap<()>, SpaceLookupFailure> {
//   //     let SpaceLiteral(SpaceRange { byte_offset, path_count }) = handle;
      
//   //     const U64_BYTES : usize= (u64::BITS/8) as usize;
//   //     let bounds = byte_offset+(U64_BYTES * (path_count+1 /* ranges are described with sliding window, so we need one more value */));

//   //     // we can't do unsafe reads if out store is too small
//   //     if bounds > store.len() {return Err(SpaceLookupFailure);}

//   //     let mut unaligned_header =  &raw const store[byte_offset] as *const u64;

//   //     let mut space = BytesTrieMap::new();
//   //     for _ in 0..path_count {
//   //       // Safety: we checked to avoid going out of bounds
//   //       let handle = unsafe {
//   //         let start = u64::from_be((unaligned_header).read_unaligned()) as usize;

//   //         unaligned_header = unaligned_header.add(1);
//   //         let end = u64::from_be((unaligned_header).read_unaligned()) as usize;
          
//   //         PathConstant::<Self>(PathRange { start , end })
//   //       };
        
//   //       let Ok(path) = Self::lookup_path(store, handle) else {return Err(SpaceLookupFailure);};
//   //       space.insert(path, ());
//   //     }
//   //     Ok(space)
//   // }
//   fn coerce_path_handle(arg : Self::ConstArg)->PathConstant<Self> {
//       let (start, end) = arg;
//       PathConstant(PathRange { start, end })
//   }
//   // fn coerce_space_handle(arg : Self::ConstArg)->SpaceLiteral<Self> {
//   //     let (byte_offset, path_count) = arg;
//   //     SpaceLiteral(SpaceRange { byte_offset, path_count })
//   // }
// }


// // represents a zipper operation to change path
// #[derive(Clone, Copy)]
// enum PathDif<CH : ConstantHandles> {
//   Goto(PathConstant<CH>),
//   Root,
//   Relative(Relative<CH>),
//   Noop,
// }

// #[derive(Clone,Copy)]
// struct Relative<CH : ConstantHandles> { accend : usize, decend : Option<PathConstant<CH>>}

// // struct SpaceLiteral<CH : ConstantHandles>(CH::SpaceHandle);
// // impl<CH : ConstantHandles> Clone for SpaceLiteral<CH> { fn clone(&self) -> Self {Self(self.0.clone())}}
// // impl<CH : ConstantHandles> Copy  for SpaceLiteral<CH> {}

// struct PathConstant<CH : ConstantHandles>(CH::PathHandle);
// impl<CH : ConstantHandles> Clone for PathConstant<CH> { fn clone(&self) -> Self {Self(self.0.clone())}}
// impl<CH : ConstantHandles> Copy  for PathConstant<CH> {}

// struct Instruction<CH : ConstantHandles> {
//   focus_op        : PathDif<CH>,
//   op              : Op,
//   const_arg       : CH::ConstArg,
//   input_registers : [Register;4],
// }

// #[derive(Debug)]
// pub enum RoutineErrorCode {
//   PathDifAccendingAboveRoot,
//   RegisterZipperNotAtRoot,
//   FocusZipperNotAtRoot,
//   ConstantPathNonExistant,
//   RegisterExprectedSpace,
//   SpaceLiteralNonExistant,
// }
// type IntructionLine = usize;
// pub struct RoutineError {
//   code : RoutineErrorCode,
//   instruction : IntructionLine,
// }

// impl<CH : ConstantHandles> Routine<CH> {
//   fn lookup_constant_path(&self, handle : PathConstant<CH>) -> Result<&[u8], PathLookupFailure> { <CH as ConstantHandles>::lookup_path(&self.store, handle) }
//   // fn lookup_constant_space(&self, handle : SpaceLiteral<CH>) -> Result<BytesTrieMap<()>, SpaceLookupFailure> { <CH as ConstantHandles>::lookup_space(&self.store, handle) }

//   /// in order for this to run efficiently, we require that the zippers are already at their zipper root ()
//   pub fn run<'a1, 'a2, 'b1, 'b2>(
//     &self,
//     register_zipper : &mut pathmap::zipper::WriteZipperTracked<'a1, 'a2, ()>,
//     focus_zipper    : &mut pathmap::zipper::WriteZipperTracked<'b1, 'b2, ()>,
//   ) -> Result<(), RoutineError> {
//     #![deprecated = "this will have issues dealing with 'iterative queries'."]
//     #![cfg_attr(rustfmt, rustfmt::skip)]

//     if !register_zipper.at_root() { return Err(RoutineError { code: RoutineErrorCode::RegisterZipperNotAtRoot, instruction: 0 }); }
//     if !focus_zipper.at_root()    { return Err(RoutineError { code: RoutineErrorCode::FocusZipperNotAtRoot, instruction: 0 }); }

//     let reg_zh = register_zipper.zipper_head();

//     // registers assume that data has been assigned correctly
//     struct RegisterSlot<'a,'b>{path : Vec<u8>, space : core::cell::RefCell<Option<WriteZipperUntracked<'a,'b, ()>>>}

//     let mut registers = Vec::<RegisterSlot>::with_capacity(self.instructions.len());
//     (0..self.instructions.len()).for_each(|_| registers.push(RegisterSlot{path:Vec::new(), space : core::cell::RefCell::new(None)}));

//     for (instruction, Instruction {focus_op, op, const_arg, input_registers }) in (&self.instructions).iter().enumerate() {
//       macro_rules! acquire_const_path { 
//         (let $PATH:ident : ConstArg = $HANDLE:expr) => {
//             acquire_const_path!{let $PATH : PathConstant = <CH as ConstantHandles>::coerce_path_handle($HANDLE)}
//         };
//         (let $PATH:ident : PathConstant = $HANDLE:expr) => {
//             let Ok($PATH) = self.lookup_constant_path($HANDLE)  else { return Err(RoutineError { code: RoutineErrorCode::ConstantPathNonExistant, instruction }); };
//         };
//       }

//       let tmp_ = (instruction as u32).to_ne_bytes(/* if we want to export register memoization, we should use another encoding like Big Endian */);
//       let out_path = tmp_.as_slice();

//       // ///////////////
//       // Change Focus //
//       // ///////////////

//       match *focus_op {
//         PathDif::Goto(handle) => {
//             acquire_const_path!{let path : PathConstant = handle};
//             focus_zipper.reset();
//             focus_zipper.descend_to(path);
//           }

//         PathDif::Relative(Relative { accend, decend }) => {
//             if !focus_zipper.ascend(accend) { return Err(RoutineError { code: RoutineErrorCode::PathDifAccendingAboveRoot, instruction }); }
            
//             let found  = decend
//               .and_then(   |handle| self.lookup_constant_path(handle).ok())
//               .map(|path|   {focus_zipper.descend_to(path) }).is_some();
//             if !found {
//               return Err(RoutineError { code: RoutineErrorCode::ConstantPathNonExistant, instruction })
//             }
//           }
//         PathDif::Root => focus_zipper.reset(),
//         PathDif::Noop => {}
//       }

//       // ////////
//       // Do OP //
//       // ////////
//       let mut out = unsafe { reg_zh.write_zipper_at_exclusive_path_unchecked(out_path) };
//       macro_rules! save_output_space {() => {
//         #[allow(unreachable_code)]
//         {
//           out.reset();
//           *registers[instruction].space.borrow_mut() = Some(out);
//         }
//       };}

//       macro_rules! acquire_reg {
//         (let $SPACE:ident : Space = $REG:expr) => {
//               let mut __tmp = registers[$REG as usize].space.borrow();
//               let Some($SPACE) = __tmp.as_ref() else {
//                 return Err(RoutineError { code: RoutineErrorCode::RegisterExprectedSpace, instruction });
//               };
//             };
//         (let $PATH:ident : Path = $REG:expr) => { 
//             let $PATH = &registers[$REG as usize].path[..];
//           };
//       }

//       match op {
//         Op::Empty => {
//             out.set_value(());
//             save_output_space!()
//           }

//         Op::Call      => todo!("Ref to other routine"),

//         Op::Mention   => {
//             todo!("I'm not sure what this is ... (as Argument!)")
//           }

//         Op::Singleton => {
//             let &[arg_0,..] = input_registers;
//             acquire_reg!{let path : Path = arg_0}
            
//             out.descend_to(path);
//             out.set_value(());
//             save_output_space!{}
//           }

//         // Op::Literal => {
//         //     let Ok(space) = self.lookup_constant_space(CH::coerce_space_handle(*const_arg)) else {return Err(RoutineError { code: RoutineErrorCode::SpaceLiteralNonExistant, instruction });};
//         //     out.graft_map(space);

//         //     save_output_space!{}
//         //   }

//         Op::Union => {
//             let &[arg_0, arg_1, ..] = input_registers;
//             acquire_reg!{let arg_0_z : Space = arg_0}
//             acquire_reg!{let arg_1_z : Space = arg_1}

//             out.graft(arg_0_z);
//             out.join(arg_1_z);
//             save_output_space!{}
//           }

//         Op::Intersection => {
//             let &[arg_0, arg_1, ..] = input_registers;
//             acquire_reg!{let arg_0_z : Space = arg_0}
//             acquire_reg!{let arg_1_z : Space = arg_1}

//             out.graft(&*arg_0_z);
//             out.meet(&*arg_1_z);
//             save_output_space!{}
//           }

//         Op::Subtraction => {
//             let &[arg_0, arg_1, ..] = input_registers;
//             acquire_reg!{let arg_0_z : Space = arg_0}
//             acquire_reg!{let arg_1_z : Space = arg_1}

//             out.graft(&*arg_0_z);
//             out.subtract(&*arg_1_z);
//             save_output_space!{}
//           }

//         Op::Restriction => {
//             let &[arg_0, arg_1, ..] = input_registers;
//             acquire_reg!{let arg_0_z  : Space = arg_0}
//             acquire_reg!{let arg_1_z  : Space = arg_1}

//             out.graft(arg_0_z);
//             out.restrict(arg_1_z);
//             save_output_space!{}
//           }

//         Op::Composition => todo!(),

//         Op::Wrap => {
//             let &[arg_0, arg_1, .. ] = input_registers;
//             acquire_reg!{let space : Space = arg_0}
//             acquire_reg!{let path  : Path  = arg_1}
//             out.descend_to(path);
//             out.graft(&*space);
//             save_output_space!{}
//           }

//         Op::Unwrap => {
//             let &[arg_0, arg_1, .. ] = input_registers;
//             acquire_reg!{let space : Space = arg_0}
//             acquire_reg!{let path  : Path  = arg_1}
//             let mut z = space.fork_read_zipper();
//             z.descend_to(path);
//             out.graft(&z);
//             save_output_space!{}

//           }

//         Op::DropHead => {
//             // TODO! this drop head is over specialized and should be replaced with one you can plugin.
//             let &[arg_0, .. ] = input_registers;
//             acquire_reg!(let space : Space = arg_0);
//             out.graft(space);
//             let mask = out.child_mask();

//             let mut it = CfIter::new(&mask);

//             while let Some(b) = it.next() {
//               if b == 0 {continue;}
//               assert!(out.descend_to(&[b]));
//               out.drop_head(b as usize);
//               assert!(out.ascend(1));
//             }
//             save_output_space!{}
//           }

//         Op::Transformation      => todo!(),

//         Op::Iteration           => todo!("implement `NextPath` and `NextSubspace`"),

//         Op::NextPath => {
//           // the name is apparently a misnomer...
          
//           // let &[arg_0, .. ] = input_registers;
//           // acquire_const_path!{let space : Space = arg_0}


//           // let path = space.
//           // registers[instruction as usize].path.reserve_exact(focus_path.len());
//           // registers[instruction as usize].path.extend_from_slice(focus_path);
//           // registers[instruction as usize].path.extend_from_slice(path);



//           todo!{}
//         },

//         Op::NextSubspace => {

//             todo!{}

//             save_output_space!{}
//           },

//         Op::ExtractPathRef      => {
//             acquire_const_path!{let path : ConstArg = *const_arg}
            
//             let focus_path = focus_zipper.path();
//             registers[instruction as usize].path.reserve_exact(focus_path.len() + path.len());
//             registers[instruction as usize].path.extend_from_slice(focus_path);
//             registers[instruction as usize].path.extend_from_slice(path);
//           }

//         Op::ExtractSpaceMention => {
//             acquire_const_path!{let path : ConstArg = *const_arg}

//             let mut reader = focus_zipper.fork_read_zipper();
//             reader.descend_to(path);
//             out.graft(&reader);
//             save_output_space!{}
//           }

//         Op::Constant => {
//             acquire_const_path!(let path : ConstArg = *const_arg);

//             registers[instruction as usize].path.reserve_exact(path.len());
//             registers[instruction as usize].path.extend_from_slice(path);
//           }

//         Op::Concat => {
//             let &[arg_0, arg_1, ..] = input_registers;
//             acquire_reg!{let left  : Path = arg_0}
//             acquire_reg!{let right : Path = arg_1}

//             let mut out_path = Vec::with_capacity(left.len() + right.len());
//             out_path.extend_from_slice(left);
//             out_path.extend_from_slice(right);
            
//             registers[instruction as usize].path = out_path;
//           }
//         Op::LeftResidual        => todo!(),

//         Op::RightResidual       => todo!(),

//         _ => todo!("Subroutine Ops"),
//       }
//     }

//     drop(registers);
//     drop(reg_zh);
//     register_zipper.reset();
//     focus_zipper.reset();

//     Ok(())
//   }
// }







type Register = u16;

type SymbolTable = bucket_map::SharedMappingHandle;

type PathOffset = usize;
type PathLen    = usize;
// type ConstPathReference = (PathOffset, PathLen);

#[derive(Debug, Clone, Copy)]
struct PathStoreReference { offset : PathOffset, len : PathLen}

type UnparsedPath<'a> = &'a [u8];
type PathStore<'a>    = &'a [u8];
type PathRef<'a>      = &'a [u8];

type Fuel = u64;

#[derive(Debug,Clone)]
struct Instruction_{
  op              : Op,
  const_arg       : PathStoreReference,
  input_registers : [Register;4],
}

#[derive(Clone)]
struct Subroutine{ iter : CfIter, previous_program_counter : usize, previous_path_buffer_len : usize }

#[derive(Clone)]
struct RoutineActivationRecord {
  arg_offsets      : ParsedRoutine,
  routine_code     : Routine_,
  program_counter  : ProgramCounter,
  subroutine_stack : Vec<Subroutine>,
  space_reg        : Vec<BytesTrieMap<()>>,
  path_reg         : Vec<PathStoreReference /* into the path_buffer */ >,
  path_buffer      : Vec<u8>,
}

pub struct CallStack {
  data    : Vec<u8>,
  offsets : Vec<usize>,
}

pub struct Interpreter {
  symbol_table          : SymbolTable,
  memo                  : BytesTrieMap<()>,
  routines              : BytesTrieMap<Routine_>,
  routine_continuations : BytesTrieMap<RoutineActivationRecord>,
}

struct RoutineActivationRecordEstimate {
  instruction_count      : usize,
  subroutine_stack_depth : usize,
  path_buffer_size       : usize,
}

type ProgramCounter = usize;

pub enum RoutineError_ { 
  RoutineNotFound(CallStack),
  RoutineMalformed((CallStack, ProgramCounter)),
  ValueWasNotMemoed((CallStack, ProgramCounter)),
}

#[derive(Clone)]
struct RoutineImpl {
  const_paths_store      : Arc<[u8]>,
  formal_parameter_count : usize,
  max_subroutine_depth   : usize,
  instructions           : Arc<[Instruction_]>,
}
type Routine_ = Arc<RoutineImpl>;


impl RoutineImpl {
  fn aquire_estimate_size(&self)->RoutineActivationRecordEstimate {
    todo!()
  }
  fn routine_name(&self) -> &[u8] { todo!() }
}


#[derive(Debug,Clone)]
struct ParsedRoutine {
  routine_name_index : PathStoreReference,
  // first_3 : [ConstPathReference ; 3] // maybe the first N arguments (maybe 3?) could be known statically avoiding a vector allocation on a common case
  arg_idicies : Vec<PathStoreReference>
}

impl Interpreter {
  fn parse_routine_with_args_paths(routine_with_arguments : UnparsedPath) -> ParsedRoutine {todo!()}
  fn path_from_offset(store : PathStore, offset_ref : PathStoreReference) -> PathRef { &store[offset_ref.offset .. offset_ref.offset + offset_ref.len] }

  pub fn run_routine<'a1, 'a2, 'b1, 'b2>(
    &mut self,
    routine_with_arguments    : UnparsedPath /* this is actually a path of paths RoutineNamespace.RoutineName.(argsAsPaths.,)* */,
    fuel         : Fuel,
  ) -> Result<BytesTrieMap<()>, RoutineError_> {
    #![cfg_attr(rustfmt, rustfmt::skip)]

    const SLICE_SIZE : usize = 2;

    let initial_slice : [usize ; SLICE_SIZE] = [0,routine_with_arguments.len()];
    let mut call_stack : CallStack = CallStack { data: Vec::from(routine_with_arguments), offsets : Vec::from(initial_slice) };

    'routine : loop {

      core::debug_assert!(call_stack.offsets.len() >= SLICE_SIZE);

      let popped_value : Option<BytesTrieMap<()>> = 'find_memo : {
        
        let len   = call_stack.offsets.len();
        let start = call_stack.offsets[len-2];
        let end   = call_stack.offsets[len-1];
        let routine_path = &call_stack.data[start..end];
        
        let rz = self.memo.read_zipper_at_path(routine_path);
        let Some(m) = rz.make_map() else { break 'find_memo None; };

        if call_stack.offsets.len() == SLICE_SIZE { return Ok(m)};

        // pop value
        unsafe { call_stack.data.set_len(end) };
        call_stack.offsets.pop();
        Some(m)
      };

      // init activation record, check if one is partially evaluated already
      let mut record = 
      if let Some(record) = self.routine_continuations.remove(routine_with_arguments) {
        record
      } else {

        let arg_offsets = Interpreter::parse_routine_with_args_paths(routine_with_arguments);

        let routine_name = Interpreter::path_from_offset(routine_with_arguments, arg_offsets.routine_name_index);

        let Some(routine_code) = self.routines.get(routine_name).cloned() else {return Err(RoutineError_::RoutineNotFound(call_stack));};

        let RoutineActivationRecordEstimate { instruction_count, subroutine_stack_depth, path_buffer_size } = routine_code.aquire_estimate_size();

        let mut new_record = RoutineActivationRecord{
          arg_offsets,
          routine_code,
          program_counter  : 0,
          subroutine_stack : Vec::with_capacity(subroutine_stack_depth),
          space_reg        : vec![BytesTrieMap::new()                      ; instruction_count],
          path_reg         : vec![PathStoreReference { offset: 0, len: 0 } ; instruction_count],
          path_buffer      : Vec::with_capacity(path_buffer_size),
        };
        new_record
      };

      let RoutineActivationRecord { arg_offsets, routine_code, program_counter, subroutine_stack, space_reg, path_reg, path_buffer } = &mut record;

      if let Some(m) = popped_value {
        // merge into the record
        space_reg[*program_counter] = m;
        *program_counter += 1;
        continue;
      }

      let RoutineImpl { const_paths_store, formal_parameter_count, max_subroutine_depth, instructions } = &**routine_code;

      core::debug_assert_eq!(arg_offsets.arg_idicies.len(), *formal_parameter_count);

      'subroutine : loop {
        core::debug_assert!(*max_subroutine_depth >= subroutine_stack.len());

        let Instruction_ { op, const_arg, input_registers } = instructions[*program_counter];
        macro_rules! binary_space_op {($OP:ident) => {{ 
            let [arg_0, arg_1, ..] = input_registers;
            let out = space_reg[arg_0 as usize].clone();
            out.$OP(&space_reg[arg_1 as usize]);
            space_reg[*program_counter] = out;
        }};}
        macro_rules! const_path {() => { &const_paths_store[const_arg.offset .. const_arg.offset + const_arg.len];};}

        match op {
            Op::Empty                => { // should be a no-op
                                          core::debug_assert!(space_reg[*program_counter].is_empty())
                                        },

            Op::Call                 => { let [arg_0 /* the whole path must fist be concatted with all args */, ..] = input_registers;
                                          let PathStoreReference { offset, len } = path_reg[arg_0 as usize];
                                          
                                          let path = &path_buffer[offset..offset+len];
                                          if let Some(m) =  self.memo.read_zipper_at_path(path).make_map() {
                                            // if we can get the value now without running a full routine
                                            space_reg[*program_counter] = m;

                                          } else {
                                            // this branch assumes we need to change routines.

                                            let offsets_len = call_stack.offsets.len();
                                            
                                            let mut wz = self.routine_continuations.write_zipper();
                                            wz.descend_to(&call_stack.data[call_stack.offsets[offsets_len-2]..call_stack.offsets[offsets_len-1]]);
                                            
                                            if let Some(cont) = wz.get_value() {
                                              if cont.program_counter > *program_counter {
                                                // the current continuation should be discarded and rerun
                                                // the rerun should aquire the more advanced continuation
                                                continue 'routine;
                                              }
                                            }
                                            
                                            call_stack.data.extend_from_slice(path);
                                            call_stack.offsets.push(call_stack.data.len());
                                            
                                            wz.set_value(record);
                                            
                                            // we want to skip bumping the program counter, it should only be advanced when we sucessfully call the routine
                                            continue 'routine                                            
                                          }
                                        },

            Op::Mention              => { todo!("I'm not sure what this is ... (as Argument!)")
                                        },

            Op::Singleton            => { let [arg_0,..] = input_registers;
                                          let PathStoreReference { offset, len } = path_reg[arg_0 as usize];
                                          let prefix = &path_buffer[ offset .. offset+len ];
                                          
                                          space_reg[*program_counter] = BytesTrieMap::new();
                                          let mut wz = space_reg[*program_counter].write_zipper_at_path(prefix);
                                          wz.set_value(());
                                        },

            Op::Union                => binary_space_op!{join},
            Op::Intersection         => binary_space_op!{meet},
            Op::Subtraction          => binary_space_op!{subtract},
            Op::Restriction          => binary_space_op!{restrict},


            Op::Wrap                 => { let [arg_0 /* Space */, arg_1 /* Path */, .. ] = input_registers;
                                          let PathStoreReference { offset, len } = path_reg[arg_1 as usize];
                                          let prefix = &path_buffer[ offset .. offset + len ];
                                          
                                          let mut out = BytesTrieMap::new();
                                          out.write_zipper_at_path(prefix).graft_map(space_reg[arg_0 as usize].clone());
                                          
                                          space_reg[*program_counter] = out;
                                        },

            Op::Unwrap               => { let [arg_0 /* Space */, arg_1 /* Path */, .. ] = input_registers;
                                          let PathStoreReference { offset, len } = path_reg[arg_1 as usize];
                                          let prefix = &path_buffer[ offset .. offset + len ];
                                     
                                          let Some(out) = space_reg[arg_0 as usize].read_zipper_at_borrowed_path(prefix).make_map() else { return Err(RoutineError_::RoutineMalformed((call_stack, *program_counter))); };
                                          
                                          space_reg[*program_counter] = out;
                                        },

            Op::DropHead             => { let [arg_0, .. ] = input_registers;
                                          let mut out = space_reg[arg_0 as usize].clone();
                                          let mut wz = out.write_zipper();

                                          let mask = wz.child_mask();

                                          let mut it = CfIter::new(&mask);
                                          
                                          while let Some(b) = it.next() {
                                            if b == 0 {continue;}
                                            assert!(wz.descend_to(&[b]));
                                            wz.drop_head(b as usize);
                                            assert!(wz.ascend(1));
                                          }
                                          drop(wz);
                                          space_reg[*program_counter] = out;
                                        },

            Op::ExtractPathRef       => { let old_len = path_buffer.len();
                                          path_buffer.extend_from_slice(const_path!());
                                          path_reg[*program_counter] = PathStoreReference { offset : old_len, len : const_arg.len };
                                        },

            Op::ExtractSpaceMention  => { let rz = self.memo.read_zipper_at_borrowed_path(const_path!());
                                          let Some(out) = rz.make_map() else { return Err(RoutineError_::ValueWasNotMemoed((call_stack, *program_counter))); };
                                          
                                          space_reg[*program_counter] = out;
                                        },
                                        
            Op::Constant             => { path_buffer.reserve(const_arg.len);
                                          let old_len = path_buffer.len();
                                          path_buffer.extend_from_slice(const_path!());
                                          path_reg[*program_counter] = PathStoreReference { offset : old_len, len : const_arg.len }
                                        },

            Op::Concat               => { let [arg_0, arg_1, ..] = input_registers;
                                          let prefix_ref = path_reg[arg_0 as usize];
                                          let suffix_ref = path_reg[arg_1 as usize];

                                          let added_len = prefix_ref.len+suffix_ref.len;
                                          path_buffer.reserve(added_len);

                                          let old_len = path_buffer.len();

                                          path_buffer.extend_from_within(prefix_ref.offset..prefix_ref.offset+prefix_ref.len);
                                          path_buffer.extend_from_within(suffix_ref.offset..suffix_ref.offset+suffix_ref.len);

                                          path_reg[*program_counter] = PathStoreReference { offset : old_len, len : added_len };
                                        },



            Op::Transformation       => todo!(),
            Op::Composition          => todo!(),
            Op::IterSubRoutine       => todo!(),
            Op::Exit                 => { todo!("Union with Subroutine parent");
                                          todo!("If Subroutine stack is empty, assign to memo!")
                                        },



            Op::Iteration            => todo!(),
            Op::LeftResidual         => todo!(),
            Op::RightResidual        => todo!(),
            Op::NextPath             => todo!(),
            Op::NextSubspace         => todo!(),
        }

        *program_counter += 1;
      }
    }
  }
}