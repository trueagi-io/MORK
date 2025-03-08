#![cfg_attr(rustfmt, rustfmt::skip)]
use std::{collections::btree_map::Range, sync::Arc};

use pathmap::{ring::Lattice, trie_map::BytesTrieMap, zipper::{WriteZipper, Zipper, ZipperIteration}};

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



#[derive(Debug,Clone, Copy)]
enum Op {
  /// `() -> Space`
  Empty,
  /// `(Path) -> Space`
  Call,
  Singleton,
  
  /// `(Space, Space) -> Space`
  Union,
  /// `(Space, Space) -> Space`
  Intersection,
  /// `(Space, Space) -> Space`
  Subtraction,
  /// `(minutend : Space, subtrahend Space) -> Space`
  Restriction,
  /// `(src : Space, path : Path) -> Space`
  Wrap,
  /// `(src : Space, path : Path) -> Space`
  Unwrap,
  /// `(Space) -> Space`
  DropHead,

  // ? should this only extract values that have alreay been memoed ?
  ExtractPathRef,
  // ? should this only extract values that have alreay been memoed ?
  ExtractSpaceMention,

  // `<const LIT : Path>() -> `
  Constant,
  Concat,

  // Subroutine Ops
  /// `jump location to subroutine inst, space to iterate over`
  IterSubRoutine,
  Exit,
}




/// The index into the register stores for paths and spaces   
/// There is an implied max bound on the number of instructions a routine can hold, `Register::MAX`
type Register    = u16;
type SymbolTable = bucket_map::SharedMappingHandle;

type PathOffset       = usize;
type PathLen          = usize;
type UnparsedPath<'a> = &'a [u8];
type PathStore<'a>    = &'a [u8];
type PathRef<'a>      = &'a [u8];

#[derive(Debug, Clone, Copy)]
struct PathStoreReference { offset : PathOffset, len : PathLen}
impl PathStoreReference {
  fn as_range(self)->core::ops::Range<usize> { self.offset..self.offset+self.len }
}

type Fuel = u64;
type ProgramCounter = usize;

#[derive(Debug,Clone)]
struct Instruction_{
  op              : Op,
  const_arg       : PathStoreReference,
  input_registers : [Register; 4],
}

struct Subroutine{
  /// the space the read zipper is working over; (we could avoid this if the ReadZipperOwned implemented clone, but this is reasonable as it only happens when a subroutine is in the continuation store) 
  zipper_space             : BytesTrieMap<()>,
  read_zipper              : pathmap::zipper::ReadZipperOwned<()>,
  iter                     : CfIter,
  subroutine_start_counter : Register,
  previous_program_counter : Register,
  prefix_first_byte        : u8,
}
impl Clone for Subroutine {
  fn clone(&self) -> Self {
    let Subroutine { read_zipper, iter, previous_program_counter, prefix_first_byte, zipper_space, subroutine_start_counter, }=self;
    let rz_new = zipper_space.clone().into_read_zipper(read_zipper.path());
    Subroutine { 
      read_zipper              : rz_new,
      previous_program_counter : *previous_program_counter, 
      subroutine_start_counter : *subroutine_start_counter,
      zipper_space             : zipper_space.clone(),
      iter                     : iter.clone(), 
      prefix_first_byte        : *prefix_first_byte }
  }
}

#[derive(Clone)]
struct RoutineActivationRecord {
  /// For the moment there is no use of this field, I expect that to change
  arg_offsets      : ParsedRoutine,
  routine_code     : Routine,
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
  routines              : BytesTrieMap<Routine>,
  routine_continuations : BytesTrieMap<RoutineActivationRecord>,
}

struct RoutineActivationRecordEstimate {
  instruction_count      : usize,
  subroutine_stack_depth : usize,
  path_buffer_size       : usize,
}


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
type Routine = Arc<RoutineImpl>;


impl RoutineImpl {
  fn aquire_estimate_size(&self)->RoutineActivationRecordEstimate {
    RoutineActivationRecordEstimate { 
      instruction_count      : self.instructions.len(),
      subroutine_stack_depth : self.instructions.len(),
      path_buffer_size : 0 }
  }
}


#[derive(Debug,Clone)]
struct ParsedRoutine {
  routine_name_index : PathStoreReference,
  // first_3 : [ConstPathReference ; 3] // maybe the first N arguments (maybe 3?) could be known statically avoiding a vector allocation on a common case
  arg_idicies : Vec<PathStoreReference>
}

impl Interpreter {
  fn parse_routine_with_args_paths(routine_with_arguments : UnparsedPath) -> ParsedRoutine { todo!() }
  fn path_from_offset(store : PathStore, offset_ref : PathStoreReference) -> PathRef { &store[offset_ref.offset .. offset_ref.offset + offset_ref.len] }

  pub fn run_routine(
    &mut self,
    routine_with_arguments : UnparsedPath /* this is actually a path of paths RoutineNamespace.RoutineName.(argsAsPaths.,)* */,
    _fuel                   : Fuel,
  ) -> Result<BytesTrieMap<()>, RoutineError_> {
    #![cfg_attr(rustfmt, rustfmt::skip)]

    /// The slice is descibed by a pair of offsets in a classic half open range
    const SLICE_SIZE : usize = 2;

    let initial_slice : [usize ; SLICE_SIZE] = [0,routine_with_arguments.len()];
    // call stack is a concatination of the routine call path, the offsets describe a half open range for each neighboring pair of offsets.
    let mut call_stack : CallStack = CallStack { data: Vec::from(routine_with_arguments), offsets : Vec::from(initial_slice) };

    'routine : loop {

      core::debug_assert!(call_stack.offsets.len() >= SLICE_SIZE);

      let popped_value : Option<BytesTrieMap<()>> = 'find_memo : {
        
        let len   = call_stack.offsets.len();
        let start = call_stack.offsets[len-SLICE_SIZE];
        let end   = call_stack.offsets[len-(SLICE_SIZE-1)];
        let routine_path = &call_stack.data[start..end];
        
        let rz = self.memo.read_zipper_at_path(routine_path);
        let Some(m) = rz.make_map() else { break 'find_memo None; };

        if call_stack.offsets.len() == SLICE_SIZE { return Ok(m)};

        // pop value (the routine and args)
        call_stack.data.truncate(end);
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

        let new_record = RoutineActivationRecord{
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
        macro_rules! const_path {() => { &const_paths_store[const_arg.offset .. const_arg.offset + const_arg.len]};}

        match op {
            Op::Empty                => { // should be a no-op
                                          core::debug_assert!(space_reg[*program_counter].is_empty())
                                        },

            Op::Call                 => { let [arg_0 /* the whole path must first be concatted with all args */, ..] = input_registers;
                                          let path = &path_buffer[path_reg[arg_0 as usize].as_range()];
                                          if let Some(memo) =  self.memo.read_zipper_at_path(path).make_map() {
                                            // if we can get the value now without running a full routine
                                            space_reg[*program_counter] = memo;

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
                                            
                                            // push to call stack
                                            call_stack.data.extend_from_slice(path);
                                            call_stack.offsets.push(call_stack.data.len());
                                            
                                            // save the current continuation
                                            wz.set_value(record);
                                            
                                            // we want to skip bumping the program counter, it should only be advanced when we sucessfully call the routine
                                            continue 'routine                                            
                                          }
                                        },


            Op::Singleton            => { let [arg_0,..] = input_registers;
                                          let prefix = &path_buffer[ path_reg[arg_0 as usize].as_range() ];
                                          
                                          space_reg[*program_counter] = BytesTrieMap::new();
                                          let mut wz = space_reg[*program_counter].write_zipper_at_path(prefix);
                                          wz.set_value(());
                                        },

            Op::Union                => binary_space_op!{join},
            Op::Intersection         => binary_space_op!{meet},
            Op::Subtraction          => binary_space_op!{subtract},
            Op::Restriction          => binary_space_op!{restrict},


            Op::Wrap                 => { let [arg_0 /* Space */, arg_1 /* Path */, .. ] = input_registers;
                                          let prefix = &path_buffer[ path_reg[arg_1 as usize].as_range() ];
                                          
                                          let mut out = BytesTrieMap::new();
                                          out.write_zipper_at_path(prefix).graft_map(space_reg[arg_0 as usize].clone());
                                          
                                          space_reg[*program_counter] = out;
                                        },

            Op::Unwrap               => { let [arg_0 /* Space */, arg_1 /* Path */, .. ] = input_registers;
                                          let prefix = &path_buffer[ path_reg[arg_1 as usize].as_range() ];
                                          
                                          let Some(out) = space_reg[arg_0 as usize].read_zipper_at_borrowed_path(prefix).make_map() else { return Err(RoutineError_::RoutineMalformed((call_stack, *program_counter))); };
                                          
                                          space_reg[*program_counter] = out;
                                        },

            Op::DropHead             => { let [arg_0, .. ] = input_registers;
                                          let mut out = space_reg[arg_0 as usize].clone();
                                          let mut wz = out.write_zipper();

                                          let mask = wz.child_mask();

                                          let mut it = CfIter::new(&mask);
                                          
                                          while let Some(b) = it.next() {
                                            if !Interpreter::is_length_byte(b) || b == 0 {continue;}
                                            assert!(wz.descend_to(&[b]));
                                            wz.drop_head(b as usize);
                                            assert!(wz.ascend(1));
                                          }
                                          wz.drop_head(1);
                                          drop(wz);
                                          space_reg[*program_counter] = out;
                                        },

            Op::ExtractPathRef       => { let old_len = path_buffer.len();
                                          
                                          let path = if let Some(Subroutine { read_zipper, .. }) = subroutine_stack.last() {
                                            read_zipper.path()
                                          } else {
                                            const_path!()
                                          };

                                          path_buffer.extend_from_slice(path);
                                          path_reg[*program_counter] = PathStoreReference { offset : old_len, len : path.len() };
                                        },

            Op::ExtractSpaceMention  => { let Some(out) = ( if let Some(Subroutine { read_zipper, .. }) = subroutine_stack.last() {
                                                              read_zipper.make_map()
                                                            } else {
                                                              self.memo.read_zipper_at_borrowed_path(const_path!()).make_map() 
                                                            }
                                                          )
                                          else { return Err(RoutineError_::ValueWasNotMemoed((call_stack, *program_counter))); };

                                          
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

                                          path_buffer.extend_from_within( prefix_ref.as_range() );
                                          path_buffer.extend_from_within( suffix_ref.as_range() );

                                          path_reg[*program_counter] = PathStoreReference { offset : old_len, len : added_len };
                                        },



            Op::IterSubRoutine       => 'iter : { let [arg_0/* jump point */, arg_1 /* space */, ..] = input_registers;
                                          let zipper_space = space_reg[arg_1 as usize].clone();
                                          let mut read_zipper = zipper_space.clone().into_read_zipper(&[]);

                                          let mask = read_zipper.child_mask();
                                          let mut iter = CfIter::new(&mask);

                                          let Some(prefix_first_byte) = iter.next() else {
                                            space_reg[*program_counter] = BytesTrieMap::new();
                                            break 'iter;
                                          };

                                          let subroutine_start_counter = arg_0;

                                          Interpreter::decend_leading(&mut read_zipper, prefix_first_byte);
                                          subroutine_stack.push(Subroutine { previous_program_counter : *program_counter as Register, subroutine_start_counter, read_zipper, iter, prefix_first_byte, zipper_space });
                                          *program_counter=arg_0 as usize;
                                          continue 'subroutine; // skip the program counter increment
                                        },

            Op::Exit                 => match subroutine_stack.pop() {
                                          None => { let ret = core::mem::replace(&mut space_reg[*program_counter-1], BytesTrieMap::new());
                                                    self.memo.write_zipper_at_path(routine_with_arguments).graft_map(ret.clone());
                                                    return Ok(ret);
                                                  }
                                          Some(Subroutine { mut iter, zipper_space, mut read_zipper, subroutine_start_counter, previous_program_counter, prefix_first_byte })
                                               => { // union value into parent
                                                    let tmp = core::mem::replace(&mut space_reg[*program_counter-1], BytesTrieMap::new());
                                                    space_reg[previous_program_counter as usize].join_into(tmp);
                                                    
                                                    if Interpreter::is_length_byte(prefix_first_byte) && read_zipper.to_next_k_path(prefix_first_byte as usize) {
                                                      subroutine_stack.push(Subroutine { read_zipper, iter, subroutine_start_counter, previous_program_counter, prefix_first_byte, zipper_space });
                                                      *program_counter = subroutine_start_counter as usize;
                                                    } else {
                                                      match iter.next() {
                                                        Some(byte) => { Interpreter::decend_leading(&mut read_zipper, byte);
                                                                        subroutine_stack.push(Subroutine { read_zipper, iter, subroutine_start_counter, previous_program_counter, prefix_first_byte : byte, zipper_space });
                                                                        *program_counter = subroutine_start_counter as usize;
                                                                      }
                                                        None       => *program_counter = previous_program_counter as usize,
                                                      }
                                                    }
                                                  }
                                        },
        }

        *program_counter += 1;
      }
    }
  }
  
  fn is_length_byte(byte : u8)-> bool {0b_00_11_11_11 >= byte /* note the first nibble is 00 */ }

  fn decend_leading(rz : &mut pathmap::zipper::ReadZipperOwned<()>, prefix_first_byte : u8) {
    rz.reset();
    core::assert!(rz.descend_to(&[prefix_first_byte]));
    if Interpreter::is_length_byte(prefix_first_byte)  {
      core::assert!(rz.descend_first_k_path(prefix_first_byte as usize));
    }
  }
}
