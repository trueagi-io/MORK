use pathmap::{trie_map::BytesTrieMap, zipper::{WriteZipper, Zipper}};

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

struct Routine {
  instructions : Vec<Instruction>,
}

/// this will get replaced but for now it marks intent at a root node that what follows is a certain type
#[derive(Clone, Copy)]
enum Type{
  Space,
  Path,
}


impl Routine {

  /// in order for this to run efficiently, we require that the zippers are already at their zipper root ()
  fn run<'a1, 'a2, 'b1, 'b2>(
    &self,
    register_zipper : &mut pathmap::zipper::WriteZipperTracked<'a1, 'a2, Type>, 
    state_zipper    : &mut pathmap::zipper::WriteZipperTracked<'b1, 'b2, Type>,
  ) {
    #![cfg_attr(rustfmt, rustfmt::skip)]
    
    core::debug_assert!(register_zipper.at_root());
    core::debug_assert!(state_zipper.at_root());
    
    for (inst, Instruction { out_register, path, op, const_arg, input_registers }) in (&self.instructions).iter().enumerate() {
      macro_rules! reg_path {(let $PATH:ident = $REG:expr) => {
        let _ : Register = $REG; // type check
        let tmp_ = $REG.to_ne_bytes();
        let $PATH = tmp_.as_slice();
      };}

      let instruction = inst as Register;
      reg_path!{let out_path = instruction}

      if path

      match op {
        Op::Empty               => { register_zipper.descend_to(out_path);
                                     register_zipper.set_value(Type::Space);
                                     while register_zipper.ascend_until() {}
                                   }
        Op::Call                => todo!("!"),
        Op::Mention             => todo!("!"),
        Op::Singleton           => { let &[arg_0,..] = input_registers;
                                     reg_path!{let arg_0_path = arg_0}
                                     let mut reg_zh = register_zipper.zipper_head();
                                     let arg_0_z    = reg_zh.read_zipper_at_borrowed_path(arg_0_path);
                                     

                                     let out_z = reg_zh.write_zipper_at_exclusive_path(out_path);

                                     state_zipper.

                                   }
        Op::Literal             => todo!(),
        Op::Union               => todo!(),
        Op::Intersection        => todo!(),
        Op::Subtraction         => todo!(),
        Op::Restriction         => todo!(),
        Op::Composition         => todo!(),
        Op::Wrap                => todo!(),
        Op::Unwrap              => todo!(),
        Op::DropHead            => todo!(),
        Op::Transformation      => todo!(),
        Op::Iteration           => todo!(),
        Op::ExtractPathRef      => todo!(),
        Op::ExtractSpaceMention => todo!(),
        Op::Constant            => todo!(),
        Op::Concat              => todo!(),
        Op::LeftResidual        => todo!(),
        Op::RightResidual       => todo!(),
      }
    }

    while register_zipper.ascend_until() {}
    while state_zipper.ascend_until() {}
  }
}

type Register = u32;

struct Instruction { 

  out_register    : Register,
  path            : Path,
  op              : Op,
  const_arg       : PathValue,
  input_registers : [Register;4], 
}


enum Path {
  Deref(PathRef),
  Constant(PathValue),
  Concat((Box<Self>,Box<Self>))
}

struct SpaceMention(Str);
struct RoutinePtr(Str);


struct PathValue(Vec<PathItem>);

enum PathItem {
  Symbol(Str),
  Variable(Str),
  Arity(usize)
}
struct PathRef(Str);

type Str = std::sync::Arc<str>;

#[test]
fn h() {
  let mut t = BytesTrieMap::new();
  t.insert(b"aaa", 1);
  t.insert(b"aab", 2);
  t.insert(b"aac", 3);

  '_zippers : {
    let mut zh = t.zipper_head();
    let mut src = zh.write_zipper_at_exclusive_path(b"aa");
    let mut dest = zh.write_zipper_at_exclusive_path(b"ab");
    
    dest.graft(&src);
  }

  let c = t.iter().map(|(v,i)| (v.clone(), *i)).collect::<Vec<_>>();
  println!("{:?}", c)
  
}