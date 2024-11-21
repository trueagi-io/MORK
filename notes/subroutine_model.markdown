
Rules for Routines:
  - the Routine is initialized with a fixed size "register stack" and "subroutine stack"
  - the program counter points the current instruction
  - The "subroutine stack" stack capacity is 
    ```
         number of subroutines 
      >= the capacity of the stack 
      >= max subroutine call depth (this should be a known constant)
    ```
  - The "register stack" has capacity equal to the number of instructions.
    - it might sound confusing that the registers are fused to a stack, that is because it behaves like both!
    - it behaves like registers becasue it allows random access
    - it behaves like a stack because intructions append new values 
      relative to the program counter as an index.
    - it also behaves like a stack at returning from a 
      subroutine makes old values "clobbered" (don't cheat!).
  - calling a subroutine pushes the current instruction.

Rules for Subroutines: 
  - Subroutines work like a stack, but they never move
  - calling a Sub routine implicitly defines a range (that could be checked statically) 
    where the values between the call site and the subroutine first instruction define a half open range of 
    unreadble registers (of the same index as instructions)
  - A subroutine can only be called if they are __below__ the current call site
  - returning from a subroutine "clobbers" it's registers.
  - Subroutines are not recursive!
  - Exit.Subroutine will union the results of the last computed value of a Subroutine to the caller
  - questions
    - Subroutines should have arguments? (this could help with reducing code size, but it defeats the goal of treating it as "just a block")

Rules for Instructions:
  - They always refer to values above them lexically

the ` ;; ` and `.label` parts are purely for human readability.
```
.offset_to_instruction_start _
" ... " ; static memory

;; The entry point
.label AUNT ; "^"
  0| ExtractSpaceMention | (family)  | (   ,   ,   ,   ) : space
  1| ExtractSpaceMention | (people)  | (   ,   ,   ,   ) : space
  2| Iter                | (person)  | (  6,   ,   ,   ) : space ; 6 == PERSON
  3| Constant            | (Aunt)    | (   ,   ,   ,   ) : path 
  4| Wrap                |           | (  2,  3,   ,   ) : space
  5| Exit.Routine        |

;; implicitly we take registers as arguments 0..=1, registers 2..=5 are considered clobbered
.label PERSON ; "^.person"
  6| NextPath            |           | (  1,   ,   ,   ) : path
  7| NextSubspace        |           | (  1,   ,   ,   ) : space
  8| Constant            | (parent)  | (   ,   ,   ,   ) : path 
  9| Unwrap              |           | (  0,  8,   ,   ) : space
 10| Constant            | (child)   | (   ,   ,   ,   ) : path 
 11| Unwrap              |           | (  0, 10,   ,   ) : space
 12| Constant            | (child)   | (   ,   ,   ,   ) : path
 13| Concat              |           | ( 12,  6,   ,   ) : path 
 14| Unwrap              |           | (  0, 13,   ,   ) : space
 15| Restriction         |           | ( 11, 14,   ,   ) : space
 16| DropHead            |           | ( 15,   ,   ,   ) : space
 17| Restriction         |           | (  9, 16,   ,   ) : space
 18| DropHead            |           | ( 17,   ,   ,   ) : space
 19| Constant            | (child)   | (   ,   ,   ,   ) : path 
 20| Concat              |           | ( 19,  6,   ,   ) : path 
 21| Unwrap              |           | (  0, 20,   ,   ) : space
 22| Subtraction         |           | ( 18, 21,   ,   ) : space
 23| Constant            | (female)  | (   ,   ,   ,   ) : path 
 24| Unwrap              |           | (  0, 23,   ,   ) : space
 25| Intersection        |           | ( 22, 24,   ,   ) : space
 26| Wrap                |           | ( 25,  6,   ,   ) : space
 27| Exit.Subroutine
```





```
 $x.y =


.label ENTRY ; "^" ;; The entry point
 0 ExtractSpaceMention (family) ()        : space
 1 Constant            (parent) ()        : path
 2 Unwrap                       (0, 1)    : space
 3 Iter                         ($x == 7)         
 4 Constant             (child) ()        : path
 5 Wrap                         (3, 4)    : space
 6 Exit.Routine

.label $x ; "^.x" ;; implicit args 0..=2, clobbered 3..=6
 7 NextPath               (2)           : path
 8 NextSubspace           (2)           : space
 9 Iter                   ($x.y == 11)
10 Exit.Subroutine

.label $x.y : "^.x.y" ;; implicit args 0..=1 and 7..=8, clobbered 3..=6 and 9..=10
11 NextPath            (8)               : path
12 Concat              (?("ask Adam"), 3): path
13 Singleton           (12)              : space
14 Exit.Subroutine
```








```
 
 0  ^     ExtractSpaceMention(family)(): space
 1  ^     Constant(parent)(): path
 2  ^     Unwrap(0, 1): space
          
 3  ^.x   NextPath(2): path
 4  ^.x   NextSubspace(2): space
      
 6  ^.x.y NextPath(4): path
 7  ^.x.y Concat(5, 3): path
 8  ^.x.y Singleton(7): space

 9  ^     Constant(child)(): path
 10 ^     Wrap(8, 9): space
```
























```
val out: WZ = ???
val family: RZ = arg(0)                  // 0  ^     ExtractSpaceMention(family)(): space
val parent_path = "parent".toBytes       // 1  ^     Constant(parent)(): path
family.descend_to(parent_path)           // 2  ^     Unwrap(0, 1): space
iter_symbol(family, (oloc) =>                        
  val x_path = oloc.path()               // 3  ^.x   NextPath(2): path
  val ys_subspace = oloc.clone()         // 4  ^.x   NextSubspace(2): space
  iter_symbol(ys_subspace, (iloc) =>           
    val y_path = iloc.path()             // 6  ^.x.y NextPath(4): path
    val r_path = y_path.concat(x_path)   // 7  ^.x.y Concat(5, 3): path
    out.descend_to(r_path)               // 8  ^.x.y Singleton(7): space
  )                                      
)                                        
val child_path = "child".toBytes         // 9  ^     Constant(child)(): path
out.descend_to(child_path)               // 10 ^     Wrap(8, 9): space
```








```
 reg | path     | Op                  | const-arg | ssa-arg           | output type
+----+----------+---------------------+-----------+-----------------------
|  0 | ^        | ExtractSpaceMention | (family)  | (   ,   ,   ,   ) : space
|  1 | ^        | ExtractSpaceMention | (people)  | (   ,   ,   ,   ) : space
|  2 | ^.person | NextPath            |           | (  1,   ,   ,   ) : path 
|  3 | ^.person | NextSubspace        |           | (  1,   ,   ,   ) : space
|  4 | ^.person | Constant            | (parent)  | (   ,   ,   ,   ) : path 
|  5 | ^.person | Unwrap              |           | (  0,  4,   ,   ) : space
|  6 | ^.person | Constant            | (child)   | (   ,   ,   ,   ) : path 
|  7 | ^.person | Unwrap              |           | (  0,  6,   ,   ) : space
|  8 | ^.person | Constant            | (child)   | (   ,   ,   ,   ) : path 
|  9 | ^.person | Concat              |           | (  8,  2,   ,   ) : path 
| 10 | ^.person | Unwrap              |           | (  0,  9,   ,   ) : space
| 11 | ^.person | Restriction         |           | (  7, 10,   ,   ) : space
| 12 | ^.person | DropHead            |           | ( 11,   ,   ,   ) : space
| 13 | ^.person | Restriction         |           | (  5, 12,   ,   ) : space
| 14 | ^.person | DropHead            |           | ( 13,   ,   ,   ) : space
| 15 | ^.person | Constant            | (child)   | (   ,   ,   ,   ) : path 
| 16 | ^.person | Concat              |           | ( 15,  2,   ,   ) : path 
| 17 | ^.person | Unwrap              |           | (  0, 16,   ,   ) : space
| 18 | ^.person | Subtraction         |           | ( 14, 17,   ,   ) : space
| 19 | ^.person | Constant            | (female)  | (   ,   ,   ,   ) : path 
| 20 | ^.person | Unwrap              |           | (  0, 19,   ,   ) : space
| 21 | ^.person | Intersection        |           | ( 18, 20,   ,   ) : space
| 22 | ^.person | Wrap                |           | ( 21,  2,   ,   ) : space
| 23 | ^        | Constant            | (Aunt)    | (   ,   ,   ,   ) : path 
| 24 | ^        | Wrap                |           | ( 22, 23,   ,   ) : space
```