This tutorial aims to walk through how a program can be constructed in MM2, focusing on small examples and building up to a non trivial program. The program is then further modified to scale to larger more involved programming.

# Tutorial Files
All the files referenced in the tutorial are to be found in the folder `structuring_code/`

# Files in `structuring_code/`
- ## The tutorial text files
  - `structuring_code_00_Intro_and_Contents.md`          
    - This markdown file
  - `structuring_code_01_Setup.md`             
    - Setting up an environment to run MM2 with the MORK CLI.
  - `structuring_code_02_Basics.md`            
    - Predication
    - Exec Syntax
    - Priorities
    - Sources/Sinks
  - `structuring_code_03_Set_Ops.md`           
    - Design of generic execs definitions
    - unification
    - Set operation examples
  - `structuring_code_04_Going_Wide.md`        
    - Tables as finite functions
    - Modifying data representation for pattern matching
    - Paths as disjoint predications
    - recursive execs
    - terminating execs
    - Fork/Join
    - making a main loop
  - `structuring_code_05_Going_Wide_Macros.md`
    - generalizing fork/join
    - specializing at startup with macro expansion
  - `structuring_code_06_Going_Wide_Larger_Programs.md`
    - adding multiple inputs and output locations
    - running multiple instances of the same process type
    - clearing data at runtime to reduce memory overhead
  - `structuring_code_07_Going_Wide_2_Programs.md`
    - define another recursive fold with another finite function
    - reusing the generic macro code for the new fold
    - modify the inputs to include the new data to evaluate in to the main loop
  - `structuring_code_08_In_Closing.md`
    - take stock of the subjects that were covered
    - Ideas to consider.
  - `structuring_code_09_Rust_Extra.md`
    - Introduction to a Rust template to experiment with the internals.


- ## `.mm2` files
  - Setup 
    - `Setup_Hello_World.mm2`
      - A basic file to see if the tutorial environment is set up.

  - Basics
    - `Basics_Sources_Sinks.mm2`
      - A basic example to showcase pattern sources and template sinks.

  - Set Operations
    - `Set_Ops_01_Hardcoded_Locations.mm2`
      - Runs an exec as a function where the argument and return locations are hardcoded.
    - `Set_Ops_02_Parameterized_Locations.mm2`
      - The initial exec uses a "definition" in the database to construct a function with the right argument and return locations.
    - `Set_Ops_03_Union.mm2` | `Set_Ops_04_Intersection.mm2` | `Set_Ops_05_Difference.mm2` | `Set_Ops_06_Symmetric_Difference.mm2`
      - examples that used the parameterized location pattern to implement set operations.

  - Going Wide
    - `Going_Wide_01_Recursive.mm2`
      - The most basic exec that constructs itself.
    - `Going_Wide_02_Halts.mm2`
      - A recursive exec that eventually fails when decrementing a Peano number to match, ending the recursion.
    - `Going_Wide_03.mm2`
      - A program that takes a recursive expression, splits it into paths, then evaluates with by joining results with a finite function
    - `Going_Wide_11_Macros.mm2`
      - a modified `Going_Wide_03.mm2` by using using partial evaluation to allow the forks and joins to be generic, but specialize them before the main loop.
    - `Going_Wide_21_Larger_Programs.mm2`
      - a modified `Going_Wide_11_Macros.mm2` to support multiple inputs and to use less memory.
    - `Going_Wide_31_Two_Programs.mm2`
      - a modified `Going_Wide_21_Larger_Programs.mm2` to support running a second process type using the same fork/join logic.

- ## `mork_playground`
  - a rust binary crate program that serves as a template for basic file IO with an embedded MORK instance.
  - mentioned in `structuring_code_09_Rust_Extra.md`
