
# MeTTa Optimal Reduction Kernel [WIP]

**A blazing fast hypergraph processing kernel for Hyperon**

MORK seeks to retrofit Hyperon with a state-of-the-art graph database and a specialized zipper-based multi-threaded virtual machine to provide speedy MeTTa evaluation across the full range of Space sizes and topologies.

By rearchitecting certain Hyperon bottlenecks, MORK has the potential to accelerate important use cases by thousands to millions of times.  That kind of speedup represents a qualitative jump in capabilities.  It's the difference between running a training step vs. finishing the training in the same amount of time.  It's the difference between a thousand input samples vs. millions, or a crocodile's brain vs. a human's.  Deep learning has advanced due in part to the software platforms that exposed the full capabilities of underlying hardware, and we hope Hyperon + MORK can help do that for symbolic AI.

## Roadmap

### Deliverable 1 - Graph database with efficient queries

Deliverable 1 is a set of data structures for a fast, scalable and memory-efficient graph database that runs on a single machine.

- Expression queries\
Support for querying by any structured key type, e.g. expression structure, etc. (See [Triemaps that match](https://arxiv.org/abs/2302.08775))

- Efficient space-wide operations\
Full [relational algebra](https://en.wikipedia.org/wiki/Relational_algebra#Joins_and_join-like_operators) support. I.e. union, intersection, and set subtraction ops across entire spaces, performed using lazy or constant-time operations.

- Matching and unification\
Support for bidirectional pattern matching and unification of S-expressions with spaces by translating slow declarative "shape matching" queries into native queries

- Billions of atoms\
A high end workstation should be able to load, query, and transform a space with over a billion atoms without running out of memory or hanging for hours

- JSON interop\
Load data from json and querying using (a subset of) [JSONPath](https://datatracker.ietf.org/doc/rfc9535/) 

#### Tasks:

- [x] Definition of Expr type structures to represent S-expressions efficiently in memory with high cache locality and searchability

- [ ] Derivation of a triemap over a range of algebraic data structures, (excluding dependent typing).  See [Multiplate](https://wiki.haskell.org/Multiplate)

- [x] Fast and memory-efficient S-expression triemap to support MeTTa atoms

- [ ] Union, intersection, and subtract ops for S-expression triemap (and other derived triemap types) implemented with algorithms that have optimal scaling properties (based on current SOTA)

- [x] Fast primitive triemap implementing the space-wide ops (union, intersection, and subtract), based on ([Ring of Sets](https://en.wikipedia.org/wiki/Ring_of_sets))

- [x] Automatic translation of slow declarative "shape matching" queries into more classical database queries, to support bidirectional pattern matching and unification

- [ ] Streaming JSON parser (completed), and JSONPath query engine

- [ ] ~~Take first place (or at least crack the top 3) in the [One Billion Row Challenge](https://github.com/gunnarmorling/1brc)~~ The datastructure is not the bottleneck in this situation.

### Deliverable 2 - Multi-threaded zipper machine

Deliverable 2 is a model of computation and a multi-threaded virtual machine to run it, utilizing the data structures from deliverable 1.

- "Zipper Abstract Machine"\
Inspired by Prolog's [Warren Abstract Machine](https://en.wikipedia.org/wiki/Warren_Abstract_Machine), exposes spaces as native computational primitives and [Zippers](https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf) as cursors to encapsulate runtime state

- Logical inference at scale\
Decompose inference steps for parallel execution and an efficient fast-path for light-weight high-frequency inference

- Basic inference control\
Expands upon MeTTa's support for nondeterminism with machine-level operations for prioritization and pruning of exploration and evaluation

- Near-linear scaling with cores\
Fearless concurrency based on isolation guarantees to allow scaling without hitting scaling walls caused by central bottlenecks

#### Tasks:

- [x] Define (mathematically) the model of computation and the specification of the ZAM behavior

- [ ] Implement the ZAM in Rust leveraging an existing framework

- [ ] Benchmark and optimize towards maximizing serial-inference-operations-per-second

- [ ] Benchmark and optimize towards parallel decomposed operation throughput

- [ ] Saturate the compute on a 128 core x86 test machine, with each incremental core delivering concomitant incremental performance for a use-case / workload with enough concurrency

### Deliverable 3 - MeTTa language support

Deliverable 3 implements a fully-functional interpreter of the high-level MeTTa language on top of the ZAM from deliverable 2, with support for native grounded operations and primitives.

- ZAM based interpreter for logical inference\
Interprets code to perform the full range of tasks and use cases that MeTTa can currently execute, although some adaptation of the MeTTa code may be required

- Enable complex programs\
Supports enough functionality to enabling long-lived and general-purpose codebases that live along-side or within massive datasets

- Grounded Interfaces\
Provides API hooks to extend MeTTa functionality with native operations, while taking care to preserve the performance characteristics of the triemap primitives as much as is possible using bidirectional transformation endpoints

- Integrated Inference Control\
Augments space-wide operations with sampling and enriching strategies using the inference control mechanisms built on the ZAM.

#### Tasks:

- [ ] Map each operation in minimal MeTTa into ZAM operations

- [ ] Define API entry points to express grounded operations, and permit them to be inverted into queries

- [ ] Implement fallback paths to materialize transformed spaces when grounded operations cannot be inverted, and develop graceful strategies to prevent these fallbacks from compromising the usability of the system overall

### Deliverable 4 - Adapt hyperon clients to use MORK

Deliverable 4 ports and adapts the MORK kernel into the  hyperon-experimental project, exposing a rich set of features and interface bindings for end-users.

- Python integration\
Update hyperon-experimental’s Python bindings to allow the MeTTa interpreter to be embedded inside Python, and allow the use of Python to define native grounded objects

- C API\
Run MeTTa from C/C++, and use C/C++ to implement native grounded objects

- WASM API\
Integrate a bridge to allow grounded objects to be implemented using WASM. 

- Complete MeTTa stdlib support\
Arithmetic and string operations, etc.

- Modules\
Isolated and composable units of functionality

- Package management\
Load packages implemented with any combination of MeTTa, Python, or WASM from disk, git, or a central repository

## General desiderata

- Software deliverables built to target [WebAssembly](https://webassembly.org/) as well as native (Linux + Mac) x (x86-64 + AArch64) platform targets

- NoCopy binary formats where possible, to allow fast loading of large files using mmap, and sharing across virtual-machine boundaries without a serialize-deserialize translation cost

## Possible future directions for MORK, beyond the 4 deliverables

Currently we don't have these items as specific deliverables, but these are directions in which we may opt to continue the work.

- Native compilation of MeTTa to machine code

- Support for specialized many-core architectures and/or accelerators

- Distribution across multiple machines on a network

## Additional reference

- [MeTTa](https://metta-lang.dev/)\
Official resources for the MeTTa language

- [Atomspace](https://github.com/opencog/atomspace)\
An existing hypergraph processing system that served as a progenitor Hyperon and MeTTa

- [Hyperon Experimental](https://github.com/trueagi-io/hyperon-experimental)\
The most feature-complete implementation of the MeTTa language

- [Triemaps that match](https://arxiv.org/abs/2302.08775)\
A paper from Simon Peyton Jones describing one of the foundational patterns MORK will use

- [CZ2](https://github.com/Adam-Vandervorst/CZ2)\
Some experiments in Scala demonstrating the scaling characteristics of the triemap structures

- [Interacting Trie-Maps](https://github.com/F1R3FLY-io/itm/)\
An implementation of triemap interactions in Scala, serving as a proof-of-concept for ZAM and concurrency model

- [Triemap derivation for Rust](https://github.com/mkovaxx/triemap-rs)\
A crate exposing a macro to derive a triemap over a Rust enum or struct type

