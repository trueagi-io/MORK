# MeTTa Optimal Reduction Kernel [WIP]

**A kernel for hypergraph processing.**

For an existing hypergraph processing system, please refer to [Atomspace](https://github.com/opencog/atomspace).\
For an implementation of the MeTTa language, please refer to [Hyperon Experimental](https://github.com/trueagi-io/hyperon-experimental).

Further references for now:
- Query and processing using and optimal reduction implementation of [MeTTa](https://metta-lang.dev/).
- Basic data-structure based on [Triemaps that match](https://arxiv.org/abs/2302.08775).
- Informed by the [CZ2](https://github.com/Adam-Vandervorst/CZ2) experiments.
- Implementing [Interacting Trie-Maps](https://github.com/F1R3FLY-io/itm/).
- Using [automatic triemap derivation for Rust](https://github.com/mkovaxx/triemap-rs).

## Roadmap
- [ ] Efficient Datastore\
Fast and memory-efficient S-expression map 

- [ ] Basic Database\
Scalable union, intersection, and subtract ([Ring of Sets](https://en.wikipedia.org/wiki/Ring_of_sets)) for triemaps

- [ ] S-expression querying\
Automatic translation of slow declarative "shape matching" queries into more classical database querying, supporting bidirectional pattern matching and unification

- [ ] Data Processing\
Efficient integration of (bidirectional) grounded functions (for e.g. integer arithmetic and string operations) into queries

- [ ] Processing of data by data\
Support the "[Zipper](https://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf) Abstract Machine", the [Warren Abstract Machine](https://en.wikipedia.org/wiki/Warren_Abstract_Machine) with triemap operations

- [ ] Support the MeTTa language\
Provide an implementation of the high-level MeTTa language in terms of the ZAM, enabling long-lived and general-purpose codebases to live along massive datasets

- [ ] Parallel processing for MeTTa\
Implement a model of fearless concurrency via ITM-based isolation guarantees, leveraging multicore systems

## Complementary
- [ ] Compile to WASM\
Support [WebAssembly](https://webassembly.org/) as a compilation target

- [ ] Efficient Datastore for any type\
Automatic derivation of [triemaps](https://arxiv.org/pdf/2302.08775) for any [Multiplate](https://wiki.haskell.org/Multiplate), yielding fast and memory-efficient maps for any algebraic data structure in programming (excluding dependent typing)

- [ ] Database\
Full [relational algebra](https://en.wikipedia.org/wiki/Relational_algebra#Joins_and_join-like_operators) support, allowing classical database querying for any structured key type

- [ ] JSON interop\
Combined parsing of JSON and construction of the Triemap database and querying using [JSONPath](https://datatracker.ietf.org/doc/rfc9535/) 
