
# MeTTa Optimal Reduction Kernel

**A blazing fast hypergraph processing kernel for Hyperon**

MORK seeks to retrofit Hyperon with a state-of-the-art graph database and a specialized zipper-based multi-threaded virtual machine to provide speedy MeTTa evaluation across the full range of Space sizes and topologies.

By rearchitecting certain Hyperon bottlenecks, MORK has the potential to accelerate important use cases by thousands to millions of times.  That kind of speedup represents a qualitative jump in capabilities.  It's the difference between running a training step vs. finishing the training in the same amount of time.  It's the difference between a thousand input samples vs. millions, or a crocodile's brain vs. a human's.  Deep learning has advanced due in part to the software platforms that exposed the full capabilities of underlying hardware, and we hope Hyperon + MORK can help do that for symbolic AI.

## Wiki
[The wiki](https://github.com/trueagi-io/MORK/wiki#where-to-start) is where you find examples, tutorials, and more info about both the formalism and implementation.

## Trying it out
If you're looking for the MORK server, use the [server branch](https://github.com/trueagi-io/MORK/tree/server).

If you're looking for the MORK command line utility, run `cargo build --release` in `/kernel`; you'll need a nightly compiler `rustup toolchain install nightly`.
