# Streaming conversions

Build with `cargo build --release -p mork` (without the `interning` feature).

```sh
mork convert mm2 upaths input.mm2 output.upaths
```

`.upaths` is PathMap's `.paths` wire format: a zlib stream of little-endian
32-bit path lengths followed by path bytes. It preserves input order and
repeated atoms. Conversion uses buffered input, without mapping the source or
constructing a Space. Memory depends on the largest expression/token, not the
file size. Symbols use MORK's inline encoding, including its 63-byte symbol
truncation. Variables are scoped to each top-level expression.

`metta upaths` is an alias. The legacy `PATTERN TEMPLATE INPUT [OUTPUT]`
arguments still work; streaming conversion requires `$` and `_1`. With the
short `INPUT [OUTPUT]` syntax these are implicit. Omitting OUTPUT replaces the
input extension. Output is staged in its destination directory and renamed
only on success, so errors leave an existing destination intact.

```sh
mork convert upaths paths input.upaths output.paths --memory-mib 1024 --temp-dir /tmp
```

Sorting compares raw path bytes and removes duplicates, as a PathMap would.
It writes sorted runs to disk and merges them in pairs. Both the run metadata
(at most 64 levels) and open file count are bounded. Completed runs are removed
as they are merged, and temporary files are cleaned up on success or error.
Allow scratch space for uncompressed path records and a merge output; peak
scratch use can approach twice the uncompressed input size, plus final output.

`--memory-mib` defaults to 1024 and must be at least 1. It bounds record buffers
and sorting workspace; codec state, allocator and runtime overhead are extra.
Half the budget is reserved for the sort arena and indices, leaving room for
input and merge buffers. A single path may use at most 1/16 of the budget;
oversize records are rejected with an instruction to increase the budget.
Malformed/truncated compressed streams, incomplete records, and trailing data
are rejected before publishing the output.
