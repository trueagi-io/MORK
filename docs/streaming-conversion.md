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

```sh
mork convert paths act output.paths output.act --memory-mib 1024
```

The final stage pushes each path into `ACTOutputStream`; it never restores a
Space. Paths must be strictly increasing (duplicates and descending paths are
errors). The ACT builder keeps the current path's trie frontier and a bounded
line-reuse cache. `--memory-mib` sets the cache limits to budget/8 bytes of line
data and budget/256 entries, and limits individual input paths to budget/16
bytes. Cache allocation capacity and metadata, the frontier (proportional to
path depth), the 4 MiB output buffer and codec/runtime overhead are additional.
These limits bound memory independently of total input size; they are not an
OS-enforced RSS limit. A finished ACT is memory-mapped and immediately dropped,
without scanning it into RAM.

This requires the local PathMap dependency's `ACTOutputStream::with_cache_limits`
API, added in PathMap commit `d775f49`. Previously its line cache grew with the
input. The conversion commit also fixes a pre-existing single-source peephole
that incorrectly handled `(I (ACT ...))` as an in-memory fact, preventing some
variable queries from reaching the ACT source.

Query an ACT on disk using the ACT source, for example with `output.act`:

```lisp
(exec 0 (I (ACT output (in $index $gate))) (, (found $index $gate)))
```

```sh
MORK_ACT_PATH=/directory/containing/act mork run query.mm2 results.mm2
```

The ACT source maps the file; it does not restore it to an in-memory PathMap.
Only accessed pages need to become resident. A complete scan can, of course,
make all file pages resident in the OS page cache.

## Validation and measurement

```sh
cargo test -p mork --lib convert::tests
cargo test --manifest-path ../PathMap/Cargo.toml --test act_stream_cache --features arena_compact,nightly
python3 kernel/bench_scripts/streaming_conversion.py /path/to/input.mm2 --memory-mib 1024
cargo run --release -p mork --example verify_streaming_conversion -- \
  target/conversion-benchmark/bean.paths target/conversion-benchmark/bean.act
```

The benchmark script records wall time and native peak RSS for each child
process (`/usr/bin/time -l` on macOS, `-v` on Linux), total consecutive wall time,
output sizes, commands, and native logs. Pipeline peak is the maximum stage RSS,
not their sum, since stages run sequentially. Build time and verification are
excluded. Outputs default to `target/conversion-benchmark/`.

The verifier compares every sorted path with an independent ACT traversal and
performs one point lookup per million paths. Tests also cover parser agreement
with MORK, multiline/quoted input, malformed input, forced multi-run sorting,
cache eviction, atomic output publication, empty and prefix paths, and a MORK
variable query against the generated ACT.

## Full-file benchmark (2026-10-02)

Input: `~/bean_full_pgo_h10_from_h3_sort_neg_iter5_equiv.lut3.mm2`,
2,541,424,781 bytes (2.37 GiB), 49,512,659 expressions, all unique.
Release build, macOS arm64 with 16 GiB RAM, `--memory-mib 1024`.
One consecutive run with normal OS caching (no cold-cache flush):

| Stage | Wall time | Peak RSS | Output bytes |
| --- | ---: | ---: | ---: |
| mm2-upaths | 48.34 s | 4.27 MiB | 427,649,091 |
| upaths-paths | 61.63 s | 465.05 MiB | 510,095,667 |
| paths-act | 11.11 s | 509.50 MiB | 1,809,219,049 |
| **Total** | **121.07 s** | **509.50 MiB** | |

All 49,512,659 sorted paths were checked against a complete on-disk ACT
traversal, with 50 sampled point lookups. An actual MORK ACT-source query also
returned exactly `(found 0 g0)` through `(found 111 g111)`; a known ground fact
matched and a deliberately absent fact did not. That selective query took
0.34 seconds and 4.56 MiB peak RSS. Full traversal can make the entire ACT's
file-backed mapping resident; validation is excluded from conversion timing
and peak RSS.

Artifacts and native logs are in `target/conversion-benchmark/`, including
`bean.upaths`, `bean.paths`, `bean.act`, `results.json`, and query outputs.
Eight MORK conversion tests and the isolated PathMap cache integration test
pass. PathMap's broader unit-test binary could not compile because of existing
ambiguous empty-slice comparisons in `zipper.rs` and `product_zipper.rs`.
