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
