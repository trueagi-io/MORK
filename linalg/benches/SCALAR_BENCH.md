# Scalar transform throughput (`benches/scalar.rs`)

Times the full [`ScalarTransform`](../src/scalar.rs) op surface on a large
`Dense` array (default `1<<22` = 4.19 M elements), for `f32` and `f64`, on both
the default std-math backend and the Intel MKL VML backend (`intel-mkl`
feature). Reports net throughput (Melem/s, GB/s) with the per-iteration buffer
refresh subtracted out.

## Running

```sh
# std math (default)
cargo bench -p linalg --bench scalar

# Intel MKL VML
cargo bench -p linalg --bench scalar --features intel-mkl   # + the env from below
```

Env overrides: `SCALAR_N` (element count), `SCALAR_ITERS` (timed iterations).

### Getting MKL (no root needed)

The `mkl`/`mkl-devel` wheels ship `libmkl_rt` and its dependencies:

```sh
uv venv mklenv
uv pip install --python mklenv/bin/python mkl mkl-devel
LIB=$(pwd)/mklenv/lib
ln -sf libmkl_rt.so.3 $LIB/libmkl_rt.so     # linker wants the unversioned name

export RUSTFLAGS="-L native=$LIB"           # link time
export LD_LIBRARY_PATH=$LIB                  # run time
export MKL_THREADING_LAYER=SEQUENTIAL        # single-core, fair vs std; drop for threaded
```

## Representative results

64-core x86-64, 4.19 M elements. Throughput in **Melem/s** (higher is better).
"MKL-1T" forces `MKL_THREADING_LAYER=SEQUENTIAL`; "MKL-NT" lets VML thread.

### f32

| op    | std    | MKL-1T | MKL-NT | 1T speedup | notes |
|-------|-------:|-------:|-------:|-----------:|-------|
| sin   |  520.8 |  715.2 | 12971  | 1.4×       | VML   |
| cos   |  478.1 |  679.5 | 12966  | 1.4×       | VML   |
| tan   |  149.1 |  543.5 | 12669  | 3.6×       | VML   |
| asin  |  195.3 |  612.9 | 12500  | 3.1×       | VML   |
| acos  |  195.5 |  598.9 | 12832  | 3.1×       | VML   |
| atan  |  253.5 |  349.0 |  9554  | 1.4×       | VML   |
| cbrt  |  200.9 |  587.2 | 10928  | 2.9×       | VML   |
| ln    |  387.8 |  827.4 | 11856  | 2.1×       | VML   |
| exp   |  439.5 | 1024.3 | 12184  | 2.3×       | VML   |
| powf  |  166.5 |  297.1 |  8462  | 1.8×       | VML (`vsPowx`) |
| sqrt  | 3419.4 | 1695.9 | 12236  | 0.5×       | std uses the hardware `sqrt`; VML call is slower single-threaded |
| abs   | 3672.7 | 3311.2 | 12703  | 0.9×       | both memory-bound; std inlines |
| atan2 |   91.1 |   89.6 |    90  | —          | scalar in both (no scalar-broadcast VML kernel) |
| min/max/clamp/powi | ~3600 | ~2900 | ~3000 | — | scalar in both (memory-bound) |

### f64 (selected)

| op    | std   | MKL-1T | 1T speedup |
|-------|------:|-------:|-----------:|
| sin   | 131.8 |  299.2 | 2.3×       |
| tan   | 115.8 |  163.7 | 1.4×       |
| cbrt  |  63.6 |  273.5 | 4.3×       |
| exp   | 221.9 |  498.1 | 2.2×       |
| ln    | 232.1 |  385.3 | 1.7×       |

## Takeaways

- MKL VML wins big on the **expensive transcendentals** (tan, asin/acos, cbrt,
  exp, ln, powf) even single-threaded — vectorized polynomial kernels vs the
  scalar `libm` calls in the std path.
- It **loses** on ops the hardware already does in one instruction (`sqrt`) or
  that inline to a couple of instructions (`abs`): the VML function-call
  overhead isn't worth it single-threaded. These are memory-bound anyway.
- `atan2`, `min`, `max`, `clamp`, `powi` are intentionally scalar in both
  builds (no single-vector-plus-scalar VML kernel), so they show no difference.
- Threaded, all VML ops saturate memory bandwidth (~100 GB/s here), hiding the
  math entirely — but that compares MKL's N cores against the std path's one,
  so the single-thread column is the apples-to-apples one.
