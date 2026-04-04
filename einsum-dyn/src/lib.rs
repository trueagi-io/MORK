//! Runtime dynamic [Einstein summation](https://en.wikipedia.org/wiki/Einstein_notation)
//! for arbitrary N-dimensional arrays.
//!
//! # Functions
//!
//! | Function | Inputs | Output |
//! |---|---|---|
//! | [`einsum_ary`] | N arrays (`&[&In]`) | tensor (`&mut Out`) |
//! | [`einsum_binary`] | two arrays | tensor (`&mut Out`) |
//! | [`einsum_unary`] | one array | tensor (`&mut Out`) |
//! | [`einsum_binary_scalar`] | two arrays | scalar (returned) |
//! | [`einsum_unary_scalar`] | one array | scalar (returned) |
//!
//! [`einsum_ary`] is the general-purpose entry point — it accepts any number
//! of inputs and subsumes both [`einsum_binary`] and [`einsum_unary`]. The
//! specialised functions remain for ergonomics and because they are ~1.5×
//! faster (stack-only buffers vs heap `Vec`s for patterns/indices).
//!
//! For scalar output with `einsum_ary`, pass a 0-dimensional output tensor
//! (`ndim() == 0`, single element at `&[]`).
//!
//! # Spec format
//!
//! Specs use lowercase letters `a`–`z` as index names, with `->` separating
//! inputs from output:
//!
//! - `"ab,bc->ac"` — matrix multiply (contract over `b`)
//! - `"ab->ba"` — transpose (no contraction)
//! - `"i,i->"` — dot product (scalar output, empty after `->`)
//! - `"aa->"` — trace (scalar output)
//! - `"ab,bc,cd->ad"` — 3-input chain contraction (N-ary)
//!
//! Indices present in inputs but absent from the output are contracted
//! (summed over). All output indices must appear in at least one input.
//!
//! # Implementing `NDIndex`
//!
//! Any type can be used with these functions by implementing [`NDIndex`]:
//!
//! ```
//! use einsum_dyn::{NDIndex, einsum_ary, einsum_binary, einsum_unary, einsum_binary_scalar, einsum_unary_scalar};
//!
//! struct MyTensor {
//!     data: Vec<f64>,
//!     shape: Vec<usize>,
//! }
//!
//! impl MyTensor {
//!     fn new(shape: Vec<usize>) -> Self {
//!         let n = shape.iter().product();
//!         Self { data: vec![0.0; n], shape }
//!     }
//!     fn linear_index(&self, ix: &[usize]) -> usize {
//!         let mut idx = 0;
//!         let mut stride = 1;
//!         for (&k, &dim) in ix.iter().rev().zip(self.shape.iter().rev()) {
//!             idx += k * stride;
//!             stride *= dim;
//!         }
//!         idx
//!     }
//! }
//!
//! impl NDIndex<f64> for MyTensor {
//!     fn ndim(&self) -> usize { self.shape.len() }
//!     fn dim(&self, axis: usize) -> usize { self.shape[axis] }
//!     fn get(&self, ix: &[usize]) -> f64 { self.data[self.linear_index(ix)] }
//!     fn set(&mut self, ix: &[usize], v: f64) {
//!         let i = self.linear_index(ix);
//!         self.data[i] = v;
//!     }
//! }
//!
//! // Matrix multiply: C = A × B
//! let mut a = MyTensor::new(vec![2, 3]);
//! a.data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
//! let mut b = MyTensor::new(vec![3, 2]);
//! b.data = vec![7.0, 8.0, 9.0, 10.0, 11.0, 12.0];
//! let mut c = MyTensor::new(vec![2, 2]);
//! einsum_binary("ab,bc->ac", &a, &b, &mut c).unwrap();
//! assert_eq!(c.data, vec![58.0, 64.0, 139.0, 154.0]);
//!
//! // Transpose
//! let mut t = MyTensor::new(vec![3, 2]);
//! einsum_unary("ab->ba", &a, &mut t).unwrap();
//! assert_eq!(t.data, vec![1.0, 4.0, 2.0, 5.0, 3.0, 6.0]);
//!
//! // Dot product (scalar)
//! let mut x = MyTensor::new(vec![3]);
//! x.data = vec![1.0, 2.0, 3.0];
//! let mut y = MyTensor::new(vec![3]);
//! y.data = vec![4.0, 5.0, 6.0];
//! let dot: f64 = einsum_binary_scalar("i,i->", &x, &y).unwrap();
//! assert_eq!(dot, 32.0);
//!
//! // Trace (scalar)
//! let mut m = MyTensor::new(vec![2, 2]);
//! m.data = vec![1.0, 2.0, 3.0, 4.0];
//! let tr: f64 = einsum_unary_scalar("aa->", &m).unwrap();
//! assert_eq!(tr, 5.0);
//!
//! // N-ary: 3-input chain A(2×3) × B(3×2) × C(2×2) via einsum_ary
//! let mut d = MyTensor::new(vec![2, 2]);
//! einsum_ary("ab,bc,cd->ad", &[&a, &b, &c], &mut d).unwrap();
//!
//! // N-ary with scalar output (0-dim tensor)
//! let mut scalar = MyTensor::new(vec![]);
//! einsum_ary("i,i->", &[&x, &y], &mut scalar).unwrap();
//! assert_eq!(scalar.data, vec![32.0]);
//! ```
//!
//! # Feature flags
//!
//! - **`ndarray`** — implements `NDIndex<T>` for [`ndarray::ArrayD<T>`], so you
//!   can pass dynamic-dimension ndarray arrays directly.

pub mod sparse;

use std::fmt;
use std::ops::{AddAssign, Mul};

/// Trait for N-dimensional array access.
///
/// Implement this for your tensor type to use the `einsum_*` functions.
/// All index slices are ordered left-to-right (outermost dimension first).
pub trait NDIndex<T> {
    fn ndim(&self) -> usize;
    fn dim(&self, axis: usize) -> usize;
    fn get(&self, indices: &[usize]) -> T;
    fn set(&mut self, indices: &[usize], val: T);

    /// Returns `None` for structurally absent (zero) entries.
    ///
    /// Dense implementations use the default, which wraps `get` in `Some`.
    /// Sparse implementations should override this to return `None` for
    /// entries not present in the sparse structure.
    fn get_opt(&self, indices: &[usize]) -> Option<T> {
        Some(self.get(indices))
    }

    /// Whether this array is a 2D sparse matrix supporting row iteration
    /// via `sparse_row_nnz` and `sparse_row_entry`. Default: false.
    fn is_sparse_2d(&self) -> bool { false }

    /// Number of non-zero entries in the given row.
    /// Only meaningful when `is_sparse_2d()` returns true.
    fn sparse_row_nnz(&self, _row: usize) -> usize { 0 }

    /// Get the `idx`-th non-zero entry in the given row as `(col, value)`.
    /// Only meaningful when `is_sparse_2d()` returns true.
    fn sparse_row_entry(&self, _row: usize, _idx: usize) -> (usize, T) {
        panic!("sparse_row_entry called on non-sparse array")
    }
}

#[cfg(feature = "ndarray")]
impl<T: Copy> NDIndex<T> for ndarray::ArrayD<T> {
    fn ndim(&self) -> usize {
        self.ndim()
    }
    fn dim(&self, axis: usize) -> usize {
        self.shape()[axis]
    }
    fn get(&self, ix: &[usize]) -> T {
        self[ndarray::IxDyn(ix)]
    }
    fn set(&mut self, ix: &[usize], val: T) {
        self[ndarray::IxDyn(ix)] = val;
    }
}

/// Error returned when an einsum spec string is invalid.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidSpec {
    MissingArrow,
    InvalidIndex { ch: char },
    WrongInputCount { expected: usize, got: usize },
    EmptyInput { input: usize },
    UnboundOutputIndex { index: char },
    InputNdimMismatch { input: usize, array_ndim: usize, spec_ndim: usize },
    DimensionMismatch { index: char, expected: usize, got: usize },
    OutputNdimMismatch { array_ndim: usize, spec_ndim: usize },
    OutputDimMismatch { axis: usize, expected: usize, got: usize },
    NonEmptyScalarOutput,
}

/// Convert a slot index back to its letter for error messages.
fn slot_to_char(s: u8) -> char {
    (s + b'a') as char
}

impl fmt::Display for InvalidSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingArrow => write!(f, "missing '->'"),
            Self::InvalidIndex { ch } => write!(f, "index '{ch}' is not a lowercase letter"),
            Self::WrongInputCount { expected, got } => {
                write!(f, "expected {expected} input(s), got {got}")
            }
            Self::EmptyInput { input } => write!(f, "input {input} has no indices"),
            Self::UnboundOutputIndex { index } => {
                write!(f, "output index '{index}' does not appear in any input")
            }
            Self::InputNdimMismatch { input, array_ndim, spec_ndim } => {
                write!(f, "input {input} has {array_ndim} dimensions but spec has {spec_ndim} indices")
            }
            Self::DimensionMismatch { index, expected, got } => {
                write!(f, "dimension mismatch for index '{index}': {expected} vs {got}")
            }
            Self::OutputNdimMismatch { array_ndim, spec_ndim } => {
                write!(f, "output has {array_ndim} dimensions but spec has {spec_ndim} output indices")
            }
            Self::OutputDimMismatch { axis, expected, got } => {
                write!(f, "output dimension {axis} is {got} but expected {expected}")
            }
            Self::NonEmptyScalarOutput => {
                write!(f, "scalar output requires empty output indices (use '...->')")
            }
        }
    }
}

impl std::error::Error for InvalidSpec {}

/// Parsed einsum specification. All index chars are stored as slot indices
/// (`b'a'` → 0, `b'b'` → 1, ..., `b'z'` → 25).
///
/// The RHS of the spec may contain multiple comma-separated output groups
/// (e.g. `"ab,bc->ac,ca"`). Single-output functions check `outputs.len() == 1`.
pub(crate) struct Spec {
    inputs: Vec<Vec<u8>>,
    outputs: Vec<Vec<u8>>,
}

impl Spec {
    /// Convenience: returns the first (and usually only) output pattern.
    pub(crate) fn output(&self) -> &[u8] {
        &self.outputs[0]
    }

    /// All unique output slots across all outputs.
    pub(crate) fn all_output_slots(&self) -> Vec<u8> {
        let mut seen = [false; 26];
        let mut slots = Vec::new();
        for out in &self.outputs {
            for &s in out {
                if !seen[s as usize] {
                    seen[s as usize] = true;
                    slots.push(s);
                }
            }
        }
        slots
    }
}

pub(crate) fn parse_spec(spec: &str, expected_inputs: usize) -> Result<Spec, InvalidSpec> {
    let spec = spec.replace(' ', "");

    let (lhs, rhs) = spec
        .split_once("->")
        .ok_or(InvalidSpec::MissingArrow)?;

    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for part in lhs.split(',') {
        let mut slots = Vec::new();
        for ch in part.bytes() {
            if !ch.is_ascii_lowercase() {
                return Err(InvalidSpec::InvalidIndex { ch: ch as char });
            }
            slots.push(ch - b'a');
        }
        inputs.push(slots);
    }

    if inputs.len() != expected_inputs {
        return Err(InvalidSpec::WrongInputCount {
            expected: expected_inputs,
            got: inputs.len(),
        });
    }

    for (i, inp) in inputs.iter().enumerate() {
        if inp.is_empty() {
            return Err(InvalidSpec::EmptyInput { input: i });
        }
    }

    let mut outputs: Vec<Vec<u8>> = Vec::new();
    for part in rhs.split(',') {
        let mut slots = Vec::new();
        for ch in part.bytes() {
            if !ch.is_ascii_lowercase() {
                return Err(InvalidSpec::InvalidIndex { ch: ch as char });
            }
            slots.push(ch - b'a');
        }
        outputs.push(slots);
    }

    // Validate: every output index must appear in at least one input
    let mut seen = [false; 26];
    for inp in &inputs {
        for &s in inp {
            seen[s as usize] = true;
        }
    }
    for out in &outputs {
        for &s in out {
            if !seen[s as usize] {
                return Err(InvalidSpec::UnboundOutputIndex { index: slot_to_char(s) });
            }
        }
    }

    Ok(Spec { inputs, outputs })
}

/// Validates that array dimensions match the spec. Returns dims as a `[usize; 26]`
/// array (indexed by slot). Unused slots are 0.
pub(crate) fn validate_dims<T, Arr: NDIndex<T>>(
    spec: &Spec,
    arrays: &[&Arr],
) -> Result<[usize; 26], InvalidSpec> {
    for (i, (inp, arr)) in spec.inputs.iter().zip(arrays.iter()).enumerate() {
        if arr.ndim() != inp.len() {
            return Err(InvalidSpec::InputNdimMismatch {
                input: i,
                array_ndim: arr.ndim(),
                spec_ndim: inp.len(),
            });
        }
    }

    let mut dims = [0usize; 26];
    let mut set = [false; 26];
    for (pi, inp) in spec.inputs.iter().enumerate() {
        for (pos, &s) in inp.iter().enumerate() {
            let si = s as usize;
            let d = arrays[pi].dim(pos);
            if set[si] {
                if dims[si] != d {
                    return Err(InvalidSpec::DimensionMismatch {
                        index: slot_to_char(s),
                        expected: dims[si],
                        got: d,
                    });
                }
            } else {
                dims[si] = d;
                set[si] = true;
            }
        }
    }

    Ok(dims)
}

/// Collects all unique indices in order of first appearance, as a SlotList.
fn all_slots_ordered(spec: &Spec) -> SlotList {
    let mut seen = [false; 26];
    let mut slots = [0u8; 26];
    let mut len = 0u8;
    for inp in &spec.inputs {
        for &s in inp {
            if !seen[s as usize] {
                seen[s as usize] = true;
                slots[len as usize] = s;
                len += 1;
            }
        }
    }
    SlotList { slots, len }
}

/// Stack-only index buffer: fixed array + length, no heap.
struct Idx {
    data: [usize; 26],
    len: u8,
}

impl Idx {
    const ZERO: Self = Idx { data: [0; 26], len: 0 };

    #[inline(always)]
    fn as_slice(&self) -> &[usize] {
        &self.data[..self.len as usize]
    }
}

/// Precomputed gather pattern: slot indices stored on the stack.
struct Pattern {
    slots: [u8; 26],
    len: u8,
}

impl Pattern {
    fn from_slots(slot_indices: &[u8]) -> Self {
        let mut slots = [0u8; 26];
        slots[..slot_indices.len()].copy_from_slice(slot_indices);
        Pattern {
            slots,
            len: slot_indices.len() as u8,
        }
    }

    /// Gather index values from `vals` into `out` according to this pattern.
    #[inline(always)]
    fn gather(&self, vals: &[usize; 26], out: &mut Idx) {
        out.len = self.len;
        for i in 0..self.len as usize {
            out.data[i] = vals[self.slots[i] as usize];
        }
    }
}

/// Precomputed loop-slot list stored on the stack.
struct SlotList {
    slots: [u8; 26],
    len: u8,
}

impl SlotList {
    fn from_slots(slot_indices: &[u8]) -> Self {
        let mut slots = [0u8; 26];
        slots[..slot_indices.len()].copy_from_slice(slot_indices);
        SlotList {
            slots,
            len: slot_indices.len() as u8,
        }
    }

    fn as_slice(&self) -> &[u8] {
        &self.slots[..self.len as usize]
    }

    fn contains(&self, s: u8) -> bool {
        self.as_slice().contains(&s)
    }

    fn filtered_complement(all: &[u8], free: &SlotList) -> Self {
        let mut slots = [0u8; 26];
        let mut len = 0u8;
        for &s in all {
            if !free.contains(s) {
                slots[len as usize] = s;
                len += 1;
            }
        }
        SlotList { slots, len }
    }
}

/// Recursive loop nest over slots. `loop_slots[i]` is a slot index,
/// `dims` and `vals` are flat [usize; 26] arrays.
#[inline(always)]
fn loop_nest(
    loop_slots: &[u8],
    dims: &[usize; 26],
    vals: &mut [usize; 26],
    emit: &mut impl FnMut(&[usize; 26]),
) {
    if loop_slots.is_empty() {
        emit(vals);
        return;
    }
    let s = loop_slots[0] as usize;
    let rest = &loop_slots[1..];
    let n = dims[s];
    for v in 0..n {
        vals[s] = v;
        loop_nest(rest, dims, vals, emit);
    }
}

// Iterative variant using an explicit counter stack.
// Benchmarked ~same as recursive.
#[cfg(any())]
#[inline(always)]
fn loop_nest_iterative(
    loop_slots: &[u8],
    dims: &[usize; 26],
    vals: &mut [usize; 26],
    emit: &mut impl FnMut(&[usize; 26]),
) {
    let depth = loop_slots.len();
    if depth == 0 {
        emit(vals);
        return;
    }
    let mut counters = [0usize; 26];
    for i in 0..depth {
        vals[loop_slots[i] as usize] = 0;
    }
    loop {
        emit(vals);
        let mut level = depth - 1;
        loop {
            let s = loop_slots[level] as usize;
            counters[level] += 1;
            if counters[level] < dims[s] {
                vals[s] = counters[level];
                break;
            }
            counters[level] = 0;
            vals[s] = 0;
            if level == 0 {
                return;
            }
            level -= 1;
        }
    }
}

/// Validate output array dimensions against the spec.
pub(crate) fn validate_output<T, Arr: NDIndex<T>>(
    spec: &Spec,
    dims: &[usize; 26],
    out: &Arr,
) -> Result<(), InvalidSpec> {
    if out.ndim() != spec.output().len() {
        return Err(InvalidSpec::OutputNdimMismatch {
            array_ndim: out.ndim(),
            spec_ndim: spec.output().len(),
        });
    }
    for (pos, &s) in spec.output().iter().enumerate() {
        if out.dim(pos) != dims[s as usize] {
            return Err(InvalidSpec::OutputDimMismatch {
                axis: pos,
                expected: dims[s as usize],
                got: out.dim(pos),
            });
        }
    }
    Ok(())
}

/// `einsum_ary(spec, inputs, out)` — N-ary einsum with tensor output.
///
/// Generalises [`einsum_binary`] and [`einsum_unary`] to an arbitrary number
/// of inputs. The spec must contain exactly `inputs.len()` comma-separated
/// input index groups.
///
/// For scalar output, pass a 0-dimensional output tensor (`ndim() == 0`,
/// one element at index `&[]`) and use an empty output spec (e.g. `"i,i->"`).
///
/// The specialised binary/unary functions are ~1.5× faster due to stack-only
/// buffers; prefer them for the 1- and 2-input cases on hot paths.
///
/// ```
/// # use einsum_dyn::{NDIndex, einsum_ary};
/// # struct T { m: Vec<f32>, d: Vec<usize> }
/// # impl T { fn new(d: Vec<usize>) -> Self { let n = d.iter().product(); Self { m: vec![0.0; n], d } } fn li(&self, ix: &[usize]) -> usize { let mut i=0; let mut s=1; for (&k,&d) in ix.iter().rev().zip(self.d.iter().rev()) { i+=k*s; s*=d; } i } }
/// # impl NDIndex<f32> for T { fn ndim(&self)->usize{self.d.len()} fn dim(&self,a:usize)->usize{self.d[a]} fn get(&self,ix:&[usize])->f32{self.m[self.li(ix)]} fn set(&mut self,ix:&[usize],v:f32){let i=self.li(ix);self.m[i]=v;} }
/// let mut a = T::new(vec![2, 3]);
/// a.m = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
/// let mut b = T::new(vec![3, 2]);
/// b.m = vec![7.0, 8.0, 9.0, 10.0, 11.0, 12.0];
/// let mut c = T::new(vec![2, 2]);
/// einsum_ary("ab,bc->ac", &[&a, &b], &mut c).unwrap();
/// assert_eq!(c.m, vec![58.0, 64.0, 139.0, 154.0]);
/// ```
pub fn einsum_ary<T, In, Out>(spec: &str, inputs: &[&In], out: &mut Out) -> Result<(), InvalidSpec>
where
    T: Default + Copy + AddAssign + Mul<Output = T>,
    In: NDIndex<T>,
    Out: NDIndex<T>,
{
    let spec = parse_spec(spec, inputs.len())?;
    let dims = validate_dims(&spec, inputs)?;
    validate_output(&spec, &dims, out)?;

    let free_slots = SlotList::from_slots(&spec.output());
    let all = all_slots_ordered(&spec);
    let contracted_slots = SlotList::filtered_complement(all.as_slice(), &free_slots);

    let pats: Vec<Pattern> = spec.inputs.iter().map(|inp| Pattern::from_slots(inp)).collect();
    let pat_out = Pattern::from_slots(&spec.output());

    let n = inputs.len();
    let mut vals = [0usize; 26];
    let mut bufs: Vec<Idx> = (0..n).map(|_| Idx::ZERO).collect();
    let mut buf_out = Idx::ZERO;

    if contracted_slots.len == 0 {
        // No contraction — direct assignment
        loop_nest(free_slots.as_slice(), &dims, &mut vals, &mut |vals| {
            for i in 0..n {
                pats[i].gather(vals, &mut bufs[i]);
            }
            // Multiply all input values; if any is sparse-absent, result is zero
            let first = match inputs[0].get_opt(bufs[0].as_slice()) {
                Some(v) => v,
                None => { pat_out.gather(vals, &mut buf_out); out.set(buf_out.as_slice(), Default::default()); return; }
            };
            let mut product = first;
            for i in 1..n {
                match inputs[i].get_opt(bufs[i].as_slice()) {
                    Some(v) => product = product * v,
                    None => { pat_out.gather(vals, &mut buf_out); out.set(buf_out.as_slice(), Default::default()); return; }
                }
            }
            pat_out.gather(vals, &mut buf_out);
            out.set(buf_out.as_slice(), product);
        });
    } else {
        // With contraction — accumulate per output element
        loop_nest(free_slots.as_slice(), &dims, &mut vals, &mut |free_vals| {
            let mut acc: T = Default::default();
            let mut inner_vals = *free_vals;
            loop_nest(
                contracted_slots.as_slice(),
                &dims,
                &mut inner_vals,
                &mut |vals| {
                    for i in 0..n {
                        pats[i].gather(vals, &mut bufs[i]);
                    }
                    let first = match inputs[0].get_opt(bufs[0].as_slice()) {
                        Some(v) => v,
                        None => return,
                    };
                    let mut product = first;
                    for i in 1..n {
                        match inputs[i].get_opt(bufs[i].as_slice()) {
                            Some(v) => product = product * v,
                            None => return,
                        }
                    }
                    acc += product;
                },
            );
            pat_out.gather(free_vals, &mut buf_out);
            out.set(buf_out.as_slice(), acc);
        });
    }

    Ok(())
}

/// `einsum_binary(spec, a, b, out)` — binary einsum with tensor output.
///
/// Spec format: `"ab,bc->ac"` (numpy-style).
/// All indices in the output must appear in at least one input.
/// Indices present in inputs but absent from the output are contracted (summed over).
/// The output array must already have the correct shape.
pub fn einsum_binary<T, In, Out>(spec: &str, a: &In, b: &In, out: &mut Out) -> Result<(), InvalidSpec>
where
    T: Default + Copy + AddAssign + Mul<Output = T>,
    In: NDIndex<T>,
    Out: NDIndex<T>,
{
    let spec = parse_spec(spec, 2)?;
    let dims = validate_dims(&spec, &[a, b])?;
    validate_output(&spec, &dims, out)?;

    let free_slots = SlotList::from_slots(&spec.output());
    let all = all_slots_ordered(&spec);
    let contracted_slots = SlotList::filtered_complement(all.as_slice(), &free_slots);

    let pat_a = Pattern::from_slots(&spec.inputs[0]);
    let pat_b = Pattern::from_slots(&spec.inputs[1]);
    let pat_out = Pattern::from_slots(&spec.output());

    let mut vals = [0usize; 26];
    let mut buf_a = Idx::ZERO;
    let mut buf_b = Idx::ZERO;
    let mut buf_out = Idx::ZERO;

    if contracted_slots.len == 0 {
        // No contraction — direct assignment
        loop_nest(free_slots.as_slice(), &dims, &mut vals, &mut |vals| {
            pat_a.gather(vals, &mut buf_a);
            pat_b.gather(vals, &mut buf_b);
            pat_out.gather(vals, &mut buf_out);
            let v = match (a.get_opt(buf_a.as_slice()), b.get_opt(buf_b.as_slice())) {
                (Some(av), Some(bv)) => av * bv,
                _ => Default::default(),
            };
            out.set(buf_out.as_slice(), v);
        });
    } else {
        // With contraction — accumulate per output element
        loop_nest(free_slots.as_slice(), &dims, &mut vals, &mut |free_vals| {
            let mut acc: T = Default::default();
            let mut inner_vals = *free_vals;
            loop_nest(
                contracted_slots.as_slice(),
                &dims,
                &mut inner_vals,
                &mut |vals| {
                    pat_a.gather(vals, &mut buf_a);
                    pat_b.gather(vals, &mut buf_b);
                    if let (Some(av), Some(bv)) =
                        (a.get_opt(buf_a.as_slice()), b.get_opt(buf_b.as_slice()))
                    {
                        acc += av * bv;
                    }
                },
            );
            pat_out.gather(free_vals, &mut buf_out);
            out.set(buf_out.as_slice(), acc);
        });
    }

    Ok(())
}

/// `einsum_unary(spec, a, out)` — unary einsum with tensor output.
///
/// Spec format: `"ab->ba"` (numpy-style).
pub fn einsum_unary<T, In, Out>(spec: &str, a: &In, out: &mut Out) -> Result<(), InvalidSpec>
where
    T: Default + Copy + AddAssign + Mul<Output = T>,
    In: NDIndex<T>,
    Out: NDIndex<T>,
{
    let spec = parse_spec(spec, 1)?;
    let dims = validate_dims(&spec, &[a])?;
    validate_output(&spec, &dims, out)?;

    let free_slots = SlotList::from_slots(&spec.output());
    let all = all_slots_ordered(&spec);
    let contracted_slots = SlotList::filtered_complement(all.as_slice(), &free_slots);

    let pat_a = Pattern::from_slots(&spec.inputs[0]);
    let pat_out = Pattern::from_slots(&spec.output());
    let mut vals = [0usize; 26];
    let mut buf_a = Idx::ZERO;
    let mut buf_out = Idx::ZERO;

    if contracted_slots.len == 0 {
        loop_nest(free_slots.as_slice(), &dims, &mut vals, &mut |vals| {
            pat_a.gather(vals, &mut buf_a);
            pat_out.gather(vals, &mut buf_out);
            let v = a.get_opt(buf_a.as_slice()).unwrap_or_default();
            out.set(buf_out.as_slice(), v);
        });
    } else {
        loop_nest(free_slots.as_slice(), &dims, &mut vals, &mut |free_vals| {
            let mut acc: T = Default::default();
            let mut inner_vals = *free_vals;
            loop_nest(
                contracted_slots.as_slice(),
                &dims,
                &mut inner_vals,
                &mut |vals| {
                    pat_a.gather(vals, &mut buf_a);
                    if let Some(av) = a.get_opt(buf_a.as_slice()) {
                        acc += av;
                    }
                },
            );
            pat_out.gather(free_vals, &mut buf_out);
            out.set(buf_out.as_slice(), acc);
        });
    }

    Ok(())
}

/// `einsum_binary_scalar(spec, a, b)` — binary einsum with scalar output.
///
/// Spec format: `"ab,ab->"` (empty output = scalar).
pub fn einsum_binary_scalar<T, Arr>(spec: &str, a: &Arr, b: &Arr) -> Result<T, InvalidSpec>
where
    T: Default + Copy + AddAssign + Mul<Output = T>,
    Arr: NDIndex<T>,
{
    let spec = parse_spec(spec, 2)?;
    let dims = validate_dims(&spec, &[a, b])?;

    if !spec.output().is_empty() {
        return Err(InvalidSpec::NonEmptyScalarOutput);
    }

    let all = all_slots_ordered(&spec);
    let pat_a = Pattern::from_slots(&spec.inputs[0]);
    let pat_b = Pattern::from_slots(&spec.inputs[1]);
    let mut vals = [0usize; 26];
    let mut buf_a = Idx::ZERO;
    let mut buf_b = Idx::ZERO;
    let mut acc: T = Default::default();

    loop_nest(all.as_slice(), &dims, &mut vals, &mut |vals| {
        pat_a.gather(vals, &mut buf_a);
        pat_b.gather(vals, &mut buf_b);
        if let (Some(av), Some(bv)) =
            (a.get_opt(buf_a.as_slice()), b.get_opt(buf_b.as_slice()))
        {
            acc += av * bv;
        }
    });

    Ok(acc)
}

/// `einsum_unary_scalar(spec, a)` — unary einsum with scalar output.
///
/// Spec format: `"aa->"` (empty output = scalar).
pub fn einsum_unary_scalar<T, Arr>(spec: &str, a: &Arr) -> Result<T, InvalidSpec>
where
    T: Default + Copy + AddAssign + Mul<Output = T>,
    Arr: NDIndex<T>,
{
    let spec = parse_spec(spec, 1)?;
    let dims = validate_dims(&spec, &[a])?;

    if !spec.output().is_empty() {
        return Err(InvalidSpec::NonEmptyScalarOutput);
    }

    let all = all_slots_ordered(&spec);
    let pat_a = Pattern::from_slots(&spec.inputs[0]);
    let mut vals = [0usize; 26];
    let mut buf_a = Idx::ZERO;
    let mut acc: T = Default::default();

    loop_nest(all.as_slice(), &dims, &mut vals, &mut |vals| {
        pat_a.gather(vals, &mut buf_a);
        if let Some(av) = a.get_opt(buf_a.as_slice()) {
            acc += av;
        }
    });

    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal dense tensor for testing.
    struct Tensor {
        m: Vec<f32>,
        d: Vec<usize>,
    }

    impl Tensor {
        fn new(d: Vec<usize>) -> Self {
            let n: usize = d.iter().product();
            Self {
                m: vec![0.0; n],
                d,
            }
        }

        fn linear_index(&self, ix: &[usize]) -> usize {
            let mut idx = 0usize;
            let mut stride = 1usize;
            for (&k, &dim) in ix.iter().rev().zip(self.d.iter().rev()) {
                idx += k * stride;
                stride *= dim;
            }
            idx
        }
    }

    impl NDIndex<f32> for Tensor {
        fn ndim(&self) -> usize {
            self.d.len()
        }

        fn dim(&self, axis: usize) -> usize {
            self.d[axis]
        }

        fn get(&self, ix: &[usize]) -> f32 {
            self.m[self.linear_index(ix)]
        }

        fn set(&mut self, ix: &[usize], v: f32) {
            let i = self.linear_index(ix);
            self.m[i] = v;
        }
    }

    fn set_matrix(t: &mut Tensor, vals: &[f32]) {
        for (i, &v) in vals.iter().enumerate() {
            t.m[i] = v;
        }
    }

    #[test]
    fn test_matmul() {
        let mut a = Tensor::new(vec![2, 3]);
        let mut b = Tensor::new(vec![3, 2]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        set_matrix(&mut b, &[7.0, 8.0, 9.0, 10.0, 11.0, 12.0]);

        let mut c = Tensor::new(vec![2, 2]);
        einsum_binary("ab,bc->ac", &a, &b, &mut c).unwrap();

        assert_eq!(c.get(&[0, 0]), 58.0);
        assert_eq!(c.get(&[0, 1]), 64.0);
        assert_eq!(c.get(&[1, 0]), 139.0);
        assert_eq!(c.get(&[1, 1]), 154.0);
    }

    #[test]
    fn test_transpose() {
        let mut a = Tensor::new(vec![2, 3]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);

        let mut t = Tensor::new(vec![3, 2]);
        einsum_unary("ab->ba", &a, &mut t).unwrap();

        assert_eq!(t.get(&[0, 0]), 1.0);
        assert_eq!(t.get(&[0, 1]), 4.0);
        assert_eq!(t.get(&[1, 0]), 2.0);
        assert_eq!(t.get(&[1, 1]), 5.0);
        assert_eq!(t.get(&[2, 0]), 3.0);
        assert_eq!(t.get(&[2, 1]), 6.0);
    }

    #[test]
    fn test_outer_product() {
        let mut a = Tensor::new(vec![3]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0]);
        let mut b = Tensor::new(vec![2]);
        set_matrix(&mut b, &[4.0, 5.0]);

        let mut c = Tensor::new(vec![3, 2]);
        einsum_binary("a,b->ab", &a, &b, &mut c).unwrap();

        assert_eq!(c.get(&[0, 0]), 4.0);
        assert_eq!(c.get(&[0, 1]), 5.0);
        assert_eq!(c.get(&[1, 0]), 8.0);
        assert_eq!(c.get(&[1, 1]), 10.0);
        assert_eq!(c.get(&[2, 0]), 12.0);
        assert_eq!(c.get(&[2, 1]), 15.0);
    }

    #[test]
    fn test_vecmat() {
        let mut v = Tensor::new(vec![2]);
        set_matrix(&mut v, &[1.0, 2.0]);
        let mut m = Tensor::new(vec![2, 2]);
        set_matrix(&mut m, &[3.0, 4.0, 5.0, 6.0]);

        let mut r = Tensor::new(vec![2]);
        einsum_binary("a,ab->b", &v, &m, &mut r).unwrap();

        assert_eq!(r.get(&[0]), 13.0);
        assert_eq!(r.get(&[1]), 16.0);
    }

    #[test]
    fn test_dot() {
        let mut a = Tensor::new(vec![4]);
        let mut b = Tensor::new(vec![4]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0]);
        set_matrix(&mut b, &[5.0, 6.0, 7.0, 8.0]);

        let result: f32 = einsum_binary_scalar("i,i->", &a, &b).unwrap();
        assert_eq!(result, 70.0);
    }

    #[test]
    fn test_trace() {
        let mut m = Tensor::new(vec![3, 3]);
        set_matrix(
            &mut m,
            &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0],
        );

        let result: f32 = einsum_unary_scalar("aa->", &m).unwrap();
        assert_eq!(result, 15.0);
    }

    #[test]
    fn test_frobenius2() {
        let mut a = Tensor::new(vec![2, 2]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0]);

        let result: f32 = einsum_binary_scalar("ab,ab->", &a, &a).unwrap();
        assert_eq!(result, 30.0);
    }

    #[test]
    fn test_attention() {
        let (b, h, q_len, k_len, dim) = (2, 2, 3, 2, 4);
        let mut q = Tensor::new(vec![b, h, q_len, dim]);
        let mut k = Tensor::new(vec![b, h, k_len, dim]);

        for bi in 0..b {
            for hi in 0..h {
                for qi in 0..q_len {
                    for di in 0..dim {
                        let v =
                            (bi + 1) as f32 * (hi + 1) as f32 * (qi + 1) as f32 + di as f32;
                        q.set(&[bi, hi, qi, di], v);
                    }
                }
                for ki in 0..k_len {
                    for di in 0..dim {
                        let v =
                            (bi + 1) as f32 * (hi + 1) as f32 * (ki + 1) as f32 * (di + 1) as f32;
                        k.set(&[bi, hi, ki, di], v);
                    }
                }
            }
        }

        let mut out = Tensor::new(vec![b, h, q_len, k_len]);
        einsum_binary("bhqd,bhkd->bhqk", &q, &k, &mut out).unwrap();

        for bi in 0..b {
            for hi in 0..h {
                for qi in 0..q_len {
                    for ki in 0..k_len {
                        let mut expected = 0.0f32;
                        for di in 0..dim {
                            expected += q.get(&[bi, hi, qi, di]) * k.get(&[bi, hi, ki, di]);
                        }
                        let actual = out.get(&[bi, hi, qi, ki]);
                        assert!(
                            (actual - expected).abs() < 1e-3,
                            "mismatch at [{bi},{hi},{qi},{ki}]: got {actual}, expected {expected}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_err_missing_arrow() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        let mut c = Tensor::new(vec![2, 2]);
        assert_eq!(
            einsum_binary("ab,bc", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::MissingArrow
        );
    }

    #[test]
    fn test_err_invalid_index() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        let mut c = Tensor::new(vec![2, 2]);
        assert_eq!(
            einsum_binary("aB,bc->ac", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::InvalidIndex { ch: 'B' }
        );
        // Invalid char in output
        assert_eq!(
            einsum_binary("ab,bc->a1", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::InvalidIndex { ch: '1' }
        );
    }

    #[test]
    fn test_err_wrong_input_count() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        let mut c = Tensor::new(vec![2, 2]);
        // Binary function but spec has 1 input
        assert_eq!(
            einsum_binary("ab->ab", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::WrongInputCount { expected: 2, got: 1 }
        );
        // Unary function but spec has 2 inputs
        assert_eq!(
            einsum_unary("ab,bc->ac", &a, &mut c).unwrap_err(),
            InvalidSpec::WrongInputCount { expected: 1, got: 2 }
        );
    }

    #[test]
    fn test_err_empty_input() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        let mut c = Tensor::new(vec![2, 2]);
        assert_eq!(
            einsum_binary(",bc->bc", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::EmptyInput { input: 0 }
        );
    }

    #[test]
    fn test_err_unbound_output_index() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        let mut c = Tensor::new(vec![2, 2]);
        assert_eq!(
            einsum_binary("ab,bc->az", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::UnboundOutputIndex { index: 'z' }
        );
    }

    #[test]
    fn test_err_input_ndim_mismatch() {
        // a is 2D but spec says 3 indices
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        let mut c = Tensor::new(vec![2, 2]);
        assert_eq!(
            einsum_binary("abc,bd->ad", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::InputNdimMismatch { input: 0, array_ndim: 2, spec_ndim: 3 }
        );
    }

    #[test]
    fn test_err_dimension_mismatch() {
        // a is 2×3, b is 3×2, spec says first dims must match (a=2 vs a=3)
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        let mut c = Tensor::new(vec![2, 2]);
        assert_eq!(
            einsum_binary("ab,ac->bc", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::DimensionMismatch { index: 'a', expected: 2, got: 3 }
        );
    }

    #[test]
    fn test_err_output_ndim_mismatch() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        // Output is 1D but spec says 2D
        let mut c = Tensor::new(vec![2]);
        assert_eq!(
            einsum_binary("ab,bc->ac", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::OutputNdimMismatch { array_ndim: 1, spec_ndim: 2 }
        );
    }

    #[test]
    fn test_err_output_dim_mismatch() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![3, 2]);
        // Output should be 2×2 but we give 2×3
        let mut c = Tensor::new(vec![2, 3]);
        assert_eq!(
            einsum_binary("ab,bc->ac", &a, &b, &mut c).unwrap_err(),
            InvalidSpec::OutputDimMismatch { axis: 1, expected: 2, got: 3 }
        );
    }

    #[test]
    fn test_err_non_empty_scalar_output() {
        let a = Tensor::new(vec![2, 3]);
        let b = Tensor::new(vec![2, 3]);
        assert_eq!(
            einsum_binary_scalar::<f32, Tensor>("ab,ab->a", &a, &b).unwrap_err(),
            InvalidSpec::NonEmptyScalarOutput
        );
        assert_eq!(
            einsum_unary_scalar::<f32, Tensor>("ab->a", &a).unwrap_err(),
            InvalidSpec::NonEmptyScalarOutput
        );
    }

    #[test]
    fn test_unary_row_sum() {
        let mut a = Tensor::new(vec![2, 3]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);

        let mut out = Tensor::new(vec![2]);
        einsum_unary("ab->a", &a, &mut out).unwrap();

        assert_eq!(out.get(&[0]), 6.0);
        assert_eq!(out.get(&[1]), 15.0);
    }

    // --- einsum_ary tests ---

    #[test]
    fn test_ary_matmul_as_binary() {
        // einsum_ary with 2 inputs should match einsum_binary
        let mut a = Tensor::new(vec![2, 3]);
        let mut b = Tensor::new(vec![3, 2]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        set_matrix(&mut b, &[7.0, 8.0, 9.0, 10.0, 11.0, 12.0]);

        let mut c = Tensor::new(vec![2, 2]);
        einsum_ary("ab,bc->ac", &[&a, &b], &mut c).unwrap();

        assert_eq!(c.get(&[0, 0]), 58.0);
        assert_eq!(c.get(&[0, 1]), 64.0);
        assert_eq!(c.get(&[1, 0]), 139.0);
        assert_eq!(c.get(&[1, 1]), 154.0);
    }

    #[test]
    fn test_ary_transpose_as_unary() {
        // einsum_ary with 1 input should match einsum_unary
        let mut a = Tensor::new(vec![2, 3]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);

        let mut t = Tensor::new(vec![3, 2]);
        einsum_ary("ab->ba", &[&a], &mut t).unwrap();

        assert_eq!(t.get(&[0, 0]), 1.0);
        assert_eq!(t.get(&[0, 1]), 4.0);
        assert_eq!(t.get(&[1, 0]), 2.0);
        assert_eq!(t.get(&[2, 1]), 6.0);
    }

    #[test]
    fn test_ary_three_input_chain() {
        // A(2×3) × B(3×4) × C(4×2) -> D(2×2)
        // spec: "ab,bc,cd->ad" contracts b and c
        let mut a = Tensor::new(vec![2, 3]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        let mut b = Tensor::new(vec![3, 4]);
        set_matrix(&mut b, &[1.0, 0.0, 0.0, 0.0,
                              0.0, 1.0, 0.0, 0.0,
                              0.0, 0.0, 1.0, 0.0]);
        let mut c = Tensor::new(vec![4, 2]);
        set_matrix(&mut c, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]);

        let mut d = Tensor::new(vec![2, 2]);
        einsum_ary("ab,bc,cd->ad", &[&a, &b, &c], &mut d).unwrap();

        // AB = [[1,2,3,0],[4,5,6,0]], ABC = AB×C = [[1*1+2*3+3*5, 1*2+2*4+3*6],[4*1+5*3+6*5, 4*2+5*4+6*6]]
        // = [[22, 28],[49, 64]]
        assert_eq!(d.get(&[0, 0]), 22.0);
        assert_eq!(d.get(&[0, 1]), 28.0);
        assert_eq!(d.get(&[1, 0]), 49.0);
        assert_eq!(d.get(&[1, 1]), 64.0);
    }

    #[test]
    fn test_ary_outer_product_three() {
        // No contraction: a(i) × b(j) × c(k) -> out(i,j,k)
        let mut a = Tensor::new(vec![2]);
        set_matrix(&mut a, &[2.0, 3.0]);
        let mut b = Tensor::new(vec![2]);
        set_matrix(&mut b, &[5.0, 7.0]);
        let mut c = Tensor::new(vec![2]);
        set_matrix(&mut c, &[11.0, 13.0]);

        let mut out = Tensor::new(vec![2, 2, 2]);
        einsum_ary("a,b,c->abc", &[&a, &b, &c], &mut out).unwrap();

        // out[i,j,k] = a[i]*b[j]*c[k]
        assert_eq!(out.get(&[0, 0, 0]), 2.0 * 5.0 * 11.0);
        assert_eq!(out.get(&[0, 0, 1]), 2.0 * 5.0 * 13.0);
        assert_eq!(out.get(&[0, 1, 0]), 2.0 * 7.0 * 11.0);
        assert_eq!(out.get(&[1, 1, 1]), 3.0 * 7.0 * 13.0);
    }

    #[test]
    fn test_ary_scalar_dot() {
        // Scalar output via 0-dim tensor: "i,i->" (dot product)
        let mut a = Tensor::new(vec![4]);
        let mut b = Tensor::new(vec![4]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0]);
        set_matrix(&mut b, &[5.0, 6.0, 7.0, 8.0]);

        let mut out = Tensor::new(vec![]);  // 0-dim
        einsum_ary("i,i->", &[&a, &b], &mut out).unwrap();

        assert_eq!(out.get(&[]), 70.0);
    }

    #[test]
    fn test_ary_scalar_trace() {
        // Scalar output via 0-dim tensor: "aa->" (trace)
        let mut m = Tensor::new(vec![3, 3]);
        set_matrix(&mut m, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0]);

        let mut out = Tensor::new(vec![]);
        einsum_ary("aa->", &[&m], &mut out).unwrap();

        assert_eq!(out.get(&[]), 15.0);
    }

    #[test]
    fn test_ary_scalar_three_input() {
        // "i,i,i->" — element-wise product summed to scalar
        let mut a = Tensor::new(vec![3]);
        let mut b = Tensor::new(vec![3]);
        let mut c = Tensor::new(vec![3]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0]);
        set_matrix(&mut b, &[4.0, 5.0, 6.0]);
        set_matrix(&mut c, &[7.0, 8.0, 9.0]);

        let mut out = Tensor::new(vec![]);
        einsum_ary("i,i,i->", &[&a, &b, &c], &mut out).unwrap();

        // 1*4*7 + 2*5*8 + 3*6*9 = 28 + 80 + 162 = 270
        assert_eq!(out.get(&[]), 270.0);
    }

    #[test]
    fn test_ary_row_sum_unary() {
        let mut a = Tensor::new(vec![2, 3]);
        set_matrix(&mut a, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);

        let mut out = Tensor::new(vec![2]);
        einsum_ary("ab->a", &[&a], &mut out).unwrap();

        assert_eq!(out.get(&[0]), 6.0);
        assert_eq!(out.get(&[1]), 15.0);
    }
}

#[cfg(test)]
#[cfg(feature = "ndarray")]
mod ndarray_tests {
    use super::*;
    use ndarray::{ArrayD, IxDyn};

    fn arr1(data: &[f64]) -> ArrayD<f64> {
        ArrayD::from_shape_vec(IxDyn(&[data.len()]), data.to_vec()).unwrap()
    }

    fn arr2(rows: usize, cols: usize, data: &[f64]) -> ArrayD<f64> {
        ArrayD::from_shape_vec(IxDyn(&[rows, cols]), data.to_vec()).unwrap()
    }

    fn zeros(shape: &[usize]) -> ArrayD<f64> {
        ArrayD::zeros(IxDyn(shape))
    }

    #[test]
    fn test_ndindex_trait() {
        let a = arr2(2, 2, &[1.0, 2.0, 3.0, 4.0]);
        assert_eq!(NDIndex::ndim(&a), 2);
        assert_eq!(NDIndex::dim(&a, 0), 2);
        assert_eq!(NDIndex::dim(&a, 1), 2);
        assert_eq!(NDIndex::get(&a, &[0, 1]), 2.0);
        assert_eq!(NDIndex::get(&a, &[1, 0]), 3.0);

        let mut b = a.clone();
        NDIndex::set(&mut b, &[0, 0], 99.0);
        assert_eq!(NDIndex::get(&b, &[0, 0]), 99.0);
    }

    #[test]
    fn test_matmul() {
        let a = arr2(2, 3, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        let b = arr2(3, 2, &[7.0, 8.0, 9.0, 10.0, 11.0, 12.0]);
        let mut c = zeros(&[2, 2]);

        einsum_binary("ab,bc->ac", &a, &b, &mut c).unwrap();

        assert_eq!(c[IxDyn(&[0, 0])], 58.0);
        assert_eq!(c[IxDyn(&[0, 1])], 64.0);
        assert_eq!(c[IxDyn(&[1, 0])], 139.0);
        assert_eq!(c[IxDyn(&[1, 1])], 154.0);
    }

    #[test]
    fn test_transpose() {
        let a = arr2(2, 3, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        let mut t = zeros(&[3, 2]);

        einsum_unary("ab->ba", &a, &mut t).unwrap();

        assert_eq!(t[IxDyn(&[0, 0])], 1.0);
        assert_eq!(t[IxDyn(&[0, 1])], 4.0);
        assert_eq!(t[IxDyn(&[1, 0])], 2.0);
        assert_eq!(t[IxDyn(&[2, 1])], 6.0);
    }

    #[test]
    fn test_dot() {
        let a = arr1(&[1.0, 2.0, 3.0, 4.0]);
        let b = arr1(&[5.0, 6.0, 7.0, 8.0]);

        let result: f64 = einsum_binary_scalar("i,i->", &a, &b).unwrap();
        assert_eq!(result, 70.0);
    }

    #[test]
    fn test_trace() {
        let m = arr2(3, 3, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0]);
        let result: f64 = einsum_unary_scalar("aa->", &m).unwrap();
        assert_eq!(result, 15.0);
    }

    #[test]
    fn test_outer_product() {
        let a = arr1(&[1.0, 2.0, 3.0]);
        let b = arr1(&[4.0, 5.0]);
        let mut c = zeros(&[3, 2]);

        einsum_binary("a,b->ab", &a, &b, &mut c).unwrap();

        assert_eq!(c[IxDyn(&[0, 0])], 4.0);
        assert_eq!(c[IxDyn(&[1, 1])], 10.0);
        assert_eq!(c[IxDyn(&[2, 0])], 12.0);
    }

    #[test]
    fn test_row_sum() {
        let a = arr2(2, 3, &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]);
        let mut out = zeros(&[2]);

        einsum_unary("ab->a", &a, &mut out).unwrap();

        assert_eq!(out[IxDyn(&[0])], 6.0);
        assert_eq!(out[IxDyn(&[1])], 15.0);
    }
}
