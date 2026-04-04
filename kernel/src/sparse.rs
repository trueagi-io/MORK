use std::collections::HashMap;
use std::hash::Hasher;
use num_traits::Zero;
use pathmap::PathMap;
use pathmap::ring::{AlgebraicResult, Lattice};
use pathmap::utils::ints::indices_to_bob;

// ============================================================================
// FAddMulF64 — Lattice wrapper for f64 (join=add, meet=mul)
// ============================================================================

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct FAddMulF64(pub f64);

impl std::ops::Deref for FAddMulF64 {
    type Target = f64;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl std::hash::Hash for FAddMulF64 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Lattice for FAddMulF64 {
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        if self.0.is_zero() { return AlgebraicResult::Identity(1) }
        if other.0.is_zero() { return AlgebraicResult::Identity(2) }
        let s = self.0 + other.0;
        if self.0 * other.0 < 0f64 && s.abs() < 1e-15 { return AlgebraicResult::None }
        AlgebraicResult::Element(FAddMulF64(s))
    }

    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        let s = self.0 * other.0;
        if s.abs() < 1e-15 { return AlgebraicResult::None }
        AlgebraicResult::Element(FAddMulF64(s))
    }
}

// ============================================================================
// SparseTensorF64 — PathMap-backed sparse tensor with BOB encoding
// ============================================================================

pub struct SparseTensorF64 {
    pub m: PathMap<f64>,
    pub d: usize,
    pub dims: Vec<usize>,
    p: Vec<u8>,
}

impl SparseTensorF64 {
    pub fn new(rank: usize) -> Self {
        Self { m: PathMap::new(), d: rank, dims: vec![0; rank], p: Vec::new() }
    }

    pub fn with_dims(dims: Vec<usize>) -> Self {
        let d = dims.len();
        Self { m: PathMap::new(), d, dims, p: Vec::new() }
    }

    pub fn set(&mut self, ix: &[usize], v: f64) {
        for (i, &idx) in ix.iter().enumerate() {
            if idx >= self.dims[i] {
                self.dims[i] = idx + 1;
            }
        }
        let path = Self::index_to_path_static(ix);
        self.m.insert(&path[..], v);
    }

    pub fn get(&self, ix: &[usize]) -> Option<f64> {
        let path = Self::index_to_path_static(ix);
        self.m.get(&path[..]).copied()
    }

    pub fn remove(&mut self, ix: &[usize]) -> Option<f64> {
        let path = Self::index_to_path_static(ix);
        self.m.remove(&path[..])
    }

    pub fn nnz(&self) -> usize {
        self.m.val_count()
    }

    fn index_to_path_static(ix: &[usize]) -> Vec<u8> {
        let mut p = Vec::new();
        let len = indices_to_bob(ix, &mut vec![]);
        p.extend(std::iter::repeat_n(0u8, 64 - len));
        indices_to_bob(ix, &mut p);
        p
    }

    // Safety: FAddMulF64 has the same layout as f64
    fn vf(&self) -> &PathMap<FAddMulF64> {
        unsafe { (&self.m as *const PathMap<f64> as *const PathMap<FAddMulF64>).as_ref().unwrap_unchecked() }
    }

    fn from_vf(m: PathMap<FAddMulF64>, d: usize, dims: Vec<usize>) -> Self {
        unsafe { Self { m: std::mem::transmute::<PathMap<FAddMulF64>, PathMap<f64>>(m), d, dims, p: Vec::new() } }
    }

    pub fn add(&self, other: &Self) -> Self {
        let dims = self.dims.iter().zip(&other.dims).map(|(&a, &b)| a.max(b)).collect();
        Self::from_vf(self.vf().join(other.vf()), self.d, dims)
    }

    pub fn mul(&self, other: &Self) -> Self {
        let dims = self.dims.iter().zip(&other.dims).map(|(&a, &b)| a.max(b)).collect();
        Self::from_vf(self.vf().meet(other.vf()), self.d, dims)
    }
}

// ============================================================================
// NDIndex<f64> implementation for einsum-dyn compatibility
// ============================================================================

impl einsum_dyn::NDIndex<f64> for SparseTensorF64 {
    fn ndim(&self) -> usize { self.d }
    fn dim(&self, axis: usize) -> usize { self.dims[axis] }

    fn get(&self, indices: &[usize]) -> f64 {
        self.get(indices).unwrap_or(0.0)
    }

    fn set(&mut self, indices: &[usize], val: f64) {
        if val.abs() < 1e-15 {
            self.remove(indices);
        } else {
            self.set(indices, val);
        }
    }

    fn get_opt(&self, indices: &[usize]) -> Option<f64> {
        self.get(indices)
    }

    fn is_sparse_2d(&self) -> bool { false }
}

// ============================================================================
// Pure functions (access tensor store via ExprSource.context)
// ============================================================================

use eval_ffi::{ExprSource, ExprSink, EvalError};
use mork_expr::SourceItem;
use eval::{EvalScope, FuncType};

/// Read tensor store from the ExprSource context pointer.
/// The context is set by PureSink via ASink::set_context before eval.
unsafe fn tensor_store_from_context(expr: &ExprSource) -> Option<&HashMap<Vec<u8>, SparseTensorF64>> {
    (expr.context as *const HashMap<Vec<u8>, SparseTensorF64>).as_ref()
}

/// (tensor_get name i0 i1 ... iN) -> f64 value at that index
pub extern "C" fn tensor_get(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"tensor_get")?;
    if items < 2 { return Err(EvalError::from("tensor_get requires name and indices")) }

    let SourceItem::Symbol(name) = expr.read() else {
        return Err(EvalError::from("tensor_get: first arg must be tensor name"))
    };
    let name = name.to_vec();

    let mut indices: Vec<usize> = Vec::new();
    for _ in 0..(items - 1) {
        let SourceItem::Symbol(idx_bytes) = expr.read() else {
            return Err(EvalError::from("tensor_get: index must be a symbol"))
        };
        let idx = std::str::from_utf8(idx_bytes)
            .map_err(|_| EvalError::from("tensor_get: index not utf8"))?
            .parse::<usize>()
            .map_err(|_| EvalError::from("tensor_get: index not a number"))?;
        indices.push(idx);
    }

    let store = unsafe { tensor_store_from_context(expr) };
    let val = store
        .and_then(|s| s.get(&name))
        .and_then(|t| t.get(&indices))
        .unwrap_or(0.0);

    sink.write(SourceItem::Symbol(&val.to_be_bytes()[..]))?;
    Ok(())
}

/// (tensor_nnz name) -> u64 count of non-zeros
pub extern "C" fn tensor_nnz(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"tensor_nnz")?;
    if items != 1 { return Err(EvalError::from("tensor_nnz takes one argument")) }

    let SourceItem::Symbol(name) = expr.read() else {
        return Err(EvalError::from("tensor_nnz: arg must be tensor name"))
    };
    let name = name.to_vec();

    let store = unsafe { tensor_store_from_context(expr) };
    let nnz = store
        .and_then(|s| s.get(&name))
        .map(|t| t.nnz())
        .unwrap_or(0) as u64;

    sink.write(SourceItem::Symbol(&nnz.to_be_bytes()[..]))?;
    Ok(())
}

pub fn register(scope: &mut EvalScope) {
    scope.add_func("tensor_get", tensor_get, FuncType::Pure);
    scope.add_func("tensor_nnz", tensor_nnz, FuncType::Pure);
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sparse_tensor_basic() {
        let mut t = SparseTensorF64::new(2);
        t.set(&[0, 1], 3.0);
        t.set(&[1, 2], 5.0);
        t.set(&[2, 0], 7.0);

        assert_eq!(t.get(&[0, 1]), Some(3.0));
        assert_eq!(t.get(&[1, 2]), Some(5.0));
        assert_eq!(t.get(&[2, 0]), Some(7.0));
        assert_eq!(t.get(&[0, 0]), None);
        assert_eq!(t.nnz(), 3);
        assert_eq!(t.dims, vec![3, 3]);
    }

    #[test]
    fn test_sparse_tensor_4d() {
        let mut t = SparseTensorF64::new(4);
        t.set(&[1, 2, 3, 4], 42.0);
        t.set(&[0, 0, 0, 0], 1.0);

        assert_eq!(t.get(&[1, 2, 3, 4]), Some(42.0));
        assert_eq!(t.get(&[0, 0, 0, 0]), Some(1.0));
        assert_eq!(t.get(&[1, 1, 1, 1]), None);
        assert_eq!(t.nnz(), 2);
    }

    #[test]
    fn test_sparse_tensor_add() {
        let mut a = SparseTensorF64::new(2);
        a.set(&[0, 0], 1.0);
        a.set(&[0, 1], 2.0);

        let mut b = SparseTensorF64::new(2);
        b.set(&[0, 0], 10.0);
        b.set(&[1, 0], 20.0);

        let c = a.add(&b);
        assert_eq!(c.get(&[0, 0]), Some(11.0));
        assert_eq!(c.get(&[0, 1]), Some(2.0));
        assert_eq!(c.get(&[1, 0]), Some(20.0));
    }

    #[test]
    fn test_sparse_tensor_mul() {
        let mut a = SparseTensorF64::new(2);
        a.set(&[0, 0], 3.0);
        a.set(&[0, 1], 5.0);

        let mut b = SparseTensorF64::new(2);
        b.set(&[0, 0], 2.0);
        b.set(&[1, 1], 4.0);

        let c = a.mul(&b);
        assert_eq!(c.get(&[0, 0]), Some(6.0));
        assert_eq!(c.get(&[0, 1]), None);
        assert_eq!(c.get(&[1, 1]), None);
    }

    #[test]
    fn test_ndindex_impl() {
        use einsum_dyn::NDIndex;
        let mut t = SparseTensorF64::with_dims(vec![3, 3]);
        <SparseTensorF64 as NDIndex<f64>>::set(&mut t, &[0, 1], 5.0);
        assert_eq!(<SparseTensorF64 as NDIndex<f64>>::get(&t, &[0, 1]), 5.0);
        assert_eq!(<SparseTensorF64 as NDIndex<f64>>::get(&t, &[0, 0]), 0.0);
        assert_eq!(t.get_opt(&[0, 1]), Some(5.0));
        assert_eq!(t.get_opt(&[0, 0]), None);
    }

    #[test]
    fn test_einsum_matmul() {
        use einsum_dyn::NDIndex;
        let mut a = SparseTensorF64::with_dims(vec![2, 2]);
        a.set(&[0, 0], 1.0); a.set(&[0, 1], 2.0);
        a.set(&[1, 0], 3.0); a.set(&[1, 1], 4.0);

        let mut b = SparseTensorF64::with_dims(vec![2, 2]);
        b.set(&[0, 0], 5.0); b.set(&[0, 1], 6.0);
        b.set(&[1, 0], 7.0); b.set(&[1, 1], 8.0);

        let mut c = SparseTensorF64::with_dims(vec![2, 2]);

        let inputs: Vec<&dyn einsum_dyn::NDIndex<f64>> = vec![&a, &b];
        let mut out: &mut dyn einsum_dyn::NDIndex<f64> = &mut c;
        einsum_dyn::sparse::einsum_vm_oneshot_dyn("ab,bc->ac", &inputs, &mut [out]).unwrap();

        assert_eq!(<SparseTensorF64 as NDIndex<f64>>::get(&c, &[0, 0]), 19.0);
        assert_eq!(<SparseTensorF64 as NDIndex<f64>>::get(&c, &[0, 1]), 22.0);
        assert_eq!(<SparseTensorF64 as NDIndex<f64>>::get(&c, &[1, 0]), 43.0);
        assert_eq!(<SparseTensorF64 as NDIndex<f64>>::get(&c, &[1, 1]), 50.0);
    }

    #[test]
    fn test_end_to_end_collect_einsum() {
        use crate::space::Space;

        let mut s = Space::new();

        // Load matrix A = [[1, 2], [3, 4]] as (a row col val) triples
        // Load matrix B = [[5, 6], [7, 8]] as (b row col val) triples
        // Matrix A = [[1, 2], [3, 4]], B = [[5, 6], [7, 8]]
        // Store as (a row col val) triples, collect into tensors, einsum, check result
        s.add_all_sexpr(r#"
            (a 0 0 1.0)
            (a 0 1 2.0)
            (a 1 0 3.0)
            (a 1 1 4.0)

            (b 0 0 5.0)
            (b 0 1 6.0)
            (b 1 0 7.0)
            (b 1 1 8.0)

            (exec P1 (, (a $r $c $v)) (O (tensor_collect A $r $c $v)))
            (exec P2 (, (b $r $c $v)) (O (tensor_collect B $r $c $v)))
            (exec P3 (,) (O (tensor_einsum "ab,bc->ac" A B C)))
        "#.as_bytes()).unwrap();

        s.metta_calculus(100);

        // Verify tensors were collected
        assert!(s.tensors.contains_key(b"A".as_slice()), "tensor A should exist");
        assert!(s.tensors.contains_key(b"B".as_slice()), "tensor B should exist");
        assert!(s.tensors.contains_key(b"C".as_slice()), "tensor C should exist");

        let a = s.tensors.get(b"A".as_slice()).unwrap();
        assert_eq!(a.nnz(), 4);
        assert_eq!(a.get(&[0, 0]), Some(1.0));
        assert_eq!(a.get(&[1, 1]), Some(4.0));

        let b = s.tensors.get(b"B".as_slice()).unwrap();
        assert_eq!(b.nnz(), 4);

        // C = A * B = [[19, 22], [43, 50]]
        let c = s.tensors.get(b"C".as_slice()).unwrap();
        assert_eq!(c.get(&[0, 0]), Some(19.0));
        assert_eq!(c.get(&[0, 1]), Some(22.0));
        assert_eq!(c.get(&[1, 0]), Some(43.0));
        assert_eq!(c.get(&[1, 1]), Some(50.0));

        // Phase 2: test tensor_get directly through EvalScope
        {
            use eval_ffi::ExprSource;
            let mut scope = eval::EvalScope::new();
            crate::sparse::register(&mut scope);
            scope.context = (&s.tensors as *const HashMap<Vec<u8>, SparseTensorF64>).cast_mut().cast();

            // Build expression: (tensor_get C 0 0)
            let expr_bytes = mork_expr::construct!("tensor_get" "C" "0" "0").unwrap();
            let result = scope.eval(ExprSource::new(expr_bytes.as_ptr())).unwrap();
            // Result is SymbolSize(8) + 8 bytes of f64
            assert_eq!(result.len(), 9, "tensor_get should return 9 bytes (tag + f64)");
            let val = f64::from_be_bytes(result[1..9].try_into().unwrap());
            assert!((val - 19.0).abs() < 1e-10, "tensor_get C 0 0 = {} expected 19.0", val);

            let expr_bytes = mork_expr::construct!("tensor_get" "C" "1" "1").unwrap();
            let result = scope.eval(ExprSource::new(expr_bytes.as_ptr())).unwrap();
            let val = f64::from_be_bytes(result[1..9].try_into().unwrap());
            assert!((val - 50.0).abs() < 1e-10, "tensor_get C 1 1 = {} expected 50.0", val);
        }
    }
}
