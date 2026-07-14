//! A GPT-2-shaped decoder-only transformer, run one token at a time on top
//! of the `linalg` einsum VM — loading weights trained by `train.py` and
//! checking its output against the NumPy reference in `gpt2_reference.py`.
//!
//! Every matmul / contraction goes through [`einsum_homogenous`] with the same
//! specs as the Python reference (`"hjd,d->hj"`, `"hj,thj->ht"`, `"ohj,hj->o"`,
//! …). The elementwise pieces the einsum VM doesn't cover — RMSNorm, ReLU,
//! softmax, residual adds — are plain loops over the flat `Dense<f32>` storage.
//!
//! ## Architecture
//!
//! GPT-2 skeleton (learned token + absolute position embeddings, pre-norm
//! blocks, causal self-attention with a KV cache, output projection, MLP) with
//! **RMSNorm** (no gain) instead of LayerNorm, **ReLU** instead of GELU, and no
//! biases anywhere.
//!
//! ## Workflow
//!
//! ```sh
//! uv run examples/gpt2/train.py            # train + export weights/
//! uv run examples/gpt2/gpt2_reference.py   # NumPy reference + ref_logits.bin
//! cargo run --release --example gpt2       # this: same decode, compared
//! ```
//!
//! With no `weights/` directory present it falls back to deterministic random
//! weights (a self-contained smoke test) and skips the comparison.

use std::path::PathBuf;

use linalg::dense::Dense;
use linalg::einsum::einsum_homogenous;

// ─────────────────────────────────────────────────────────────────────────
// Config (loaded at runtime from weights/config.txt)
// ─────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug)]
struct Config {
    vocab: usize,
    n_embd: usize,
    n_head: usize,
    n_layer: usize,
    head_dim: usize,
    mlp_hidden: usize,
    block_size: usize,
    n_generate: usize,
    rms_eps: f32,
}

impl Config {
    /// Fallback config used when no trained weights are present.
    fn default_demo() -> Self {
        Config {
            vocab: 128,
            n_embd: 64,
            n_head: 4,
            n_layer: 3,
            head_dim: 16,
            mlp_hidden: 256,
            block_size: 64,
            n_generate: 12,
            rms_eps: 1e-5,
        }
    }

    fn parse(text: &str) -> Self {
        let mut c = Config::default_demo();
        for line in text.lines() {
            let mut it = line.split_whitespace();
            let (Some(k), Some(v)) = (it.next(), it.next()) else { continue };
            match k {
                "vocab" => c.vocab = v.parse().unwrap(),
                "n_embd" => c.n_embd = v.parse().unwrap(),
                "n_head" => c.n_head = v.parse().unwrap(),
                "n_layer" => c.n_layer = v.parse().unwrap(),
                "head_dim" => c.head_dim = v.parse().unwrap(),
                "mlp_hidden" => c.mlp_hidden = v.parse().unwrap(),
                "block_size" => c.block_size = v.parse().unwrap(),
                "n_generate" => c.n_generate = v.parse().unwrap(),
                "rms_eps" => c.rms_eps = v.parse().unwrap(),
                _ => {}
            }
        }
        c
    }
}

// ─────────────────────────────────────────────────────────────────────────
// einsum helper — allocate the output and run the VM, mirroring Python's `E`.
// ─────────────────────────────────────────────────────────────────────────

fn e(spec: &str, inputs: &[&Dense<f32>], out_shape: Vec<usize>) -> Dense<f32> {
    let mut out = Dense::<f32>::zeros(out_shape);
    einsum_homogenous::<f32, Dense<f32>, Dense<f32>>(spec, inputs, &mut [&mut out])
        .unwrap_or_else(|err| panic!("einsum {spec:?} failed: {err}"));
    out
}

// ─────────────────────────────────────────────────────────────────────────
// Elementwise ops the einsum VM doesn't cover (all over flat storage)
// ─────────────────────────────────────────────────────────────────────────

/// Build a new tensor by applying `f` elementwise (shape preserved).
fn map(x: &Dense<f32>, f: impl Fn(f32) -> f32) -> Dense<f32> {
    Dense { data: x.data.iter().map(|&v| f(v)).collect(), shape: x.shape.clone() }
}

/// Row-vector RMSNorm: `x / sqrt(mean(x²) + eps)`. No learned gain.
fn rmsnorm(x: &Dense<f32>, eps: f32) -> Dense<f32> {
    let ms = x.data.iter().map(|&v| v * v).sum::<f32>() / x.data.len() as f32;
    let inv = 1.0 / (ms + eps).sqrt();
    map(x, |v| v * inv)
}

fn relu(x: &Dense<f32>) -> Dense<f32> {
    map(x, |v| v.max(0.0))
}

fn add(a: &Dense<f32>, b: &Dense<f32>) -> Dense<f32> {
    debug_assert_eq!(a.shape, b.shape);
    Dense {
        data: a.data.iter().zip(&b.data).map(|(&x, &y)| x + y).collect(),
        shape: a.shape.clone(),
    }
}

fn scale(x: &Dense<f32>, s: f32) -> Dense<f32> {
    map(x, |v| v * s)
}

/// Softmax over the last axis (each contiguous run of `last` elements).
fn softmax_last(x: &Dense<f32>) -> Dense<f32> {
    let last = *x.shape.last().unwrap();
    let mut data = x.data.clone();
    for row in data.chunks_mut(last) {
        let m = row.iter().copied().fold(f32::NEG_INFINITY, f32::max);
        let mut sum = 0.0;
        for v in row.iter_mut() {
            *v = (*v - m).exp();
            sum += *v;
        }
        let inv = 1.0 / sum;
        for v in row.iter_mut() {
            *v *= inv;
        }
    }
    Dense { data, shape: x.shape.clone() }
}

// ─────────────────────────────────────────────────────────────────────────
// Weights
// ─────────────────────────────────────────────────────────────────────────

struct Layer {
    wq: Dense<f32>,  // [h, j, d]
    wk: Dense<f32>,  // [h, j, d]
    wv: Dense<f32>,  // [h, j, d]
    wo: Dense<f32>,  // [o, h, j]
    fc1: Dense<f32>, // [mlp_hidden, n_embd]
    fc2: Dense<f32>, // [n_embd, mlp_hidden]
}

struct Model {
    cfg: Config,
    wte: Dense<f32>,     // [vocab, n_embd]
    wpe: Dense<f32>,     // [block_size, n_embd]
    layers: Vec<Layer>,
    lm_head: Dense<f32>, // [vocab, n_embd]
}

/// Sequential f32 reader over `weights.bin`, matching the export order.
struct Blob {
    data: Vec<f32>,
    off: usize,
}
impl Blob {
    fn take(&mut self, shape: Vec<usize>) -> Dense<f32> {
        let n: usize = shape.iter().product();
        let slice = &self.data[self.off..self.off + n];
        self.off += n;
        Dense { data: slice.to_vec(), shape }
    }
}

/// Deterministic small-magnitude weight fill (fallback demo mode).
struct Lcg(u64);
impl Lcg {
    fn tensor(&mut self, shape: Vec<usize>) -> Dense<f32> {
        let mut t = Dense::<f32>::zeros(shape);
        for v in t.data.iter_mut() {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            *v = (((self.0 >> 33) as f32 / u32::MAX as f32) * 2.0 - 1.0) * 0.02;
        }
        t
    }
}

impl Model {
    fn from_blob(cfg: Config, mut b: Blob) -> Self {
        let (h, j, d, o, mlp) = (cfg.n_head, cfg.head_dim, cfg.n_embd, cfg.n_embd, cfg.mlp_hidden);
        let wte = b.take(vec![cfg.vocab, d]);
        let wpe = b.take(vec![cfg.block_size, d]);
        let layers = (0..cfg.n_layer)
            .map(|_| Layer {
                wq: b.take(vec![h, j, d]),
                wk: b.take(vec![h, j, d]),
                wv: b.take(vec![h, j, d]),
                wo: b.take(vec![o, h, j]),
                fc1: b.take(vec![mlp, d]),
                fc2: b.take(vec![d, mlp]),
            })
            .collect();
        let lm_head = b.take(vec![cfg.vocab, d]);
        assert_eq!(b.off, b.data.len(), "weight blob length mismatch");
        Model { cfg, wte, wpe, layers, lm_head }
    }

    fn random(cfg: Config, seed: u64) -> Self {
        let mut r = Lcg(seed);
        let (h, j, d, o, mlp) = (cfg.n_head, cfg.head_dim, cfg.n_embd, cfg.n_embd, cfg.mlp_hidden);
        let layers = (0..cfg.n_layer)
            .map(|_| Layer {
                wq: r.tensor(vec![h, j, d]),
                wk: r.tensor(vec![h, j, d]),
                wv: r.tensor(vec![h, j, d]),
                wo: r.tensor(vec![o, h, j]),
                fc1: r.tensor(vec![mlp, d]),
                fc2: r.tensor(vec![d, mlp]),
            })
            .collect();
        Model {
            cfg,
            wte: r.tensor(vec![cfg.vocab, d]),
            wpe: r.tensor(vec![cfg.block_size, d]),
            layers,
            lm_head: r.tensor(vec![cfg.vocab, d]),
        }
    }
}

/// Row `i` of a `[rows, cols]` dense tensor as a fresh `[cols]` vector.
fn row(t: &Dense<f32>, i: usize) -> Dense<f32> {
    let cols = t.shape[1];
    Dense { data: t.data[i * cols..(i + 1) * cols].to_vec(), shape: vec![cols] }
}

// ─────────────────────────────────────────────────────────────────────────
// KV cache — per layer, a flat [T, n_head, head_dim] buffer that grows by one
// position each decode step.
// ─────────────────────────────────────────────────────────────────────────

struct Cache {
    keys: Vec<Vec<f32>>,
    values: Vec<Vec<f32>>,
    len: usize,
}
impl Cache {
    fn new(n_layer: usize) -> Self {
        Cache { keys: vec![Vec::new(); n_layer], values: vec![Vec::new(); n_layer], len: 0 }
    }
    fn push(&mut self, li: usize, k: &Dense<f32>, v: &Dense<f32>) {
        self.keys[li].extend_from_slice(&k.data);
        self.values[li].extend_from_slice(&v.data);
    }
    fn prefix(&self, li: usize, n_head: usize, head_dim: usize) -> (Dense<f32>, Dense<f32>) {
        let shape = vec![self.len, n_head, head_dim];
        (
            Dense { data: self.keys[li].clone(), shape: shape.clone() },
            Dense { data: self.values[li].clone(), shape },
        )
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Forward: one token at position `pos`, returns logits `[vocab]`.
// ─────────────────────────────────────────────────────────────────────────

fn calculate_step(m: &Model, cache: &mut Cache, token_id: usize, pos: usize) -> Dense<f32> {
    let cfg = m.cfg;
    let head_scale = (cfg.head_dim as f32).sqrt();

    let tok_emb = row(&m.wte, token_id);
    let pos_emb = row(&m.wpe, pos);
    let joint = add(&tok_emb, &pos_emb);
    let mut x = rmsnorm(&joint, cfg.rms_eps); // block_input_0

    cache.len = pos + 1;

    for (li, layer) in m.layers.iter().enumerate() {
        // ── Attention ──
        let attn_residual = x.clone();
        let normed = rmsnorm(&x, cfg.rms_eps);

        let q = e("hjd,d->hj", &[&layer.wq, &normed], vec![cfg.n_head, cfg.head_dim]);
        let k = e("hjd,d->hj", &[&layer.wk, &normed], vec![cfg.n_head, cfg.head_dim]);
        let v = e("hjd,d->hj", &[&layer.wv, &normed], vec![cfg.n_head, cfg.head_dim]);

        cache.push(li, &k, &v);
        let (key_prefix, value_prefix) = cache.prefix(li, cfg.n_head, cfg.head_dim);
        let t = cache.len;

        let logits = e("hj,thj->ht", &[&q, &key_prefix], vec![cfg.n_head, t]);
        let logits = scale(&logits, 1.0 / head_scale);
        let weights = softmax_last(&logits);
        let head_output =
            e("ht,thj->hj", &[&weights, &value_prefix], vec![cfg.n_head, cfg.head_dim]);

        let attn_projected = e("ohj,hj->o", &[&layer.wo, &head_output], vec![cfg.n_embd]);
        x = add(&attn_projected, &attn_residual);

        // ── MLP ──
        let mlp_residual = x.clone();
        let mlp_norm = rmsnorm(&x, cfg.rms_eps);
        let fc1_out = e("od,d->o", &[&layer.fc1, &mlp_norm], vec![cfg.mlp_hidden]);
        let hidden = relu(&fc1_out);
        let fc2_out = e("od,d->o", &[&layer.fc2, &hidden], vec![cfg.n_embd]);
        x = add(&fc2_out, &mlp_residual);
    }

    // No final norm (the reference just copies the last block output).
    e("od,d->o", &[&m.lm_head, &x], vec![cfg.vocab])
}

fn argmax(logits: &Dense<f32>) -> usize {
    logits
        .data
        .iter()
        .enumerate()
        .fold((0usize, f32::NEG_INFINITY), |(bi, bv), (i, &v)| {
            if v > bv { (i, v) } else { (bi, bv) }
        })
        .0
}

// ─────────────────────────────────────────────────────────────────────────
// I/O helpers
// ─────────────────────────────────────────────────────────────────────────

fn weights_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/gpt2/weights")
}

fn read_f32_le(path: &std::path::Path) -> std::io::Result<Vec<f32>> {
    let bytes = std::fs::read(path)?;
    Ok(bytes.chunks_exact(4).map(|c| f32::from_le_bytes([c[0], c[1], c[2], c[3]])).collect())
}

fn main() {
    let dir = weights_dir();
    let cfg_path = dir.join("config.txt");

    // ── Trained mode if weights exist, else a self-contained random demo. ──
    let (model, prompt_tokens, itos, ref_logits) = if cfg_path.exists() {
        let cfg = Config::parse(&std::fs::read_to_string(&cfg_path).unwrap());
        let blob = Blob { data: read_f32_le(&dir.join("weights.bin")).unwrap(), off: 0 };
        let model = Model::from_blob(cfg, blob);

        let vocab_bytes = std::fs::read(dir.join("vocab.bin")).unwrap();
        let itos: Vec<char> = vocab_bytes.iter().map(|&b| b as char).collect();
        let stoi: std::collections::HashMap<char, usize> =
            itos.iter().enumerate().map(|(i, &c)| (c, i)).collect();

        let prompt = std::fs::read_to_string(dir.join("prompt.txt")).unwrap();
        let prompt_tokens: Vec<usize> = prompt.chars().map(|c| stoi[&c]).collect();

        // Reference logits: [n_step, vocab], row-major.
        let ref_logits = read_f32_le(&dir.join("ref_logits.bin")).ok();

        println!(
            "gpt2 (RMSNorm+ReLU) — trained weights, decode on the linalg einsum VM\n\
             config: {:?}\n",
            cfg
        );
        println!("prompt: {prompt:?}");
        (model, prompt_tokens, Some(itos), ref_logits)
    } else {
        let cfg = Config::default_demo();
        println!(
            "gpt2 (RMSNorm+ReLU) — NO trained weights found, using random demo weights\n\
             (run examples/gpt2/train.py to train and compare against the reference)\n"
        );
        (Model::random(cfg, 0x9E3779B97F4A7C15), vec![7, 42, 13, 99], None, None)
    };

    let cfg = model.cfg;
    let mut cache = Cache::new(cfg.n_layer);
    let mut tokens = prompt_tokens.clone();
    let mut pos = 0usize;

    // Feed the prompt (warm the KV cache).
    let mut logits = Dense::<f32>::zeros(vec![cfg.vocab]);
    for &tok in &prompt_tokens {
        logits = calculate_step(&model, &mut cache, tok, pos);
        pos += 1;
    }

    // Greedy generation, recording each step's logits for comparison.
    let mut rust_logits: Vec<Vec<f32>> = Vec::new();
    for _ in 0..cfg.n_generate {
        if pos >= cfg.block_size {
            break;
        }
        rust_logits.push(logits.data.clone());
        let next = argmax(&logits);
        tokens.push(next);
        logits = calculate_step(&model, &mut cache, next, pos);
        pos += 1;
    }

    // ── Report ──
    if let Some(itos) = &itos {
        let text: String = tokens.iter().map(|&t| itos[t]).collect();
        println!("output: {text:?}");
    }
    println!("tokens: {tokens:?}");

    // ── Compare against the NumPy reference ──
    if let Some(reference) = ref_logits {
        let vocab = cfg.vocab;
        let n_ref = reference.len() / vocab;
        let n = n_ref.min(rust_logits.len());
        let mut max_abs = 0.0f32;
        let mut argmax_matches = 0usize;
        for s in 0..n {
            let ref_row = &reference[s * vocab..(s + 1) * vocab];
            let rust_row = &rust_logits[s];
            for (a, b) in ref_row.iter().zip(rust_row) {
                max_abs = max_abs.max((a - b).abs());
            }
            let ref_arg = ref_row
                .iter()
                .enumerate()
                .fold((0usize, f32::NEG_INFINITY), |(bi, bv), (i, &v)| {
                    if v > bv { (i, v) } else { (bi, bv) }
                })
                .0;
            if ref_arg == argmax(&Dense { data: rust_row.clone(), shape: vec![vocab] }) {
                argmax_matches += 1;
            }
        }
        println!("\n── comparison vs NumPy reference ──");
        println!("steps compared     : {n}");
        println!("max abs logit diff : {max_abs:.3e}");
        println!("argmax agreement   : {argmax_matches}/{n}");
        if argmax_matches == n && max_abs < 1e-2 {
            println!("RESULT: MATCH ✓");
        } else {
            println!("RESULT: MISMATCH ✗");
        }
    } else if itos.is_some() {
        println!("\n(no ref_logits.bin — run gpt2_reference.py to enable the comparison)");
    }
}
