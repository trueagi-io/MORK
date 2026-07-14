# GPT-2 on the `linalg` einsum VM

A small GPT-2-shaped decoder-only transformer whose every matmul / contraction
runs through `linalg`'s einsum VM. It exists to show that the *linear algebra*
of a full transformer forward pass — the QKV / attention / output / MLP / LM-head
contractions — expresses as einsum, and to check the Rust implementation against
a Python reference bit-for-bit (modulo float summation order).

The einsum VM handles only the contractions. The elementwise and reduction
steps — RMSNorm, ReLU, softmax, residual adds, the `1/sqrt(head_dim)` scale —
are *not* einsum; they're plain loops over the flat `Dense<f32>` storage (see
[Architecture](#architecture) for which spec each contraction uses).

The same architecture is written **three times against one set of einsum specs**:

| File | Backend | Role |
|---|---|---|
| `train.py` | PyTorch (`torch.einsum`) | trains the model, exports weights |
| `gpt2_reference.py` | NumPy (`np.einsum`) | reference forward, dumps logits |
| `main.rs` | `linalg` einsum VM | the example, compared against the reference |

## Architecture

GPT-2 skeleton with two modern substitutions (this is why it is **not** a real
GPT-2 checkpoint and has nothing to download):

- Learned **token + absolute position** embeddings (`wte` + `wpe`), added and
  then passed through an initial RMSNorm.
- Pre-norm blocks: causal self-attention (with a KV cache) + a two-layer MLP,
  each wrapped in a residual around the *pre-norm* value.
- **RMSNorm** instead of LayerNorm — no learned gain, no bias.
- **ReLU** MLP activation instead of GELU.
- No biases anywhere; every projection is a pure einsum.
- No final norm before the LM head (the reference just copies the last block
  output).

The einsum specs, shared across all three implementations (batch/position axes
`b`,`t`,`s` added in the training/reference forwards):

| step | spec (decode) | meaning |
|---|---|---|
| Q/K/V projection | `hjd,d->hj` | per-head weight `[h,j,d]` · normed `[d]` |
| attention logits | `hj,thj->ht` | query `[h,j]` · cached keys `[t,h,j]` |
| head output | `ht,thj->hj` | weights `[h,t]` · cached values `[t,h,j]` |
| output projection | `ohj,hj->o` | `wo [o,h,j]` · heads `[h,j]` |
| MLP / LM head | `od,d->o` | dense weight `[o,d]` · `[d]` |

The elementwise pieces the einsum VM doesn't cover — RMSNorm, ReLU, softmax,
residual adds, the `1/sqrt(head_dim)` scale — are plain loops over the flat
`Dense<f32>` storage.

## Running

```sh
# 1. Train (PyTorch, CPU, ~15 s after the one-time torch download) and export
#    weights/ (weights.bin, config.txt, vocab.bin, prompt.txt).
uv run examples/gpt2/train.py

# 2. NumPy reference forward: greedy-decode and write weights/ref_logits.bin.
uv run examples/gpt2/gpt2_reference.py

# 3. The Rust example: load the same weights, decode through the linalg einsum
#    VM, and compare its logits against the reference.
cargo run --release --example gpt2
```

`uv` is used per the repo convention — no manual venv needed; dependencies are
declared inline (PEP 723) at the top of each script.

Expected tail of step 3:

```
prompt: "the spar"
output: "the sparse tensor hums a quiet t"
tokens: [21, 10, 7, 0, 20, 17, 3, 19, ...]

── comparison vs NumPy reference ──
steps compared     : 24
max abs logit diff : 1.717e-5
argmax agreement   : 24/24
RESULT: MATCH ✓
```

The `~1e-5` residual is float32 summation-order difference between the linalg
VM, NumPy, and PyTorch; the greedy token streams are identical.

### Running without the trained weights

`cargo run --release --example gpt2` works with no `weights/` directory: it
falls back to deterministic random weights (a self-contained smoke test that
just exercises the einsum forward pass) and skips the comparison.

## Retraining / reconfiguring

Model size, corpus, and training length live at the top of `train.py`
(`N_EMBD`, `N_HEAD`, `N_LAYER`, `MLP_HIDDEN`, `BLOCK_SIZE`, `STEPS`, `CORPUS`,
`N_GENERATE`). The exported `config.txt` carries the dims, so after retraining
the NumPy reference and the Rust example pick up the new shape automatically —
no code changes needed. Re-run steps 2 and 3 after any retrain so
`ref_logits.bin` matches the new weights.

The checked-in `weights/` is the model produced by the committed `train.py`, so
steps 2–3 run out of the box without retraining.

## Files

```
examples/gpt2/
├── README.md            this file
├── train.py             PyTorch trainer + weight exporter
├── gpt2_reference.py    NumPy reference forward + logit dump
├── main.rs              the linalg example (loads weights, decodes, compares)
└── weights/             exported model + reference logits
    ├── config.txt       dims (vocab, n_embd, n_head, n_layer, …)
    ├── weights.bin      all parameters, row-major f32 LE, fixed order
    ├── vocab.bin        byte i = ASCII char for token i
    ├── prompt.txt       the decode prompt
    └── ref_logits.bin   NumPy per-step logits [n_step, vocab] for comparison
```

The `weights.bin` byte layout (matching `train.py`'s export and `main.rs`'s
loader): `wte`, `wpe`, then for each layer `wq, wk, wv, wo, fc1, fc2`, then
`lm_head` — each a contiguous row-major f32 block.
