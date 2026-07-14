# /// script
# requires-python = ">=3.9"
# dependencies = ["numpy"]
# ///
"""
NumPy reference forward for the RMSNorm+ReLU GPT-2 variant — the Python
implementation to compare the Rust `examples/gpt2` against.

Loads the weights exported by `train.py`, runs a full-context causal forward
with `np.einsum` (same specs as the reference decode step), greedy-decodes
`n_generate` tokens, prints the decoded text, and dumps the per-step
last-position logits to `weights/ref_logits.bin` so the Rust example can load
them and report the max abs difference.

Run:  uv run examples/gpt2/gpt2_reference.py
"""

import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "weights")


def load_config():
    cfg = {}
    with open(os.path.join(OUT, "config.txt")) as fh:
        for line in fh:
            k, v = line.split()
            cfg[k] = float(v) if k == "rms_eps" else int(v)
    return cfg


cfg = load_config()
VOCAB = cfg["vocab"]
N_EMBD = cfg["n_embd"]
N_HEAD = cfg["n_head"]
N_LAYER = cfg["n_layer"]
HEAD_DIM = cfg["head_dim"]
MLP_HIDDEN = cfg["mlp_hidden"]
BLOCK_SIZE = cfg["block_size"]
N_GENERATE = cfg["n_generate"]
RMS_EPS = cfg["rms_eps"]

# ── Load weights in the exported order ──────────────────────────────────────
blob = np.fromfile(os.path.join(OUT, "weights.bin"), dtype="<f4")
_off = 0


def take(*shape):
    global _off
    n = int(np.prod(shape))
    a = blob[_off : _off + n].reshape(shape).astype(np.float32)
    _off += n
    return a


wte = take(VOCAB, N_EMBD)
wpe = take(BLOCK_SIZE, N_EMBD)
layers = []
for _ in range(N_LAYER):
    layers.append(dict(
        wq=take(N_HEAD, HEAD_DIM, N_EMBD),
        wk=take(N_HEAD, HEAD_DIM, N_EMBD),
        wv=take(N_HEAD, HEAD_DIM, N_EMBD),
        wo=take(N_EMBD, N_HEAD, HEAD_DIM),
        fc1=take(MLP_HIDDEN, N_EMBD),
        fc2=take(N_EMBD, MLP_HIDDEN),
    ))
lm_head = take(VOCAB, N_EMBD)
assert _off == blob.size, f"weight blob leftover: {_off} vs {blob.size}"

with open(os.path.join(OUT, "vocab.bin"), "rb") as fh:
    itos = [chr(b) for b in fh.read()]
stoi = {c: i for i, c in enumerate(itos)}


def rmsnorm(x):  # over last axis, no gain
    ms = np.mean(x * x, axis=-1, keepdims=True)
    return x / np.sqrt(ms + RMS_EPS)


def forward(tokens):
    """Full causal forward over `tokens`; returns logits for every position [T, vocab]."""
    T = len(tokens)
    scale = HEAD_DIM ** 0.5
    mask = np.tril(np.ones((T, T), dtype=bool))

    h = wte[tokens] + wpe[:T]        # [T, d]
    h = rmsnorm(h)

    for L in layers:
        res = h
        xn = rmsnorm(h)
        q = np.einsum("hjd,td->thj", L["wq"], xn)
        k = np.einsum("hjd,td->thj", L["wk"], xn)
        v = np.einsum("hjd,td->thj", L["wv"], xn)
        att = np.einsum("thj,shj->hts", q, k) / scale        # [h, Tq, Tk]
        att = np.where(mask[None], att, -np.inf)
        att = att - att.max(-1, keepdims=True)
        att = np.exp(att)
        att = att / att.sum(-1, keepdims=True)
        out = np.einsum("hts,shj->thj", att, v)
        proj = np.einsum("ohj,thj->to", L["wo"], out)
        h = proj + res

        res2 = h
        xn2 = rmsnorm(h)
        f1 = np.maximum(np.einsum("od,td->to", L["fc1"], xn2), 0.0)
        f2 = np.einsum("oh,th->to", L["fc2"], f1)
        h = f2 + res2

    return np.einsum("od,td->to", lm_head, h)   # [T, vocab]


# ── Greedy decode, recording each step's logits ─────────────────────────────
with open(os.path.join(OUT, "prompt.txt"), "rb") as fh:
    prompt = fh.read().decode("ascii")
tokens = [stoi[c] for c in prompt]

step_logits = []
for _ in range(N_GENERATE):
    if len(tokens) >= BLOCK_SIZE:
        break
    logits = forward(tokens)[-1]     # last position
    step_logits.append(logits.astype("<f4"))
    tokens.append(int(np.argmax(logits)))

np.stack(step_logits).tofile(os.path.join(OUT, "ref_logits.bin"))

text = "".join(itos[t] for t in tokens)
print(f"prompt : {prompt!r}")
print(f"output : {text!r}")
print(f"tokens : {tokens}")
print(f"\nwrote {len(step_logits)} steps of logits to weights/ref_logits.bin")
