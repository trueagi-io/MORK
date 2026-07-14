# /// script
# requires-python = ">=3.9"
# dependencies = ["torch", "numpy"]
# ///
"""
Trivial nanoGPT-style trainer for the RMSNorm+ReLU GPT-2 variant that the
Rust `examples/gpt2` runs.

It defines the architecture with `torch.einsum` using the *exact same specs*
as `example_gpt.py` / the Rust example (`hjd,btd->bthj`, `ohj,bthj->bto`, …),
trains it char-level on a small embedded corpus, and exports the weights in a
fixed binary layout that both `gpt2_reference.py` (NumPy) and `main.rs` load.

Run:  uv run examples/gpt2/train.py
"""

import os
import struct

import numpy as np
import torch
import torch.nn.functional as F

torch.manual_seed(1337)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "weights")

# ── Config (kept tiny so CPU training takes seconds) ────────────────────────
N_EMBD = 64
N_HEAD = 4
N_LAYER = 3
HEAD_DIM = N_EMBD // N_HEAD
MLP_HIDDEN = 4 * N_EMBD
BLOCK_SIZE = 32
RMS_EPS = 1e-5

BATCH = 32
STEPS = 1500
LR = 3e-3
N_GENERATE = 128  # how many tokens the reference/rust will greedily generate

# ── Corpus (original ASCII text; repeated to give a small model structure) ──
CORPUS = (
    "the sparse tensor hums a quiet tune. "
    "rows and columns fold into one another, "
    "and every einsum spells the same small song. "
    "dense or sparse, the answer must agree. "
    "a matrix walks into a norm and leaves it whole. "
    "we train a tiny mind on tiny words, "
    "then ask the rust to speak them back to us. "
) * 12

# ── Vocab ───────────────────────────────────────────────────────────────────
chars = sorted(set(CORPUS))
assert all(ord(c) < 128 for c in chars), "corpus must be ASCII (one byte per token)"
VOCAB = len(chars)
stoi = {c: i for i, c in enumerate(chars)}
itos = {i: c for i, c in enumerate(chars)}
data = torch.tensor([stoi[c] for c in CORPUS], dtype=torch.long)


def get_batch():
    ix = torch.randint(0, len(data) - BLOCK_SIZE - 1, (BATCH,))
    x = torch.stack([data[i : i + BLOCK_SIZE] for i in ix])
    y = torch.stack([data[i + 1 : i + 1 + BLOCK_SIZE] for i in ix])
    return x, y


def rmsnorm(x):
    # No learned gain, matching the single-argument reference rmsnorm(x).
    return x * torch.rsqrt(x.pow(2).mean(-1, keepdim=True) + RMS_EPS)


def p(*shape):
    """A trainable parameter with small init, shape in the export layout."""
    return torch.nn.Parameter(torch.randn(*shape) * 0.02)


class GPT(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.wte = p(VOCAB, N_EMBD)
        self.wpe = p(BLOCK_SIZE, N_EMBD)
        self.wq = torch.nn.ParameterList([p(N_HEAD, HEAD_DIM, N_EMBD) for _ in range(N_LAYER)])
        self.wk = torch.nn.ParameterList([p(N_HEAD, HEAD_DIM, N_EMBD) for _ in range(N_LAYER)])
        self.wv = torch.nn.ParameterList([p(N_HEAD, HEAD_DIM, N_EMBD) for _ in range(N_LAYER)])
        self.wo = torch.nn.ParameterList([p(N_EMBD, N_HEAD, HEAD_DIM) for _ in range(N_LAYER)])
        self.fc1 = torch.nn.ParameterList([p(MLP_HIDDEN, N_EMBD) for _ in range(N_LAYER)])
        self.fc2 = torch.nn.ParameterList([p(N_EMBD, MLP_HIDDEN) for _ in range(N_LAYER)])
        self.lm_head = p(VOCAB, N_EMBD)

    def forward(self, idx):
        B, T = idx.shape
        scale = HEAD_DIM ** 0.5
        # causal mask: key position s may not exceed query position t
        mask = torch.tril(torch.ones(T, T)).view(1, 1, T, T)

        h = self.wte[idx] + self.wpe[:T]          # [B,T,d]
        h = rmsnorm(h)                            # initial norm on embeddings

        for li in range(N_LAYER):
            res = h
            xn = rmsnorm(h)
            q = torch.einsum("hjd,btd->bthj", self.wq[li], xn)
            k = torch.einsum("hjd,btd->bthj", self.wk[li], xn)
            v = torch.einsum("hjd,btd->bthj", self.wv[li], xn)
            att = torch.einsum("bthj,bshj->bhts", q, k) / scale   # [B,h,Tq,Tk]
            att = att.masked_fill(mask == 0, float("-inf"))
            att = F.softmax(att, dim=-1)
            out = torch.einsum("bhts,bshj->bthj", att, v)
            proj = torch.einsum("ohj,bthj->bto", self.wo[li], out)
            h = proj + res

            res2 = h
            xn2 = rmsnorm(h)
            f1 = torch.relu(torch.einsum("od,btd->bto", self.fc1[li], xn2))
            f2 = torch.einsum("oh,bth->bto", self.fc2[li], f1)
            h = f2 + res2

        return torch.einsum("od,btd->bto", self.lm_head, h)   # [B,T,vocab]


model = GPT()
opt = torch.optim.AdamW(model.parameters(), lr=LR)

for step in range(STEPS):
    x, y = get_batch()
    logits = model(x)
    loss = F.cross_entropy(logits.reshape(-1, VOCAB), y.reshape(-1))
    opt.zero_grad(set_to_none=True)
    loss.backward()
    opt.step()
    if step % 100 == 0 or step == STEPS - 1:
        print(f"step {step:4d}  loss {loss.item():.4f}")

# ── Export ──────────────────────────────────────────────────────────────────
os.makedirs(OUT, exist_ok=True)


def wf(fh, t):
    fh.write(t.detach().cpu().numpy().astype("<f4").tobytes())


with open(os.path.join(OUT, "weights.bin"), "wb") as fh:
    wf(fh, model.wte)
    wf(fh, model.wpe)
    for li in range(N_LAYER):
        wf(fh, model.wq[li])
        wf(fh, model.wk[li])
        wf(fh, model.wv[li])
        wf(fh, model.wo[li])
        wf(fh, model.fc1[li])
        wf(fh, model.fc2[li])
    wf(fh, model.lm_head)

with open(os.path.join(OUT, "config.txt"), "w") as fh:
    for k, v in [
        ("vocab", VOCAB), ("n_embd", N_EMBD), ("n_head", N_HEAD),
        ("n_layer", N_LAYER), ("head_dim", HEAD_DIM), ("mlp_hidden", MLP_HIDDEN),
        ("block_size", BLOCK_SIZE), ("n_generate", N_GENERATE),
    ]:
        fh.write(f"{k} {v}\n")
    fh.write(f"rms_eps {RMS_EPS}\n")

# vocab.bin: byte i is the ASCII char for token i (single-byte guaranteed above)
with open(os.path.join(OUT, "vocab.bin"), "wb") as fh:
    fh.write(bytes(ord(itos[i]) for i in range(VOCAB)))

# prompt: first few chars of the corpus, no trailing newline
prompt = CORPUS[:8]
with open(os.path.join(OUT, "prompt.txt"), "wb") as fh:
    fh.write(prompt.encode("ascii"))

print(f"\nexported weights + config to {OUT}")
print(f"prompt: {prompt!r}  vocab: {VOCAB} chars")
