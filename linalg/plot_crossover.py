#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib", "numpy"]
# ///
"""Plot the density-crossover bench output (sparse vs BLAS).

Usage: uv run plot_crossover.py crossover.log

Reads the CSV sections emitted by `cargo bench -p linalg --bench crossover
--features blas` and writes crossover_matmul.png and crossover_attention.png
next to the log file. Crossover = density where the sparse curve meets the
BLAS curve.
"""

import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

MATMUL_HDR = "n,density,nnz,csr_us,csr_par_us,blas_us,seq_ratio,par_ratio"
ATTN_HDR = "config,density,q_nz,blas_us,b8_us,b16_us,b8_ratio,b16_ratio"


def parse(path: Path):
    matmul, attn = [], []
    current = None
    for line in path.read_text().splitlines():
        line = line.strip()
        if line == MATMUL_HDR:
            current = matmul
            continue
        if line == ATTN_HDR:
            current = attn
            continue
        if line.startswith("===") or line.startswith("("):
            continue
        if current is None or line.count(",") != 7:
            continue
        current.append(line.split(","))
    return matmul, attn


def f(x):
    return float(x) if x else np.nan


def crossover(dens, ratio):
    """Log-log interpolated density where ratio crosses 1.0."""
    for i in range(len(dens) - 1):
        r0, r1 = ratio[i], ratio[i + 1]
        if np.isnan(r0) or np.isnan(r1):
            continue
        if r0 <= 1.0 < r1:
            t = -np.log(r0) / (np.log(r1) - np.log(r0))
            return np.exp(np.log(dens[i]) + t * (np.log(dens[i + 1]) - np.log(dens[i])))
    return None


def plot_group(ax, rows, key_col, series):
    """rows grouped by rows[key_col]; series = [(col, style, label_suffix)]."""
    keys = list(dict.fromkeys(r[key_col] for r in rows))
    cmap = plt.cm.viridis(np.linspace(0, 0.85, len(keys)))
    for key, color in zip(keys, cmap):
        grp = [r for r in rows if r[key_col] == key]
        dens = np.array([f(r[1]) for r in grp])
        for col, style, suffix in series:
            vals = np.array([f(r[col]) for r in grp])
            ax.plot(dens, vals, style, color=color, label=f"{key} {suffix}")
        # crossover markers vs the BLAS column (last series entry is BLAS)
        blas = np.array([f(r[series[-1][0]]) for r in grp])
        for col, _, suffix in series[:-1]:
            vals = np.array([f(r[col]) for r in grp])
            d = crossover(dens, vals / blas)
            if d is not None:
                t = np.exp(np.interp(np.log(d), np.log(dens[~np.isnan(blas)]),
                                     np.log(blas[~np.isnan(blas)])))
                ax.plot([d], [t], "o", color=color, markersize=9,
                        markerfacecolor="none", markeredgewidth=2)
                ax.annotate(f"{d * 100:.2g}%", (d, t), textcoords="offset points",
                            xytext=(6, -12), fontsize=8, color=color)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("density")
    ax.set_ylabel("time (µs)")
    ax.grid(True, alpha=0.3, which="both")
    ax.legend(fontsize=7)


def main():
    log = Path(sys.argv[1] if len(sys.argv) > 1 else "crossover.log")
    matmul, attn = parse(log)
    outdir = log.resolve().parent

    if matmul:
        fig, ax = plt.subplots(figsize=(9, 6))
        plot_group(ax, matmul, 0, [
            (3, "-", "csr"), (4, ":", "csr_par"), (5, "--", "blas"),
        ])
        ax.set_title("SpGEMM (Csr<u32,f32>) vs BLAS sgemm — circles mark crossover")
        fig.tight_layout()
        fig.savefig(outdir / "crossover_matmul.png", dpi=150)
        print(f"Saved {outdir / 'crossover_matmul.png'}")

    if attn:
        fig, ax = plt.subplots(figsize=(9, 6))
        plot_group(ax, attn, 0, [
            (4, "-", "Blocked8"), (5, ":", "Blocked16"), (3, "--", "blas"),
        ])
        ax.set_title("Blocked attention vs BLAS batched attention — circles mark crossover")
        fig.tight_layout()
        fig.savefig(outdir / "crossover_attention.png", dpi=150)
        print(f"Saved {outdir / 'crossover_attention.png'}")

    if not matmul and not attn:
        sys.exit(f"no CSV sections found in {log}")


if __name__ == "__main__":
    main()
