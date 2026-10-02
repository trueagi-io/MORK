#!/usr/bin/env python3
"""Measure the three-stage mm2 -> ACT pipeline with native peak-RSS reporting.

Usage: python3 kernel/bench_scripts/streaming_conversion.py INPUT.mm2 [--memory-mib 1024]
Results, artifacts, and native time logs are kept in --output-dir.
"""
import argparse
import json
from pathlib import Path
import platform
import re
import subprocess
import time


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--mork", type=Path, default=root / "target/release/mork")
    parser.add_argument("--output-dir", type=Path, default=root / "target/conversion-benchmark")
    parser.add_argument("--memory-mib", type=int, default=1024)
    args = parser.parse_args()
    system = platform.system()
    if system not in ("Darwin", "Linux"):
        parser.error("peak RSS measurement requires macOS or Linux /usr/bin/time")
    if args.memory_mib < 1:
        parser.error("--memory-mib must be at least 1")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    outputs = [args.output_dir / name for name in ("bean.upaths", "bean.paths", "bean.act")]
    stages = [
        ("mm2", "upaths", args.input, outputs[0]),
        ("upaths", "paths", outputs[0], outputs[1]),
        ("paths", "act", outputs[1], outputs[2]),
    ]
    report = {
        "input": str(args.input.resolve()),
        "input_bytes": args.input.stat().st_size,
        "platform": platform.platform(),
        "memory_mib": args.memory_mib,
        "stages": [],
    }
    started = time.perf_counter()
    for source, target, input_path, output_path in stages:
        name = f"{source}-{target}"
        time_path = args.output_dir / f"{name}.time"
        command = [str(args.mork), "convert", source, target, str(input_path), str(output_path),
                   "--memory-mib", str(args.memory_mib), "--temp-dir", str(args.output_dir)]
        stage_start = time.perf_counter()
        with (args.output_dir / f"{name}.log").open("w") as log:
            subprocess.run(["/usr/bin/time", "-l" if system == "Darwin" else "-v", "-o", str(time_path), *command],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        elapsed = time.perf_counter() - stage_start
        native = time_path.read_text()
        if system == "Darwin":
            rss = int(re.search(r"(\d+)\s+maximum resident set size", native)[1])
        else:
            rss = int(re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", native)[1]) * 1024
        stage = {"stage": name, "wall_seconds": elapsed, "peak_rss_bytes": rss,
                 "output_bytes": output_path.stat().st_size, "command": command}
        report["stages"].append(stage)
        print(f"{name}: {elapsed:.2f} s, {rss / 2**20:.2f} MiB peak RSS", flush=True)
    report["total_wall_seconds"] = time.perf_counter() - started
    report["pipeline_peak_rss_bytes"] = max(s["peak_rss_bytes"] for s in report["stages"])
    (args.output_dir / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"total: {report['total_wall_seconds']:.2f} s", flush=True)


if __name__ == "__main__":
    main()
