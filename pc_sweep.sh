#!/usr/bin/env bash
# Usage: ./pc_sweep.sh process_calculus_s1000_n200
# Prints: name,wall_us,cycles,perf_instructions,task_clock_ms,transitions,unifications,panic
set -u
BIN="${MORK_BIN:-./target/release/mork}"
name="$1"

perf_err=$(mktemp) app_out=$(mktemp)
trap 'rm -f "$perf_err" "$app_out"' EXIT

perf stat -e task-clock,cycles,instructions "$BIN" bench "$name" 2>"$perf_err" 1>"$app_out"
perfout=$(cat "$perf_err")
appout=$(cat "$app_out")

# bench self-report
wall_us=$(echo "$appout" | grep -oE 'in [0-9]+ µs' | grep -oE '[0-9]+' | head -1)
transitions=$(echo "$appout" | grep -oE 'instructions [0-9]+' | grep -oE '[0-9]+' | head -1)
unifications=$(echo "$appout" | grep -oE 'unifications [0-9]+' | grep -oE '[0-9]+' | head -1)
panic=$(echo "$appout" | grep -c 'panicked')

# perf counters (strip commas)
cycles=$(echo "$perfout" | grep -E '[0-9].*cycles' | grep -oE '[0-9,]+' | head -1 | tr -d ',')
pinstr=$(echo "$perfout" | grep -E '[0-9].*instructions' | grep -oE '[0-9,]+' | head -1 | tr -d ',')
taskclk=$(echo "$perfout" | grep -E 'task-clock' | grep -oE '[0-9]+\.[0-9]+' | head -1)

echo "${name},${wall_us:-NA},${cycles:-NA},${pinstr:-NA},${taskclk:-NA},${transitions:-NA},${unifications:-NA},${panic}"
