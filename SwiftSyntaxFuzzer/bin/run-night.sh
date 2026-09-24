#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

ITERATIONS="${ITERATIONS:-1000000}"
TIMEOUT="${TIMEOUT:-10}"
SEED="${SEED:-0xA0C2021}"
HEARTBEAT_EVERY="${HEARTBEAT_EVERY:-25}"
MAX_ARTIFACTS="${MAX_ARTIFACTS:-10000}"
MAX_ARTIFACT_MB="${MAX_ARTIFACT_MB:-1024}"
RUNS_DIR="${RUNS_DIR:-AdventFuzzer/runs}"

mkdir -p "$RUNS_DIR"
LOG="$RUNS_DIR/latest.log"

nohup AdventFuzzer/.build/advent-fuzz-runner \
  --iterations "$ITERATIONS" \
  --timeout "$TIMEOUT" \
  --seed "$SEED" \
  --heartbeat-every "$HEARTBEAT_EVERY" \
  --max-artifacts "$MAX_ARTIFACTS" \
  --max-artifact-mb "$MAX_ARTIFACT_MB" \
  --quiet-passes \
  >"$LOG" 2>&1 &

PID="$!"
echo "$PID" > "$RUNS_DIR/latest.pid"

echo "Started Advent fuzzer PID $PID"
echo "Log: $ROOT/$LOG"
echo "PID file: $ROOT/$RUNS_DIR/latest.pid"
echo "Latest run directory will be printed at the top of the log."
