#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

ITERATIONS="${ITERATIONS:-1000000}"
TIMEOUT="${TIMEOUT:-10}"
if [[ -z "${SEED:-}" ]]; then
  SEED="$(( ( $(date +%s) << 16 ) ^ $$ ))"
fi
HEARTBEAT_EVERY="${HEARTBEAT_EVERY:-25}"
MAX_ARTIFACTS="${MAX_ARTIFACTS:-10000}"
MAX_ARTIFACT_MB="${MAX_ARTIFACT_MB:-1024}"
MAX_ARTIFACTS_PER_STATUS="${MAX_ARTIFACTS_PER_STATUS:-}"
DEDUPE_BY_SIGNAL="${DEDUPE_BY_SIGNAL:-0}"
REDUCE_ARTIFACTS="${REDUCE_ARTIFACTS:-0}"
INTERESTING_PASSES="${INTERESTING_PASSES:-1}"
MAX_INTERESTING_PASSES="${MAX_INTERESTING_PASSES:-2000}"
INTERESTING_CORPUS="${INTERESTING_CORPUS:-}"
INTERESTING_PERCENT="${INTERESTING_PERCENT:-15}"
RUNS_DIR="${RUNS_DIR:-SwiftSyntaxFuzzer/runs}"
WORKERS="${WORKERS:-$(sysctl -n hw.ncpu 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)}"
WORKERS="$(( WORKERS < 1 ? 1 : WORKERS ))"
ITERATIONS_PER_WORKER="$(( (ITERATIONS + WORKERS - 1) / WORKERS ))"
FOREGROUND="${FOREGROUND:-0}"

mkdir -p "$RUNS_DIR"
PID_FILE="$RUNS_DIR/latest.pid"
: > "$PID_FILE"

echo "Starting $WORKERS ApusApus fuzzer workers"
echo "Base seed: $SEED"
echo "Iterations: $ITERATIONS total target, $ITERATIONS_PER_WORKER per worker"

for ((worker = 0; worker < WORKERS; worker++)); do
  worker_dir="$RUNS_DIR/worker-$worker"
  mkdir -p "$worker_dir"
  log="$RUNS_DIR/latest.worker-$worker.log"
  worker_seed="$(/usr/bin/python3 - "$SEED" "$worker" <<'PY'
import sys
base = int(sys.argv[1], 0)
worker = int(sys.argv[2])
mixed = (base ^ (0x9E3779B97F4A7C15 * (worker + 1))) & ((1 << 64) - 1)
print(mixed)
PY
)"

  command=(
    SwiftSyntaxFuzzer/.build/advent-fuzz-runner
    --iterations "$ITERATIONS_PER_WORKER" \
    --timeout "$TIMEOUT" \
    --seed "$worker_seed" \
    --output "$worker_dir" \
    --heartbeat-every "$HEARTBEAT_EVERY" \
    --max-artifacts "$MAX_ARTIFACTS" \
    --max-artifact-mb "$MAX_ARTIFACT_MB" \
    --reduce-artifacts "$REDUCE_ARTIFACTS" \
    --max-interesting-passes "$MAX_INTERESTING_PASSES" \
    --quiet-passes
  )
  if [[ "$INTERESTING_PASSES" == "0" ]]; then
    command+=(--no-interesting-passes)
  fi
  if [[ -n "$MAX_ARTIFACTS_PER_STATUS" ]]; then
    command+=(--max-artifacts-per-status "$MAX_ARTIFACTS_PER_STATUS")
  fi
  if [[ "$DEDUPE_BY_SIGNAL" == "1" ]]; then
    command+=(--dedupe-by-signal)
  fi
  if [[ -n "$INTERESTING_CORPUS" ]]; then
    command+=(--interesting-corpus "$INTERESTING_CORPUS" --interesting-percent "$INTERESTING_PERCENT")
  fi

  if [[ "$FOREGROUND" == "1" ]]; then
    "${command[@]}" >"$log" 2>&1 &
    pid="$!"
  else
    nohup "${command[@]}" >"$log" 2>&1 &
    pid="$!"
  fi
  echo "$pid worker-$worker seed=$worker_seed log=$ROOT/$log" >> "$PID_FILE"
  echo "Started worker-$worker PID $pid seed=$worker_seed"
  echo "  Log: $ROOT/$log"
done

echo "PID file: $ROOT/$PID_FILE"
echo "Each worker's latest run directory will be printed at the top of its log."

if [[ "$FOREGROUND" == "1" ]]; then
  echo "Waiting for workers; interrupt this supervisor to stop the run."
  wait
fi
