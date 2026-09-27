#!/usr/bin/env python3
"""Replay saved fuzz sources through the current probe and report old → new status.

Inputs are artifact JSON files (`runs/<run>/artifacts/*.json`) and/or `telemetry.jsonl` files
(one `{"status", "generator", "source", ...}` object per line). Use it after grammar changes to see
which saved cases now pass, which still fail, and which changed category.

    tools/replay_fuzz_sources.py SwiftSyntaxFuzzer/runs/<run>/artifacts/*.json
    tools/replay_fuzz_sources.py --only-changed SwiftSyntaxFuzzer/runs/<run>/telemetry.jsonl

Rebuild the probe first when the engine changed:
    ADVENT_FUZZER_SKIP_XCODEBUILD=1 bash SwiftSyntaxFuzzer/bin/build.sh
"""
import argparse
import collections
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
PROBE = ROOT / "SwiftSyntaxFuzzer/.build/advent-fuzz-probe"
GRAMMAR = ROOT / "grammars/Swift.apus"


def load_cases(paths):
    for path in paths:
        p = pathlib.Path(path)
        if p.suffix == ".jsonl":
            for line in p.read_text().splitlines():
                if line.strip():
                    e = json.loads(line)
                    yield p.name, e.get("status", "?"), e.get("generator"), e["source"]
        else:
            d = json.loads(p.read_text())
            yield p.name, d["probe"]["status"], d["event"].get("generator"), d["source"]


def probe(source):
    run = subprocess.run([str(PROBE), "--grammar", str(GRAMMAR)], input=source,
                         capture_output=True, text=True, timeout=600)
    lines = [l for l in run.stdout.splitlines() if l.startswith("{")]
    return json.loads(lines[-1])["status"] if lines else f"probe-error(exit {run.returncode})"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("inputs", nargs="+")
    ap.add_argument("--only-changed", action="store_true", help="list only cases whose status changed")
    args = ap.parse_args()

    transitions = collections.Counter()
    for name, old, generator, source in load_cases(args.inputs):
        new = probe(source)
        transitions[(old, new)] += 1
        if args.only_changed and old == new:
            continue
        tail = " ⏎ ".join(source.rstrip().split("\n")[-3:])
        print(f"{new:<48} {generator or '-'}\n    {name}\n    …{tail[-140:]}")
    print("\nold → new:")
    for (old, new), n in transitions.most_common():
        print(f"  {n:4}  {old} → {new}")


if __name__ == "__main__":
    main()
