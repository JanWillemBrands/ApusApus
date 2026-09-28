#!/usr/bin/env python3
"""Cluster residual-ambiguity fuzz artifacts by ambiguous grammar signature.

Usage:
    tools/cluster_ambiguities.py SwiftSyntaxFuzzer/runs/worker-*/RUN/artifacts/*.json

Artifacts produced by newer probes store residual ambiguity diagnostics as:
    node<TAB>message<TAB>signature

Older artifacts only have the human-readable diagnostic string; those are still grouped, but less
precisely.
"""
import argparse
import collections
import json
import pathlib
import re


SPAN_RE = re.compile(r"\s*\[\d+(?:\[[^\]]+\])?\.\.\d+(?:\[[^\]]+\])?\]")
CANDIDATE_RE = re.compile(r"\s*\(\d+ candidates\)")


def iter_artifacts(paths):
    for raw in paths:
        path = pathlib.Path(raw)
        if path.is_dir():
            yield from iter_artifacts(str(p) for p in path.rglob("*.json"))
            continue
        try:
            artifact = json.loads(path.read_text())
        except Exception as error:
            print(f"warning: skipped {path}: {error}")
            continue
        probe = artifact.get("probe") or {}
        if probe.get("status") != "residual-ambiguity":
            continue
        yield path, artifact, probe


def parse_diagnostic(raw):
    parts = raw.split("\t", 2)
    if len(parts) == 3:
        node, message, signature = parts
        return node or "-", message or "-", signature or "-"

    # Backward-compatible parser for older strings like:
    # statements [83[utf8]..139[utf8]]: ambiguous alternate (2 candidates)
    normalized = SPAN_RE.sub("", raw)
    normalized = CANDIDATE_RE.sub("", normalized)
    node = normalized.split(" ", 1)[0].rstrip(":") if normalized else "-"
    message = "ambiguous alternate" if "ambiguous alternate" in raw else (
        "ambiguous pivot" if "ambiguous pivot" in raw else "residual ambiguity"
    )
    return node, message, normalized


def source_preview(source):
    lines = [line.rstrip() for line in source.strip().splitlines()]
    if len(lines) <= 5:
        return " / ".join(lines)
    return " / ".join(lines[:2] + ["..."] + lines[-2:])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+")
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--show-sources", type=int, default=1)
    args = parser.parse_args()

    clusters = collections.defaultdict(list)
    for path, artifact, probe in iter_artifacts(args.inputs):
        diagnostics = probe.get("residualAmbiguities") or ["<missing diagnostic>"]
        seen_in_artifact = set()
        for diagnostic in diagnostics:
            key = parse_diagnostic(diagnostic)
            if key in seen_in_artifact:
                continue
            seen_in_artifact.add(key)
            clusters[key].append((path, artifact, diagnostic))

    rows = sorted(clusters.items(), key=lambda item: (-len(item[1]), item[0]))
    print(f"clusters: {len(rows)}")
    print(f"artifacts: {sum(len(v) for _, v in rows)}")
    for index, ((node, message, signature), entries) in enumerate(rows[: args.top], start=1):
        print()
        print(f"{index}. count={len(entries)} node={node} kind={message}")
        print(f"   signature={signature}")
        for path, artifact, diagnostic in entries[: args.show_sources]:
            source = artifact.get("source", "")
            original = artifact.get("originalSource")
            reduced = " reduced" if original is not None else ""
            print(f"   example={path}{reduced}")
            print(f"   preview={source_preview(source)}")


if __name__ == "__main__":
    main()
