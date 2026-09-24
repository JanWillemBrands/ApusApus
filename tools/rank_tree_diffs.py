#!/usr/bin/env python3
"""Rank `trees differ` labels by their FIRST divergent dump line.

Turns the opaque "N labels still differ" number into a work queue: identical first
divergences almost always share one root cause, so the top bucket is the next fix.

    tools/rank_tree_diffs.py /tmp/run.log [--top N] [--bucket "expected X   got Y"]

`--bucket` lists every label in one bucket instead of the ranking.
"""
import collections, re, sys

def blocks(path):
    txt = open(path, encoding='utf-8', errors='replace').read()
    for b in re.split(r"Trees differ for '", txt)[1:]:
        label = b.split("'")[0]
        try:
            ref = b.split('refDump → "')[1].split('\U0001F0135   adventDump → "')[0]
        except (IndexError, ValueError):
            # the marker glyph differs between runs; fall back to a loose split
            if 'refDump → "' not in b or 'adventDump → "' not in b:
                continue
            ref = b.split('refDump → "')[1].split('adventDump → "')[0]
        adv = b.split('adventDump → "')[-1].split('\n​')[0]
        yield label, [l.strip() for l in ref.split('\n')], [l.strip() for l in adv.split('\n')]

def first_divergence(ref, adv):
    for i in range(max(len(ref), len(adv))):
        r = ref[i] if i < len(ref) else '<end>'
        a = adv[i] if i < len(adv) else '<end>'
        if r != a:
            return f"expected {r}   got {a}"
    return None

def main():
    path = sys.argv[1]
    top = int(sys.argv[sys.argv.index('--top') + 1]) if '--top' in sys.argv else 20
    want = sys.argv[sys.argv.index('--bucket') + 1] if '--bucket' in sys.argv else None
    buckets = collections.defaultdict(list)
    for label, ref, adv in blocks(path):
        cause = first_divergence(ref, adv)
        if cause:
            buckets[cause].append(label)
    if want:
        for label in sorted(buckets.get(want, [])):
            print(label)
        return
    total = sum(len(v) for v in buckets.values())
    for cause, labels in sorted(buckets.items(), key=lambda kv: -len(kv[1]))[:top]:
        print(f"{len(labels):4}  {cause}   e.g. {labels[0]}")
    print(f"--- {total} labels in {len(buckets)} buckets")

main()
