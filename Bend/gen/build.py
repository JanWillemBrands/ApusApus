#!/usr/bin/env python3
"""Rebuild a generated proof file of Bend/ from its generator folder.

    python3 Bend/gen/build.py PROOF_LL1AT            # writes Bend/PROOF_LL1AT.bend
    python3 Bend/gen/build.py PROOF_LL1AT --check    # only compares with Bend/PROOF_LL1AT.bend
    python3 Bend/gen/build.py --check-all            # compares every folder

Each folder holds the generator scripts and the hand-written parts of one proof, and a
`parts.txt` with one entry per line, in order:
    run  <script.py>    run the script in the folder (it writes its own .bend part)
    part <file.bend>    append this part to the proof
Lines starting with # are comments. Scripts read and write paths relative to their folder.
"""
import os, subprocess, sys, difflib

HERE = os.path.dirname(os.path.abspath(__file__))
BEND = os.path.dirname(HERE)

def build(name):
    folder = os.path.join(HERE, name)
    parts = []
    for line in open(os.path.join(folder, 'parts.txt')):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        kind, arg = line.split(None, 1)
        if kind == 'run':
            subprocess.run([sys.executable, arg], cwd=folder, check=True)
        elif kind == 'part':
            parts.append(arg)
        else:
            sys.exit('%s/parts.txt: unknown entry %r' % (name, line))
    return ''.join(open(os.path.join(folder, p)).read() for p in parts)

def check(name):
    text = build(name)
    target = os.path.join(BEND, name + '.bend')
    installed = open(target).read()
    if text == installed:
        print('%s: same as Bend/%s.bend' % (name, name))
        return True
    print('%s: DIFFERS from Bend/%s.bend' % (name, name))
    sys.stdout.writelines(list(difflib.unified_diff(installed.splitlines(True), text.splitlines(True), 'installed', 'rebuilt'))[:40])
    return False

def main(args):
    if args == ['--check-all']:
        names = sorted(d for d in os.listdir(HERE) if os.path.isfile(os.path.join(HERE, d, 'parts.txt')))
        sys.exit(0 if all([check(n) for n in names]) else 1)
    if len(args) == 2 and args[1] == '--check':
        sys.exit(0 if check(args[0]) else 1)
    if len(args) == 1:
        text = build(args[0])
        open(os.path.join(BEND, args[0] + '.bend'), 'w').write(text)
        print('wrote Bend/%s.bend' % args[0])
        return
    sys.exit(__doc__)

main(sys.argv[1:])
