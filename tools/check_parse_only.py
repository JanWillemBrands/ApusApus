#!/usr/bin/env python3
"""Report test fixtures that swiftc parses but no program compiles ("parse-only", agreed 2026-10-24).

Run before adding an accept fixture harvested from the fuzzer: a parse-only source must not become a
fixture that the grammar has to keep accepting. The verdict is the fuzzer probe's own
(`checkParseOnly` request, ProbeMain.swift `hasStructuralTypecheckError`), so fixtures and fuzzer
artifacts are judged alike.

  tools/check_parse_only.py ApusApusTests/SwiftSyntaxTests.swift:fuzzHarvestSnippets
  tools/check_parse_only.py --source 'if let nil = y {}'

A `FILE:ARRAY` argument reads the `SwiftSnippet(label:source:…)` entries of that array; plain `FILE`
reads every entry. Entries that already carry `disabledReason:` or `compilerRejects:` are skipped.
Exit status 1 when any parse-only source is found.
"""
import argparse, json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / 'SwiftSyntaxFuzzer/.build/advent-fuzz-probe'
GRAMMAR = ROOT / 'grammars/Swift.apus'
ENTRY = re.compile(r'SwiftSnippet\(\s*label:\s*"([^"]*)",\s*source:\s*(#*)"((?:[^"\\]|\\.)*)"\2(.*?)\)\s*,?\s*$',
                   re.M | re.S)


def unescape(text):
    text = re.sub(r'\\u\{([0-9a-fA-F]+)\}', lambda m: chr(int(m.group(1), 16)), text)
    return re.sub(r'\\(.)', lambda m: {'n': '\n', 't': '\t', 'r': '\r', '0': '\0'}.get(m.group(1), m.group(1)), text)


def fixtures(spec):
    path, _, array = spec.partition(':')
    text = (ROOT / path).read_text()
    if array:
        start = text.index('let %s: [SwiftSnippet] = [' % array)
        text = text[start:text.index('\n]\n', start)]
    for line in text.splitlines():
        m = ENTRY.search(line)
        if not m or 'disabledReason:' in m.group(4) or 'compilerRejects:' in m.group(4):
            continue
        yield m.group(1), m.group(3) if m.group(2) else unescape(m.group(3))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('specs', nargs='*', help='FILE or FILE:ARRAY with SwiftSnippet entries')
    parser.add_argument('--source', action='append', default=[], help='a source to check directly')
    args = parser.parse_args()
    items = [(s, s) for s in args.source] + [item for spec in args.specs for item in fixtures(spec)]
    probe = subprocess.Popen([str(PROBE), '--grammar', str(GRAMMAR), '--server'], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, bufsize=1)
    found = 0
    for label, source in items:
        probe.stdin.write(json.dumps({'source': source, 'checkParseOnly': True}) + '\n')
        probe.stdin.flush()
        out = json.loads(probe.stdout.readline())
        if out.get('parseOnly'):
            found += 1
            errors = [l.split('error: ', 1)[1] for l in (out.get('compilerTypecheckStderr') or '').splitlines()
                      if 'error: ' in l]
            print('%s\t%s\t%s' % (label, json.dumps(source), ' | '.join(dict.fromkeys(errors))))
    probe.kill()
    print('%d of %d parse-only' % (found, len(items)), file=sys.stderr)
    return 1 if found else 0


if __name__ == '__main__':
    sys.exit(main())
