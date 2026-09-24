#!/usr/bin/env python3
"""Extract valid assertParse() snippets from SwiftSyntax test files.

Usage: python3 extract_snippets.py <input.swift> [syntax_version]

Outputs Swift snippet array entries for all assertParse() calls
that do NOT have a `diagnostics:` parameter.
"""

import re
import sys
import os

def find_matching_paren(text, start):
    """Find the matching closing paren for an opening paren at `start`."""
    depth = 0
    i = start
    in_string = False
    string_delim = None
    raw_pounds = 0
    in_multiline = False
    escape_next = False

    while i < len(text):
        ch = text[i]

        if escape_next:
            escape_next = False
            i += 1
            continue

        if in_string:
            if in_multiline:
                if ch == '"' and i + 2 < len(text) and text[i:i+3] == '"""':
                    if raw_pounds > 0:
                        after = text[i+3:i+3+raw_pounds]
                        if after == '#' * raw_pounds:
                            in_string = False
                            in_multiline = False
                            i += 3 + raw_pounds
                            continue
                    else:
                        in_string = False
                        in_multiline = False
                        i += 3
                        continue
                elif ch == '\\':
                    if raw_pounds > 0:
                        after = text[i+1:i+1+raw_pounds]
                        if after == '#' * raw_pounds:
                            escape_next = False
                            i += 1 + raw_pounds + 1
                            continue
                    else:
                        escape_next = True
            else:
                if ch == '"':
                    if raw_pounds > 0:
                        after = text[i+1:i+1+raw_pounds]
                        if after == '#' * raw_pounds:
                            in_string = False
                            i += 1 + raw_pounds
                            continue
                    else:
                        in_string = False
                        i += 1
                        continue
                elif ch == '\\':
                    if raw_pounds > 0:
                        after = text[i+1:i+1+raw_pounds]
                        if after == '#' * raw_pounds:
                            i += 1 + raw_pounds + 1
                            continue
                    else:
                        escape_next = True
        else:
            # Check for raw string start: #"  or ##" or #""" etc.
            if ch == '#':
                pounds = 0
                j = i
                while j < len(text) and text[j] == '#':
                    pounds += 1
                    j += 1
                if j < len(text) and text[j] == '"':
                    if j + 2 < len(text) and text[j:j+3] == '"""':
                        in_string = True
                        in_multiline = True
                        raw_pounds = pounds
                        i = j + 3
                        continue
                    else:
                        in_string = True
                        in_multiline = False
                        raw_pounds = pounds
                        i = j + 1
                        continue
            elif ch == '"':
                if i + 2 < len(text) and text[i:i+3] == '"""':
                    in_string = True
                    in_multiline = True
                    raw_pounds = 0
                    i += 3
                    continue
                else:
                    in_string = True
                    in_multiline = False
                    raw_pounds = 0
                    i += 1
                    continue
            elif ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0:
                    return i
            elif ch == '/' and i + 1 < len(text) and text[i+1] == '/':
                # line comment - skip to end of line
                while i < len(text) and text[i] != '\n':
                    i += 1
                continue

        i += 1

    return -1


def extract_first_string_arg(text):
    """Extract the first string literal argument from an assertParse call body.

    text starts right after 'assertParse(' and may contain:
      "simple string"
      #"raw string"#
      ##"double raw"##
      \"\"\"multiline\"\"\"
      #\"\"\"raw multiline\"\"\"#

    Returns (string_literal_as_written, rest_of_args) or None.
    """
    stripped = text.lstrip()

    # Detect what kind of string literal
    raw_pounds = 0
    pos = 0

    if stripped[pos] == '#':
        while pos < len(stripped) and stripped[pos] == '#':
            raw_pounds += 1
            pos += 1

    if pos >= len(stripped) or stripped[pos] != '"':
        return None

    start = 0  # start of the full literal including #s

    # Check for multiline
    if stripped[pos:pos+3] == '"""':
        # multiline string
        end_marker = '"""' + '#' * raw_pounds
        search_start = pos + 3
        while True:
            end_idx = stripped.find(end_marker, search_start)
            if end_idx == -1:
                return None
            # Make sure it's not escaped
            # Count backslashes before
            bs = 0
            ci = end_idx - 1
            while ci >= 0 and stripped[ci] == '\\':
                bs += 1
                ci -= 1
            if raw_pounds > 0 or bs % 2 == 0:
                literal_end = end_idx + len(end_marker)
                literal = stripped[start:literal_end]
                rest = stripped[literal_end:]
                return (literal, rest)
            search_start = end_idx + 1
    else:
        # single-line string
        end_marker = '"' + '#' * raw_pounds
        search_start = pos + 1
        while True:
            end_idx = stripped.find(end_marker, search_start)
            if end_idx == -1:
                return None
            # For non-raw strings, check escape
            if raw_pounds == 0:
                bs = 0
                ci = end_idx - 1
                while ci >= 0 and stripped[ci] == '\\':
                    bs += 1
                    ci -= 1
                if bs % 2 == 1:
                    search_start = end_idx + 1
                    continue
            literal_end = end_idx + len(end_marker)
            literal = stripped[start:literal_end]
            rest = stripped[literal_end:]
            return (literal, rest)


def has_diagnostics(rest_of_args):
    """Check if the remaining arguments contain a NON-EMPTY diagnostics: parameter.

    `diagnostics: []` asserts the opposite of what the bare substring suggests: it means
    "this source parses with NO errors". Both extractors key off this helper and so both
    misfiled such a call — `extract_snippets.py` skipped it from the ACCEPT corpus while
    `extract_rejects.py` asserted it as a REJECT, i.e. exactly backwards.

    It bit `TypeTests.testLifetimeSpecifier`: `assertParse("func foo() -> dependsOn(0) X",
    diagnostics: [], experimentalFeatures: [.nonescapableTypes])` is a VALID case, but landed
    in the reject corpus as `testLifetimeSpecifier#6`, where it could never pass — Advent is
    right to accept it. Only one call in each raw corpus is affected, so this is a guard
    against recurrence on the next version bump rather than a bulk re-harvest.
    """
    match = re.search(r'diagnostics\s*:\s*\[', rest_of_args)
    if not match:
        return False
    # Empty list (whitespace/newlines only before the closing bracket) = asserts NO errors.
    tail = rest_of_args[match.end():]
    return tail.lstrip()[:1] != ']'


def has_underscored_attrs(source_literal):
    """Check if the source string uses underscored/internal attributes."""
    # Match @_ followed by a word char (internal attributes like @_spi, @_exported, etc.)
    return bool(re.search(r'@_\w', source_literal))


MARKER_PATTERN = re.compile(
    '[\U0000FE00-\U0000FE0F\U00010000-\U0010FFFF]'  # variation selectors + supplementary
    '|[⃣ℹ️]'  # combining enclosing keycap, info, variation
)

def has_marker_chars(s):
    """Check for SwiftSyntax diagnostic markers like 1️⃣, ℹ️ etc."""
    # These are emoji sequences used as location markers
    return bool(re.search(r'[0-9]️⃣|ℹ️', s))


def strip_markers(s):
    """Strip SwiftSyntax diagnostic markers from a string."""
    # Remove digit + VS16 + combining enclosing keycap sequences
    s = re.sub(r'[0-9]️⃣', '', s)
    # Remove ℹ️ (info + VS16)
    s = re.sub(r'ℹ️', '', s)
    return s


def extract_string_content(literal):
    """Given a Swift string literal (including quotes/pounds), return the actual string content."""
    # Determine raw pounds
    raw_pounds = 0
    pos = 0
    while pos < len(literal) and literal[pos] == '#':
        raw_pounds += 1
        pos += 1

    if literal[pos:pos+3] == '"""':
        # Multiline: strip opening """ (+ newline) and closing """
        open_end = pos + 3
        close_start = literal.rfind('"""')
        content = literal[open_end:close_start]
        # Strip leading newline
        if content.startswith('\n'):
            content = content[1:]
        # Strip trailing whitespace before closing """
        lines = content.split('\n')
        if lines:
            # The indentation of the closing """ determines the trim
            last_before_close = literal[:close_start].split('\n')[-1]
            indent = len(last_before_close) - len(last_before_close.lstrip())
            lines = [l[indent:] if len(l) >= indent else l for l in lines]
            # Remove trailing empty line
            if lines and lines[-1].strip() == '':
                lines = lines[:-1]
            content = '\n'.join(lines)
        return content
    else:
        # Single-line: strip opening " and closing "
        content = literal[pos+1:-(1+raw_pounds)]
        return content


def find_test_func(text, position):
    """Find the enclosing test function name for a given position."""
    before = text[:position]
    matches = list(re.finditer(r'func\s+(test\w+)\s*\(', before))
    if matches:
        return matches[-1].group(1)
    return "unknown"


def process_file(filepath, syntax_version="603.0.1"):
    """Process a Swift test file and extract valid snippets."""
    with open(filepath, 'r', encoding='utf-8') as f:
        source = f.read()

    basename = os.path.splitext(os.path.basename(filepath))[0]

    snippets = []
    func_counters = {}

    pos = 0
    while True:
        idx = source.find('assertParse(', pos)
        if idx == -1:
            break

        paren_start = idx + len('assertParse')
        paren_end = find_matching_paren(source, paren_start)
        if paren_end == -1:
            pos = idx + 1
            continue

        call_body = source[paren_start+1:paren_end]

        func_name = find_test_func(source, idx)

        result = extract_first_string_arg(call_body)
        if result is None:
            pos = paren_end + 1
            continue

        literal, rest = result
        has_diag = has_diagnostics(rest)
        has_markers = has_marker_chars(literal)

        if not has_diag:
            if func_name not in func_counters:
                func_counters[func_name] = 0
            func_counters[func_name] += 1
            counter = func_counters[func_name]

            underscored = has_underscored_attrs(literal)

            # Clean markers if present (rare in non-diagnostic calls)
            if has_markers:
                literal_clean = strip_markers(literal)
            else:
                literal_clean = literal

            snippets.append({
                'label': f"{func_name}#{counter}",
                'literal': literal_clean,
                'origin': f"{basename}.{func_name}",
                'syntax_version': syntax_version,
                'underscored': underscored,
            })

        pos = paren_end + 1

    return snippets


def format_snippets_swift(snippets, array_name):
    """Format snippets as a Swift array declaration."""
    lines = [f"let {array_name}: [SwiftSnippet] = ["]

    for s in snippets:
        literal = s['literal']
        disabled = s['underscored']
        disabled_field = ', disabledReason: "underscore attribute"' if disabled else ''

        if '\n' in literal:
            lines.append(f"    SwiftSnippet(")
            lines.append(f"        label: \"{s['label']}\",")
            lines.append(f"        source: {literal},")
            lines.append(f"        origin: \"{s['origin']}\",")
            if disabled:
                lines.append(f"        syntaxVersion: \"{s['syntax_version']}\",")
                lines.append(f"        disabledReason: \"underscore attribute\"")
            else:
                lines.append(f"        syntaxVersion: \"{s['syntax_version']}\"")
            lines.append(f"    ),")
        else:
            lines.append(f"    SwiftSnippet(label: \"{s['label']}\", source: {literal}, origin: \"{s['origin']}\", syntaxVersion: \"{s['syntax_version']}\"{disabled_field}),")

    lines.append("]")
    return '\n'.join(lines)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <input.swift> [syntax_version]", file=sys.stderr)
        sys.exit(1)

    filepath = sys.argv[1]
    version = sys.argv[2] if len(sys.argv) > 2 else "603.0.1"

    snippets = process_file(filepath, version)

    basename = os.path.splitext(os.path.basename(filepath))[0]
    # DeclarationTests -> declarationSnippets
    array_name = basename[0].lower() + basename[1:]
    if array_name.endswith('Tests'):
        array_name = array_name[:-5] + 'Snippets'

    # Stats
    total_valid = len(snippets)
    underscored = sum(1 for s in snippets if s['underscored'])
    print(f"// Extracted {total_valid} valid snippets ({underscored} with underscore attrs)", file=sys.stderr)

    print(format_snippets_swift(snippets, array_name))
