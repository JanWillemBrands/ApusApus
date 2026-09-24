#!/usr/bin/env python3
"""Per-annotation necessity sweep over Swift.apus.

For EACH Oracle annotation occurrence: remove just that one, run the full suite,
record the outcome, restore the grammar. Gathers results only — never acts on them.

The grammar is read from SOURCE by the tests (`testProjectDirectory()` is
`#filePath`-derived), so no rebuild is needed between iterations.

Outputs TSV to tools/sweep_results.tsv, one line per annotation, flushed as it goes.
Logs are kept only for iterations that FAIL (tools/sweep_logs/NNN.log).
"""
import os, re, subprocess, sys, time

ROOT = "/Users/janwillem/Developer/Xcode/AoC2021"
GRAMMAR = os.path.join(ROOT, "apus grammars/Swift.apus")
ORIG = "/tmp/sweep_orig.apus"
RESULTS = os.path.join(ROOT, "tools/sweep_results.tsv")
LOGDIR = os.path.join(ROOT, "tools/sweep_logs")
TIMEOUT = 600          # a removal can cause a blowup; cap it rather than hang the sweep

# Annotations that take a parenthesised operand — the operand must go with the word.
WITH_ARGS = ("cannotParse", "canParse", "confinedTo", "excludedFrom")
ALL_KINDS = ("longest", "shortest", "prefer", "avoid", "sameLine") + WITH_ARGS
# Only the arg-taking kinds may absorb a following `(...)`; for the others a `(`
# belongs to a bracket GROUP in the rule and must not be touched.
PATTERN = re.compile(
    r"@(?:" + "|".join(WITH_ARGS) + r")\s*\([^)]*\)"
    r"|@(?:" + "|".join(k for k in ALL_KINDS if k not in WITH_ARGS) + r")\b"
)
LHS = re.compile(r"^([A-Za-z_][\w-]*)\s*[=:-]")


def occurrences(text):
    """Every LIVE annotation occurrence: (start, end, kind, line_no, enclosing_lhs, text).

    Matches inside `//` comments are skipped — the file discusses these annotations
    in prose constantly, and removing a word from a comment is a 78-second no-op.
    """
    out = []
    for m in PATTERN.finditer(text):
        line_start = text.rfind("\n", 0, m.start()) + 1
        if "//" in text[line_start:m.start()]:
            continue
        kind = m.group(0)[1:].split("(")[0].strip()
        line_no = text.count("\n", 0, m.start()) + 1
        lhs = "?"
        for ln in reversed(text[: m.start()].split("\n")):
            hit = LHS.match(ln)
            if hit:
                lhs = hit.group(1)
                break
        out.append((m.start(), m.end(), kind, line_no, lhs, m.group(0)))
    return out


def variant(text, occ):
    """`text` with occurrence `occ` deleted, plus a trailing space or blank line."""
    start, end = occ[0], occ[1]
    while end < len(text) and text[end] == " ":
        end += 1
    cut = text[:start] + text[end:]
    # A standalone annotation line leaves an empty line behind; harmless (trivia).
    return cut


def metrics(log):
    def n(pat):
        return len(re.findall(pat, log))
    run = re.search(r"Test run with (\d+) tests in (\d+) suites (\w+)", log)
    return {
        "verdict": run.group(3) if run else "NO-RUN",
        "issues": n(r"recorded an issue"),
        "ambiguity": n(r"Residual ambiguity"),
        "noparse": n(r"Advent failed to parse"),
        "treediff": n(r"Trees differ"),
        "wrongaccept": n(r"wrongly accepted invalid input|accepted invalid input"),
        "crash": n(r"Crash:"),
        "unhandled": (re.search(r"\.unhandled tally \((\d+) total\)", log) or ["", "?"])[1],
        "matching": (re.search(r"matching:\s+(\d+)", log) or ["", "?"])[1],
    }


def main():
    os.makedirs(LOGDIR, exist_ok=True)
    with open(GRAMMAR) as f:
        original = f.read()
    with open(ORIG, "w") as f:
        f.write(original)

    occs = occurrences(original)
    cols = ["idx", "kind", "line", "lhs", "verdict", "issues", "ambiguity",
            "noparse", "treediff", "wrongaccept", "crash", "unhandled",
            "matching", "secs", "annotation"]
    with open(RESULTS, "w") as out:
        out.write("\t".join(cols) + "\n")
        out.flush()
        for i, occ in enumerate(occs):
            with open(GRAMMAR, "w") as g:
                g.write(variant(original, occ))
            t0 = time.time()
            try:
                p = subprocess.run(
                    ["caffeinate", "-i", "xcodebuild", "test-without-building",
                     "-scheme", "Advent", "-destination", "platform=macOS",
                     "-parallel-testing-enabled", "NO"],
                    cwd=ROOT, capture_output=True, text=True, timeout=TIMEOUT)
                log = p.stdout + p.stderr
            except subprocess.TimeoutExpired as e:
                log = (e.stdout or "") + (e.stderr or "") if isinstance(e.stdout, str) else ""
                log += "\nSWEEP-TIMEOUT\n"
                subprocess.run(["pkill", "-9", "-f", "xctest"], capture_output=True)
            secs = round(time.time() - t0, 1)
            m = metrics(log)
            if m["verdict"] != "passed":
                with open(os.path.join(LOGDIR, f"{i:03d}.log"), "w") as lf:
                    lf.write(log)
            row = [str(i), occ[2], str(occ[3]), occ[4],
                   m["verdict"], str(m["issues"]), str(m["ambiguity"]), str(m["noparse"]),
                   str(m["treediff"]), str(m["wrongaccept"]), str(m["crash"]),
                   str(m["unhandled"]), str(m["matching"]), str(secs),
                   occ[5].replace("\t", " ")]
            out.write("\t".join(row) + "\n")
            out.flush()
            # Always restore before the next iteration.
            with open(GRAMMAR, "w") as g:
                g.write(original)
    # Final safety: grammar byte-identical to the start.
    with open(GRAMMAR) as f:
        assert f.read() == original, "grammar not restored!"
    print("SWEEP COMPLETE", len(occs), "annotations")


if __name__ == "__main__":
    main()
