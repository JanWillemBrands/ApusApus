#!/usr/bin/env python3
"""Parse every .swift file under one or more directories with Advent and record the outcome.

The crawl harness for TODO.md / Make whole-file parsing crash-free and crawlable:

  * one PERSISTENT probe per worker (`advent-fuzz-probe --server`): the ~1 s grammar load is paid
    once per worker, not once per file;
  * a per-file TIMEOUT: a stuck probe is killed, the file is retried once on a fresh probe, and
    the crawl moves on; a record carrying `firstAttempt: timeout` plus a real status is harness
    flakiness, a record whose status stays `timeout` is a genuinely pathological file, and
    `probeCpuSeconds` says whether the probe was working or idle when it was killed;
  * a SIZE CAP for pathological files (`--max-bytes`), recorded as `skipped-size`;
  * every outcome — accepted, rejected, tree difference, ambiguity, crash, timeout — is a line in
    `results.jsonl`; nothing stops the crawl.

    tools/crawl_swift_sources.py --out /tmp/crawl DIR [DIR …]
    tools/crawl_swift_sources.py --workers 8 --timeout 120 --out /tmp/crawl ~/src/some-repos

Statuses are the probe's. By default the probe runs NO compiler checks (`skipCompiler`), so a
swift-syntax-accepts/Advent-rejects file reads `advent-underaccept`; pass `--compiler` to let the
probe consult `swiftc` for those (slow). Rebuild the probe after engine changes:
    ADVENT_FUZZER_SKIP_XCODEBUILD=1 bash SwiftSyntaxFuzzer/bin/build.sh
"""
import argparse
import collections
import json
import os
import pathlib
import queue
import re
import subprocess
import sys
import threading
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
PROBE = ROOT / "SwiftSyntaxFuzzer/.build/advent-fuzz-probe"
# APUS_GRAMMAR lets an A/B run point at a grammar snapshot without touching the shared file.
GRAMMAR = pathlib.Path(os.environ.get("APUS_GRAMMAR", ROOT / "grammars/Swift.apus"))
SKIP_DIRS = {".build", ".git", "DerivedData", "Pods", "Carthage", "node_modules"}


class Probe:
    """A persistent probe process that answers one JSON request per line.

    Both ends of the pipe outgrow the 64 KB pipe buffer on real sources — a 65 KB file makes a
    67 KB request, and one reply measured 1.5 MB on a single line — so request and reply are
    pumped CONCURRENTLY by two threads. Writing and then reading from the same thread deadlocks
    once the request exceeds the buffer: the write waits for the probe to drain stdin while the
    probe waits for the rest of the request. The reader is a thread rather than `select`, because
    `select` polls the file descriptor and cannot see bytes already sitting in Python's own
    8 KB read buffer; a reply parked there looks exactly like a hung probe. The 2026-09-28 crawl
    reported 11 timeouts at precisely 120.0 s each, every one of which re-runs in under 9 s.
    """

    def __init__(self):
        self.proc = None
        self.replies = None
        self.reader = None

    def start(self):
        self.proc = subprocess.Popen(
            [str(PROBE), "--grammar", str(GRAMMAR), "--server"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            text=True, bufsize=1)
        self.replies = queue.Queue()
        stream, sink = self.proc.stdout, self.replies

        def pump():
            for line in stream:           # blocks in the thread, never in the worker
                sink.put(line)
            sink.put(None)                # EOF: the probe died

        self.reader = threading.Thread(target=pump, daemon=True)
        self.reader.start()

    def stop(self):
        if self.proc and self.proc.poll() is None:
            self.proc.kill()
            self.proc.wait()
        self.proc = None
        self.replies = None
        self.reader = None

    def cpu_seconds(self):
        """CPU time the probe has burned, to tell a working probe from a stuck one."""
        if self.proc is None:
            return None
        try:
            result = subprocess.run(["ps", "-o", "cputime=", "-p", str(self.proc.pid)],
                                    capture_output=True, text=True)
        except PermissionError:
            return None
        field = result.stdout.strip()             # [[dd-]hh:]mm:ss
        if not field:
            return None
        parts = field.replace("-", ":").split(":")
        seconds = 0.0
        for part in parts:
            seconds = seconds * 60 + float(part)
        return round(seconds, 1)

    def run(self, source, timeout, compiler):
        if self.proc is None or self.proc.poll() is not None:
            self.start()
        request = json.dumps({"source": source, "includeDumps": False,
                              "skipCompiler": not compiler}) + "\n"
        broken = []

        def send():
            try:
                self.proc.stdin.write(request)
                self.proc.stdin.flush()
            except (BrokenPipeError, ValueError, OSError) as error:
                broken.append(error)

        sender = threading.Thread(target=send, daemon=True)
        sender.start()
        try:
            line = self.replies.get(timeout=timeout)
        except queue.Empty:
            cpu = self.cpu_seconds()
            self.stop()
            return {"status": "timeout", "probeCpuSeconds": cpu}
        if line is None:
            code = self.proc.poll()
            self.stop()
            return {"status": "crash", "exit": code}
        if broken:
            self.stop()
            return {"status": "crash"}
        try:
            return json.loads(line)
        except json.JSONDecodeError:
            self.stop()
            return {"status": "invalid-probe-output"}


# Words kept verbatim in a cause key; every other identifier collapses to `x`, so
# `@_lifetime(borrow e)` and `@_lifetime(borrow self)` land in one cluster.
KEYWORDS = {
    "actor", "any", "as", "associatedtype", "async", "await", "borrow", "borrowing", "break",
    "case", "catch", "class", "consume", "consuming", "continue", "default", "defer", "deinit",
    "do", "each", "else", "enum", "extension", "fallthrough", "false", "fileprivate", "for",
    "func", "get", "guard", "if", "import", "in", "indirect", "infix", "init", "inout",
    "internal", "is", "isolated", "lazy", "let", "macro", "mutating", "nil", "nonisolated",
    "nonmutating", "open", "operator", "override", "package", "postfix", "precedencegroup",
    "prefix", "private", "protocol", "public", "repeat", "rethrows", "return", "self", "Self",
    "sending", "set", "some", "static", "struct", "subscript", "super", "switch", "throw",
    "throws", "true", "try", "typealias", "unowned", "using", "var", "weak", "where", "while",
    "willSet", "didSet",
}
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def normalize(text):
    return IDENT.sub(lambda m: m.group(0) if m.group(0) in KEYWORDS else "x", text)


QUOTED = re.compile(r'"[^"]*"')


def normalize_dump_line(text):
    """A dump line keyed by SHAPE, not by the name in it.

    Lines are either a node kind (`DeclReferenceExpr`) or a token
    (`identifier("foo") "foo"`, `keyword(SwiftSyntax.Keyword.for) "for"`). Collapsing every
    identifier — what `normalize` does — turned the node kind itself into `x`, so 206 of 312 tree
    differences in the 2026-09-28 crawl collapsed into one useless `x != x` bucket. Keep the kind
    and the keyword name; blank only the QUOTED token text, which is the part that varies per file.
    """
    return QUOTED.sub('"…"', text.strip())


def cause_key(record, reply):
    """A short, stable label grouping findings that share one underlying cause.

    Rejects key on WHERE the parse stopped (the probe's failure site) plus what the grammar wanted
    there — identifiers collapsed, so only the shape remains. Tree differences key on the first
    differing dump line, ambiguities on the ambiguous nonterminal. No per-file reduction needed.
    """
    status = record["status"]
    if status in ("skipped-size", "skipped-encoding", "same"):
        return status
    if status == "residual-ambiguity":
        first = (reply.get("residualAmbiguities") or ["?"])[0]
        return "ambiguity: " + normalize(first.split("[")[0].strip())
    if status == "tree-difference":
        reference = (reply.get("referenceDump") or "").split("\n")
        advent = (reply.get("adventDump") or "").split("\n")
        for i in range(max(len(reference), len(advent))):
            a = reference[i].strip() if i < len(reference) else "<missing>"
            b = advent[i].strip() if i < len(advent) else "<missing>"
            if a != b:
                return f"tree: {normalize_dump_line(a)[:48]} != {normalize_dump_line(b)[:48]}"
        return "tree: <no normalized difference>"
    context = reply.get("failureContext")
    if context:
        before, _, after = context.partition("<HERE>")
        window = normalize(before[-14:]) + "<HERE>" + normalize(after[:14])
        expected = ",".join((reply.get("failureExpected") or [])[:3])
        return f"{status} at {window} expected {expected}"
    return status


def swift_files(dirs):
    for d in dirs:
        for root, subdirs, files in os.walk(d):
            subdirs[:] = [s for s in subdirs if s not in SKIP_DIRS]
            for f in files:
                if f.endswith(".swift"):
                    yield os.path.join(root, f)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("dirs", nargs="+")
    ap.add_argument("--out", required=True, help="output directory (results.jsonl, summary.txt)")
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 2) - 2))
    ap.add_argument("--timeout", type=float, default=300, help="seconds per file")
    ap.add_argument("--max-bytes", type=int, default=1_000_000, help="skip larger files")
    ap.add_argument("--compiler", action="store_true", help="let the probe consult swiftc")
    args = ap.parse_args()

    out = pathlib.Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    files = sorted(set(swift_files(args.dirs)))
    work = queue.Queue()
    for path in files:
        work.put(path)
    lock = threading.Lock()
    results = out / "results.jsonl"
    counts = collections.Counter()
    slowest = []
    started = time.time()
    done = [0]

    def worker():
        probe = Probe()
        with results.open("a") as sink:
            while True:
                try:
                    path = work.get_nowait()
                except queue.Empty:
                    break
                size = os.path.getsize(path)
                record = {"path": path, "bytes": size}
                if size > args.max_bytes:
                    record["status"] = "skipped-size"
                else:
                    try:
                        source = pathlib.Path(path).read_text(encoding="utf-8")
                    except UnicodeDecodeError:
                        source = None
                        record["status"] = "skipped-encoding"
                    if source is not None:
                        t = time.time()
                        reply = probe.run(source, args.timeout, args.compiler)
                        if reply.get("status") == "timeout":
                            # A timeout costs the whole limit, so it is worth one retry on a
                            # fresh probe: that separates a genuinely pathological file (times
                            # out twice) from harness flakiness (parses fine the second time).
                            record["firstAttempt"] = "timeout"
                            record["firstAttemptProbeCpuSeconds"] = reply.get("probeCpuSeconds")
                            reply = probe.run(source, args.timeout, args.compiler)
                        record["seconds"] = round(time.time() - t, 3)
                        if reply.get("probeCpuSeconds") is not None:
                            record["probeCpuSeconds"] = reply["probeCpuSeconds"]
                        record["status"] = reply.get("status", "unknown")
                        metrics = reply.get("metrics") or {}
                        record["tokens"] = metrics.get("tokenCount")
                        if reply.get("residualAmbiguities"):
                            record["ambiguity"] = reply["residualAmbiguities"][0]
                        for key in ("failureOffset", "failureLine", "failureContext", "failureExpected"):
                            if reply.get(key) not in (None, [], ""):
                                record[key] = reply[key]
                        record["cause"] = cause_key(record, reply)
                with lock:
                    sink.write(json.dumps(record) + "\n")
                    sink.flush()
                    counts[record["status"]] += 1
                    if "seconds" in record:
                        slowest.append((record["seconds"], path))
                    done[0] += 1
                    if done[0] % 50 == 0 or done[0] == len(files):
                        rate = done[0] / max(1e-9, time.time() - started)
                        print(f"[{done[0]}/{len(files)}] {rate:.1f} files/s  {dict(counts)}", flush=True)
        probe.stop()

    threads = [threading.Thread(target=worker) for _ in range(args.workers)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    elapsed = time.time() - started
    causes = collections.Counter()
    examples = {}
    with results.open() as sink:
        for line in sink:
            record = json.loads(line)
            if record["status"] == "same" or "cause" not in record:
                continue
            causes[record["cause"]] += 1
            examples.setdefault(record["cause"], record["path"])
    lines = [f"files: {len(files)}  workers: {args.workers}  wall: {elapsed:.0f} s",
             "statuses: " + ", ".join(f"{k}={v}" for k, v in counts.most_common()),
             "",
             f"causes ({len(causes)} distinct, ranked by files):"]
    for cause, n in causes.most_common(40):
        lines.append(f"  {n:5}  {cause}")
        lines.append(f"         e.g. {examples[cause]}")
    lines += ["", "slowest:"]
    lines += [f"  {s:7.1f} s  {p}" for s, p in sorted(slowest, reverse=True)[:10]]
    (out / "summary.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
