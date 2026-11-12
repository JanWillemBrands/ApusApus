#!/usr/bin/env python3
"""Find corpus rows that need a project-context compiler verification.

The isolated swiftc invocation below deliberately has no package or Xcode build settings.  Its
acceptances are useful, but its rejections are only leads: feature flags, availability-macro
definitions, and other project settings can make the original source valid.
"""

import argparse
import concurrent.futures
import json
import pathlib
import subprocess
import tempfile


def check(record: dict) -> dict:
    with tempfile.NamedTemporaryFile(suffix=".swift", mode="w", encoding="utf-8") as source:
        source.write(record["source"])
        source.flush()
        result = subprocess.run(
            ["xcrun", "swiftc", "-swift-version", "6", "-parse", source.name],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            text=True,
            timeout=20,
        )
    record["swiftcAccepted"] = result.returncode == 0
    record["swiftcDiagnostic"] = result.stderr.strip().splitlines()[0] if result.stderr.strip() else None
    is_reject_corpus = "reject" in record["collection"]
    record["isolatedSwiftcRejection"] = (
        not is_reject_corpus
        and record.get("disabledReason") is None
        and record.get("compilerRejects") is None
        and not record["swiftcAccepted"]
    )
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("corpus", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    parser.add_argument("--workers", type=int, default=8)
    args = parser.parse_args()
    # JSON may legally contain literal U+2028/U+2029 characters. str.splitlines() treats those
    # as record separators even though the exporter uses only ASCII LF between JSON objects.
    records = [json.loads(line) for line in args.corpus.read_text().split("\n") if line]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        audited = list(pool.map(check, records))
    with args.output.open("w", encoding="utf-8") as output:
        for record in audited:
            if record["isolatedSwiftcRejection"]:
                output.write(json.dumps(record, ensure_ascii=False) + "\n")
    isolated_rejections = sum(r["isolatedSwiftcRejection"] for r in audited)
    classified_rejections = sum(not r["swiftcAccepted"] and r.get("disabledReason") is not None for r in audited)
    print(f"audited: {len(audited)}")
    print(f"classified/disabled swiftc rejections: {classified_rejections}")
    print(f"isolated swiftc rejections requiring project-context verification: {isolated_rejections}")


if __name__ == "__main__":
    main()
