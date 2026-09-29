#!/usr/bin/env python3
"""Fetch a corpus of GitHub Swift repositories to crawl with `crawl_swift_sources.py`.

Everything lands OUTSIDE the repo (default `~/Library/Caches/ApusApusCorpus`): the resolved repo
list, the shallow clones and the fetch log. Nothing here is meant to be committed.

    tools/fetch_swift_repos.py                      # top 100 Swift repos by stars + the extra set
    tools/fetch_swift_repos.py --limit 30 --update  # refresh existing clones too
    tools/fetch_swift_repos.py --list-only          # resolve and print the list, clone nothing

Repo selection uses the GitHub search API unauthenticated (~10 requests/minute, no token needed);
`--token` or `$GITHUB_TOKEN` raises that limit. Star-ranked results skew towards apps and
frameworks, so EXTRA_REPOS is always included: those exercise macros, ownership and lifetime
annotations, which is where the grammar's gaps actually are.

Clones are `--depth 1 --single-branch`: ~1.6 s and a few MB each, no history. Then crawl them:

    tools/crawl_swift_sources.py --out /tmp/crawl ~/Library/Caches/ApusApusCorpus/repos
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys
import time
import urllib.error
import urllib.request

DEFAULT_ROOT = pathlib.Path.home() / "Library/Caches/ApusApusCorpus"
SEARCH = ("https://api.github.com/search/repositories"
          "?q=language:Swift+stars:>500+archived:false&sort=stars&order=desc"
          "&per_page={per_page}&page={page}")

# Always crawled: recent language features (macros, ownership, lifetime annotations, typed throws)
# live here, not in the star-ranked app repos.
# Doc/list repos that rank high by stars but contain little or no Swift.
SKIP_WORDS = ("awesome", "tutorial", "cheatsheet", "interview", "roadmap", "resources",
              "guide", "book", "example-", "-examples", "learn")

EXTRA_REPOS = [
    "apple/swift-syntax", "apple/swift-collections", "apple/swift-algorithms",
    "apple/swift-async-algorithms", "apple/swift-argument-parser", "apple/swift-nio",
    "apple/swift-log", "apple/swift-metrics", "apple/swift-distributed-actors",
    "apple/swift-foundation", "apple/swift-testing", "apple/swift-format",
    "apple/swift-markdown", "apple/swift-docc", "apple/swift-openapi-generator",
    "swiftlang/swift-subprocess", "pointfreeco/swift-composable-architecture",
    "pointfreeco/swift-dependencies", "pointfreeco/swift-snapshot-testing",
    "groue/GRDB.swift", "vapor/vapor", "vapor/fluent-kit",
]


def api_get(url, token):
    request = urllib.request.Request(url, headers={
        "Accept": "application/vnd.github+json",
        "User-Agent": "ApusApus-corpus-fetch",
        **({"Authorization": f"Bearer {token}"} if token else {}),
    })
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


def resolve(limit, token, max_mb):
    """Top Swift repos by stars, plus EXTRA_REPOS, de-duplicated and size-filtered."""
    found, page = {}, 1
    while len(found) < limit and page <= 10:
        try:
            payload = api_get(SEARCH.format(per_page=min(100, limit), page=page), token)
        except urllib.error.HTTPError as error:
            print(f"search page {page} failed ({error.code}); keeping {len(found)} repos",
                  file=sys.stderr)
            break
        items = payload.get("items", [])
        if not items:
            break
        for item in items:
            # `size` is the checkout in KB; a huge repo is usually assets, not Swift.
            if item.get("size", 0) / 1024 > max_mb:
                continue
            # Link collections rank high under `language:Swift` but are markdown, not code
            # (`awesome-mac` and `awesome-ios` were #1 and #2 on 2026-09-28).
            if any(word in item["full_name"].lower() for word in SKIP_WORDS):
                continue
            found[item["full_name"]] = {"full_name": item["full_name"],
                                        "clone_url": item["clone_url"],
                                        "stars": item.get("stargazers_count", 0),
                                        "size_mb": round(item.get("size", 0) / 1024, 1)}
            if len(found) >= limit:
                break
        page += 1
        time.sleep(2)   # unauthenticated search is rate-limited per minute
    for name in EXTRA_REPOS:
        found.setdefault(name, {"full_name": name,
                                "clone_url": f"https://github.com/{name}.git",
                                "stars": None, "size_mb": None})
    return sorted(found.values(), key=lambda r: (r["stars"] is None, -(r["stars"] or 0)))


def clone(repo, repos_dir, update):
    target = repos_dir / repo["full_name"].replace("/", "__")
    if target.exists():
        if not update:
            return "cached"
        result = subprocess.run(["git", "-C", str(target), "fetch", "--depth", "1", "--quiet"],
                                capture_output=True, text=True)
        return "updated" if result.returncode == 0 else "update-failed"
    result = subprocess.run(["git", "clone", "--depth", "1", "--single-branch", "--quiet",
                             repo["clone_url"], str(target)],
                            capture_output=True, text=True, timeout=300)
    return "cloned" if result.returncode == 0 else "clone-failed"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=str(DEFAULT_ROOT), help=f"corpus cache (default {DEFAULT_ROOT})")
    ap.add_argument("--limit", type=int, default=100, help="how many star-ranked repos to take")
    ap.add_argument("--max-mb", type=int, default=400, help="skip repos larger than this")
    ap.add_argument("--token", default=os.environ.get("GITHUB_TOKEN"))
    ap.add_argument("--update", action="store_true", help="fetch repos that are already cloned")
    ap.add_argument("--list-only", action="store_true")
    args = ap.parse_args()

    root = pathlib.Path(os.path.expanduser(args.root))
    repos_dir = root / "repos"
    repos_dir.mkdir(parents=True, exist_ok=True)

    repos = resolve(args.limit, args.token, args.max_mb)
    (root / "repos.json").write_text(json.dumps(repos, indent=2) + "\n")
    print(f"{len(repos)} repos resolved -> {root / 'repos.json'}")
    if args.list_only:
        for repo in repos:
            print(f"  {repo['stars'] if repo['stars'] is not None else '   -':>6}  {repo['full_name']}")
        return

    counts, started = {}, time.time()
    for index, repo in enumerate(repos, 1):
        outcome = clone(repo, repos_dir, args.update)
        counts[outcome] = counts.get(outcome, 0) + 1
        if outcome.endswith("failed") or index % 10 == 0 or index == len(repos):
            print(f"[{index}/{len(repos)}] {outcome:13} {repo['full_name']}", flush=True)
    swift_files = sum(1 for _ in repos_dir.rglob("*.swift"))
    summary = (f"{len(repos)} repos, {swift_files} .swift files, "
               f"{time.time() - started:.0f} s, {counts}")
    (root / "fetch.log").write_text(summary + "\n")
    print(summary)
    print(f"crawl with: tools/crawl_swift_sources.py --out /tmp/crawl {repos_dir}")


if __name__ == "__main__":
    main()
