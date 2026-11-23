#!/usr/bin/env python3
"""Mark file-local helper theorems `private`.

A top-level `theorem` or `lemma` in FILE is changed to `private theorem` when

- it has no attribute (no `@[...]` before it and no `attribute [...]` line naming it),
- it is not already `private` or `protected`,
- the last component of its name occurs again in FILE, and
- that component, as a whole word, occurs in no other `.lean` file under `src/`.

The last condition is deliberately coarse: it also rules out uses through dot notation,
`open`, and quoted names in metaprograms. A theorem that is never used is left alone, since
it is dead code rather than a helper.

`private` moves the statement out of the module's public `.olean`, so importers load less,
and a later change to the theorem no longer changes the module's public interface.

A helper used in the exposed body of a public definition (under `@[expose]`) must stay
public: Lean then reports `Unknown identifier` or `Invalid field` at the use. Build the
changed modules with `lake build`, save the log, and run with --revert-from-log LOG to put
those helpers back; repeat until the build is clean.

usage: scripts/privatize-local-theorems.py [--dry-run] FILE...
       scripts/privatize-local-theorems.py --revert-from-log LOG
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
DECL = re.compile(r"^(?P<mods>(?:(?:noncomputable|nonrec)\s+)*)(?P<kw>theorem|lemma)\s+"
                  r"(?P<name>[^\s:({\[]+)")
STEM = re.compile(r"[A-Za-z0-9_Ͱ-Ͽᴀ-ᶿ₀-ₜ]+")


def candidates(path: Path) -> list[dict]:
    lines = path.read_text().split("\n")
    attributed = set()
    for line in lines:
        if line.startswith("attribute"):
            attributed.update(re.findall(r"[^\s\[\]]+", line.split("]", 1)[-1]))
    found = []
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m:
            continue
        j = i - 1
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j >= 0 and lines[j].lstrip().startswith("@["):
            continue
        name = m["name"]
        last = name.split(".")[-1]
        stem = STEM.match(last)
        if not stem or name in attributed or last in attributed:
            continue
        found.append({"file": path, "line": i, "name": name, "stem": stem.group(0)})
    return found


ERROR = re.compile(r"error: (?P<file>[^:\s]+\.lean):\d+:\d+: (?:Unknown identifier|Unknown constant|"
                   r"Invalid field) `(?P<name>[^`]+)`")


def revert(log: Path) -> int:
    """Remove `private` from helpers that a build log reports as unreachable."""
    wanted = collections.defaultdict(set)
    for m in ERROR.finditer(log.read_text()):
        wanted[ROOT / m["file"]].add(m["name"].split(".")[-1])
    count = 0
    for path, names in sorted(wanted.items()):
        lines = path.read_text().split("\n")
        for i, line in enumerate(lines):
            if not line.startswith("private "):
                continue
            m = DECL.match(line[len("private "):])
            if m and m["name"].split(".")[-1] in names:
                lines[i] = line[len("private "):]
                count += 1
                print(json.dumps({"file": str(path.relative_to(ROOT)), "public": m["name"]}, ensure_ascii=False))
        path.write_text("\n".join(lines))
    print(f"{count} theorems made public again", file=sys.stderr)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--revert-from-log", type=Path, metavar="LOG")
    opts = parser.parse_args()
    if opts.revert_from_log:
        return revert(opts.revert_from_log)
    files = [p.resolve() for p in opts.files]
    found = [c for p in files for c in candidates(p)]
    stems = sorted({c["stem"] for c in found})
    if not stems:
        return 0
    with tempfile.NamedTemporaryFile("w", suffix=".txt") as patterns:
        patterns.write("\n".join(stems) + "\n")
        patterns.flush()
        out = subprocess.run(["rg", "-w", "-o", "-F", "--no-line-number", "--with-filename",
                              "-f", patterns.name, str(SRC)], capture_output=True, text=True).stdout
    where = collections.defaultdict(collections.Counter)
    for line in out.splitlines():
        file, _, token = line.rpartition(":")
        where[token][file] += 1
    chosen = collections.defaultdict(list)
    for c in found:
        uses = where[c["stem"]]
        if set(uses) == {str(c["file"])} and uses[str(c["file"])] >= 2:
            chosen[c["file"]].append(c)
    for path, items in sorted(chosen.items()):
        print(json.dumps({"file": str(path.relative_to(ROOT)), "private": [c["name"] for c in items]},
                         ensure_ascii=False))
        if opts.dry_run:
            continue
        lines = path.read_text().split("\n")
        for c in items:
            lines[c["line"]] = "private " + lines[c["line"]]
        path.write_text("\n".join(lines))
    print(f"{sum(map(len, chosen.values()))} theorems in {len(chosen)} files", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
