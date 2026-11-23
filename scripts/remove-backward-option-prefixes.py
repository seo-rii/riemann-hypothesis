#!/usr/bin/env python3
"""Remove `set_option <OPTION> false in` prefixes that a file no longer needs.

For each FILE, the script finds every line of the form

    set_option <OPTION> false in <tactic>        (also after a `· ` bullet)
    set_option <OPTION> false in                 (on its own line, before a declaration)

drops the prefix (or the whole line), and elaborates the file with the options that
`lakefile.toml` passes to Lean. If Lean reports an error, the script puts back the prefixes
whose scope contains an error and tries again: an inline prefix owns its tactic block (from
the line that opens the block to the end of the block), and a declaration prefix owns the
declaration. A file is left changed only if its final version elaborates with no error.

Every module FILE imports must already be built or restored from the cache. Files are edited
in place, so run it on a clean checkout and review the diff.

usage: scripts/remove-backward-option-prefixes.py [--option NAME] [--jobs N] [--log LOG] FILE...
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DIAG = re.compile(r"^(?P<file>.*?):(?P<line>\d+):\d+: (?P<kind>error|warning)(\([^)]*\))?: (?P<msg>.*)$", re.M)
TOP = re.compile(r"^(@\[|/--|theorem|lemma|def|abbrev|instance|example|structure|class|inductive|noncomputable|"
                 r"private|protected|public|nonrec|irreducible_def|set_option|attribute|open|namespace|section|"
                 r"end|variable|omit|include|#|--|macro|syntax|elab)")


def lean_args(path: Path) -> list[str]:
    """The options Lake passes to Lean for this file (package and library leanOptions)."""
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    options = dict(config.get("leanOptions", {}))
    module = ".".join(path.relative_to(ROOT / "src").with_suffix("").parts)
    for lib in config.get("lean_lib", []):
        if any(re.fullmatch(g.replace(".", r"\.").replace(r"\.+", r"\..+"), module) for g in lib.get("globs", [])):
            options.update(lib.get("leanOptions", {}))

    def flat(prefix, value):
        if isinstance(value, dict):
            for k, v in value.items():
                yield from flat(f"{prefix}.{k}", v)
        else:
            yield prefix, value

    args = list(config.get("moreLeanArgs", []))
    for key, value in options.items():
        for name, v in flat(key, value):
            args.append(f"-D{name}={str(v).lower() if isinstance(v, bool) else v}")
    return args


def indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def occurrences(lines: list[str], option: str) -> list[dict]:
    prefix = f"set_option {option} false in"
    inline = re.compile(r"^(\s*(?:· )?)" + re.escape(prefix) + r" (\S.*)$")
    alone = re.compile(r"^\s*" + re.escape(prefix) + r"\s*$")
    out = []
    for i, line in enumerate(lines):
        m = inline.match(line)
        if m:
            col = len(m.group(1))
            lo = i
            while lo > 0 and (not lines[lo - 1].strip() or indent(lines[lo - 1]) >= col):
                lo -= 1
            lo = max(lo - 1, 0)  # the line that opens the block, which holds its `by`
            hi = i + 1
            while hi < len(lines) and (not lines[hi].strip() or indent(lines[hi]) >= col):
                hi += 1
            out.append(dict(line=i, inline=True, new=m.group(1) + m.group(2), lo=lo, hi=hi - 1))
        elif alone.match(line):
            hi = i + 2
            while hi < len(lines) and not (lines[hi] and not lines[hi][0].isspace() and TOP.match(lines[hi])):
                hi += 1
            out.append(dict(line=i, inline=False, new=None, lo=i, hi=hi - 1))
    return out


def elaborate(path: Path, args: list[str]) -> tuple[int, list[tuple[int, str]], float]:
    start = time.monotonic()
    proc = subprocess.run(["lake", "env", "lean", *args, str(path)], cwd=ROOT, capture_output=True, text=True)
    errors = [(int(m["line"]), m["msg"]) for m in DIAG.finditer(proc.stdout + proc.stderr) if m["kind"] == "error"]
    return proc.returncode, errors, time.monotonic() - start


def process(path: Path, option: str) -> dict:
    original = path.read_text()
    lines = original.split("\n")
    occ = occurrences(lines, option)
    report = {"file": str(path.relative_to(ROOT)), "found": len(occ), "removed": 0, "runs": 0}
    if not occ:
        return report
    by_line = {o["line"]: o for o in occ}
    args = lean_args(path)
    keep: set[int] = set()
    try:
        for _ in range(5):
            removed = set(by_line) - keep
            if not removed:
                break
            kept_lines = [i for i in range(len(lines)) if not (i in removed and not by_line[i]["inline"])]
            text = "\n".join(by_line[i]["new"] if i in removed else lines[i] for i in kept_lines)
            path.write_text(text)
            code, errors, _ = elaborate(path, args)
            report["runs"] += 1
            if code == 0 and not errors:
                report.update(removed=len(removed), kept=len(keep))
                return report
            at = [kept_lines[n - 1] for n, _ in errors if 0 < n <= len(kept_lines)]
            blamed = {i for i in removed if any(by_line[i]["lo"] <= n <= by_line[i]["hi"] for n in at)}
            if not blamed:
                path.write_text(original)
                code0, errors0, _ = elaborate(path, args)
                report["runs"] += 1
                if code0 != 0 or errors0:
                    report["skipped"] = "original does not elaborate"
                    break
                keep |= removed  # an error the scopes do not explain: keep the rest
            else:
                keep |= blamed
        path.write_text(original)
        report["kept"] = len(keep)
        return report
    except BaseException:
        path.write_text(original)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--option", default="backward.isDefEq.respectTransparency.instanceSearchTypes")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--log", type=Path)
    opts = parser.parse_args()
    log = open(opts.log, "a") if opts.log else None
    with ThreadPoolExecutor(opts.jobs) as pool:
        results = list(pool.map(lambda p: process(p.resolve(), opts.option), opts.files))
    for r in results:
        line = json.dumps(r)
        print(line)
        if log:
            log.write(line + "\n")
    print(f"{sum(r['removed'] for r in results)}/{sum(r['found'] for r in results)} prefixes removed", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
