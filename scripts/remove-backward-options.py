#!/usr/bin/env python3
"""Remove `set_option backward.* …` options that a file no longer needs.

For each FILE the script deletes every `set_option backward.<name> <value>` line, and the
`set_option backward.<name> <value> in` prefix of a tactic, elaborates
the file, and puts back each option whose declaration (or, for a file-wide option, the
rest of the file) now reports an error. It repeats until the file elaborates with no error
that the original did not have, then times the original and the result.

Elaboration uses `lake env lean` with the options `lakefile.toml` passes to Lean; every module
FILE imports must already be built or restored from the cache.

usage: scripts/remove-backward-options.py [--report out.json] FILE...
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def lean_args(path: Path) -> list[str]:
    """The options Lake passes to Lean for this file (package and library leanOptions)."""
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    options = dict(config.get("leanOptions", {}))
    module = ".".join(path.relative_to(ROOT / "src").with_suffix("").parts)
    for lib in config.get("lean_lib", []):
        if any(re.fullmatch(g.replace(".", r"\.").replace(r"\.+", r"\..+"), module)
               for g in lib.get("globs", [])):
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


def elaborate(path: Path, args: list[str]) -> tuple[int, str, float]:
    start = time.monotonic()
    proc = subprocess.run(["lake", "env", "lean", *args, str(path)], cwd=ROOT,
                          capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr, time.monotonic() - start


DIAG = re.compile(r"^(?P<file>.*?):(?P<line>\d+):\d+: (?P<kind>error|warning)(\([^)]*\))?: (?P<msg>.*)$",
                  re.M)


def diagnostics(output: str) -> list[tuple[int, str]]:
    return [(int(m["line"]), f"{m['kind']}: {m['msg']}") for m in DIAG.finditer(output)]


OPTION = re.compile(r"^\s*set_option backward\.[\w.]+ (true|false)( in)?\s*$")
# `set_option backward.… in <tactic>` on one line inside a proof
INLINE = re.compile(r"^(\s*(?:· )?)set_option backward\.[\w.]+ (true|false) in (\S.*)$")
TOP = re.compile(r"^(@\[|/--|theorem|lemma|def|abbrev|instance|example|structure|class|inductive|"
                 r"noncomputable|private|protected|public|nonrec|irreducible_def|set_option|"
                 r"attribute|open|namespace|section|end|variable|omit|include|#|--|macro|syntax|elab)")


def drop(line: str) -> str:
    """The line without its option: the tactic for an inline option, else nothing."""
    m = INLINE.match(line)
    return m.group(1) + m.group(3) if m else ""


def owners(lines: list[str]) -> list[tuple[int, int, int]]:
    """(option line, first owned line, last owned line), 0-based."""
    out = []
    for i, line in enumerate(lines):
        if INLINE.match(line):
            out.append((i, i, i))
            continue
        m = OPTION.match(line)
        if not m:
            continue
        if m.group(2):  # `… in`: the option covers the next command
            j = i + 1
            while j < len(lines) and OPTION.match(lines[j]):
                j += 1
            k = j + 1
            while k < len(lines) and not (lines[k] and not lines[k][0].isspace() and TOP.match(lines[k])):
                k += 1
            out.append((i, i, k - 1))
        else:
            out.append((i, i, len(lines) - 1))
    return out


def process(path: Path) -> dict:
    original = path.read_text()
    lines = original.split("\n")
    opts = owners(lines)
    report = {"file": str(path.relative_to(ROOT)), "options": len(opts), "removed": 0}
    if not opts:
        return report
    args = lean_args(path)
    code0, out0, t0 = elaborate(path, args)
    if code0 != 0:
        report["skipped"] = "original does not elaborate"
        return report
    before = {msg for _, msg in diagnostics(out0) if msg.startswith("error")}
    keep: set[int] = set()
    try:
        for _ in range(6):
            removed = {o[0] for o in opts} - keep
            if not removed:
                break
            # Deleted lines become blank so that line numbers stay put.
            new = "\n".join(drop(line) if i in removed else line for i, line in enumerate(lines))
            path.write_text(new)
            code1, out1, t1 = elaborate(path, args)
            fresh = [line - 1 for line, msg in diagnostics(out1)
                     if msg.startswith("error") and msg not in before]
            if code1 == 0 and not fresh:
                break
            blamed = {o[0] for o in opts if o[0] in removed and any(o[1] <= l <= o[2] for l in fresh)}
            keep |= blamed or removed
        else:
            keep = {o[0] for o in opts}
        removed = {o[0] for o in opts} - keep
        if not removed:
            path.write_text(original)
            return report
        # Drop the blanked lines for good.
        final = "\n".join(drop(line) if i in removed else line for i, line in enumerate(lines)
                          if i not in removed or INLINE.match(line))
        path.write_text(final)
        code2, out2, t2 = elaborate(path, args)
        if code2 != 0 or {m for _, m in diagnostics(out2) if m.startswith("error")} - before:
            path.write_text(original)
            report["reverted"] = True
            return report
    except BaseException:
        path.write_text(original)
        raise
    report.update(removed=len(removed), seconds_before=round(t0, 1), seconds_after=round(t2, 1))
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--report", type=Path)
    opts = parser.parse_args()
    results = []
    for p in opts.files:
        r = process(p.resolve())
        results.append(r)
        print(json.dumps(r), flush=True)
    if opts.report:
        opts.report.write_text(json.dumps(results, indent=1) + "\n")
    print(f"{sum(r['removed'] for r in results)}/{sum(r['options'] for r in results)} options removed",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
