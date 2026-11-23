#!/usr/bin/env python3
"""Replace `nlinarith` by `linarith` with the product facts that `nlinarith`'s proof uses.

`nlinarith` adds the pairwise products of all hypotheses (and squares of atoms) to the
`linarith` problem, which is what makes it slow. Its final proof only uses a few of them.
When none of those depends on the negated goal, the same proof is found by
`linarith [hints, p₁, …, pₖ]`, where the pᵢ are the products the proof used.

For each file the script

1. probes: adds a local tactic `nl2l_probe` (see PROBE below) and wraps occurrence i as
   `(nl2l_probe i (nlinarith ...))`. The probe runs the original call, reads the products out
   of the proof term it produced and logs them. It logs `NEG` when a product involves the
   negated goal or an inaccessible hypothesis, which `linarith` hints cannot name. A factor
   that is a hypothesis `h : a ≤ b` is written `sub_nonneg.2 h`; any other factor is
   written `(by linarith : 0 ≤ q)` with the polynomial `q` the product used.
2. rewrites each occurrence whose runs all logged the same usable product list to
   `linarith [<original hints>, <products>]` (wrapping hint lists past 100 columns),
   elaborates the file, and puts back any occurrence that an error points into, until the
   file elaborates with no new error or warning.
3. times the original and the rewritten file with the same command, one after the other.

Elaboration uses `lake env lean` with the options `lakefile.toml` passes to Lean, so no
`.olean` is written, and every module FILE imports must already be built or restored from
the cache. Afterwards `lake build <module>` checks each changed module the usual way.

usage: scripts/nlinarith-to-linarith.py [--jobs N] [--report out.json] [--dry-run] FILE...
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import subprocess
import sys
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TAG = "NL2L"

PROBE = r'''
open Lean Elab Tactic Meta in
/-- Run the given `nlinarith` call and log, as `linarith` hints, the products its proof uses. -/
local elab "nl2l_probe " n:num t:tactic : tactic => do
  let g ← getMainGoal
  evalTactic t
  let pf ← instantiateMVars (.mvar g)
  let heads := [``mul_nonneg_of_nonpos_of_nonpos, ``mul_pos_of_neg_of_neg,
    ``Mathlib.Tactic.Linarith.zero_mul_eq, ``Mathlib.Tactic.Linarith.mul_zero_eq,
    ``sq_nonneg, ``mul_self_nonneg]
  let found ← IO.mkRef (#[] : Array Expr)
  pf.forEach fun e => do
    if let .const c _ := e.getAppFn then
      if heads.contains c then
        let ar := (← getConstInfo c).type.getForallBinderNames.length
        if e.getAppNumArgs == ar then found.modify (·.push e)
  let result ← g.withContext do
    let pp (e : Expr) : MetaM String := do
      return (← PrettyPrinter.ppTerm (← PrettyPrinter.delab e)).pretty 100000
    let named (h : Expr) : MetaM (Option String) := do
      if h.isFVar && !(← h.fvarId!.getDecl).userName.hasMacroScopes then
        return some (← pp h)
      return none
    -- `a : p ≤ 0` or `a : p < 0` becomes a hint proving `0 ≤ q` or `0 < q` with `q = -p`.
    let factor (a : Expr) : MetaM String := do
      let fn := a.getAppFn.constName?
      if fn == some ``Mathlib.Tactic.Linarith.sub_nonpos_of_le then
        if let some h ← named a.appArg! then return s!"sub_nonneg.2 {h}"
      if fn == some ``Mathlib.Tactic.Linarith.sub_neg_of_lt then
        if let some h ← named a.appArg! then return s!"sub_pos.2 {h}"
      if fn == some ``le_of_lt then
        let b := a.appArg!
        if b.getAppFn.constName? == some ``Mathlib.Tactic.Linarith.sub_neg_of_lt then
          if let some h ← named b.appArg! then return s!"(sub_pos.2 {h}).le"
      let ty ← whnfR (← instantiateMVars (← inferType a))
      let (rel, args) ← match ty.getAppFnArgs with
        | (``LE.le, args) => pure ("≤", args)
        | (``LT.lt, args) => pure ("<", args)
        | _ => throwError "unexpected factor"
      let p := args[2]!
      let q ← match p.getAppFnArgs with
        | (``HSub.hSub, #[_, _, _, _, x, y]) => mkAppM ``HSub.hSub #[y, x]
        | _ => mkAppM ``Neg.neg #[p]
      let q := (← simpOnlyNames [``one_mul, ``mul_one, ``sub_zero, ``zero_sub, ``add_zero,
        ``zero_add, ``neg_neg, ``neg_sub] q).expr
      return s!"(by linarith : (0 : {← pp args[0]!}) {rel} {← pp q})"
    let mut texts : Array String := #[]
    for e in (← found.get) do
      if e.hasLooseBVars || e.hasMVar then return "NEG"
      let lctx ← getLCtx
      if ← (collectFVars {} e).fvarIds.anyM fun f => do
          match lctx.find? f with
          | some d => return d.userName.hasMacroScopes
          | none => return true then
        return "NEG"
      let args := e.getAppArgs
      let arg (a : Expr) : MetaM String := do
        let s ← factor a
        return if s.startsWith "(by " then s else s!"({s})"
      let s ← match e.getAppFn.constName? with
        | some ``mul_nonneg_of_nonpos_of_nonpos =>
          pure s!"mul_nonneg {← arg args[args.size - 2]!} {← arg args.back!}"
        | some ``mul_pos_of_neg_of_neg =>
          pure s!"mul_pos {← arg args[args.size - 2]!} {← arg args.back!}"
        | some ``sq_nonneg => pure s!"sq_nonneg ({← pp args.back!} : {← pp (← inferType args.back!)})"
        | some ``mul_self_nonneg =>
          pure s!"mul_self_nonneg ({← pp args.back!} : {← pp (← inferType args.back!)})"
        | _ => return "NEG"
      unless texts.contains s do texts := texts.push s
    return "@@".intercalate texts.toList
  logInfo m!"NL2L|{n.getNat}|{result}"
'''



def lean_args(path: Path) -> list[str]:
    """The options Lake passes to Lean for this file (package and library leanOptions)."""
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    options = dict(config.get("leanOptions", {}))
    module = ".".join(path.relative_to(ROOT / "src").with_suffix("").parts)
    for lib in config.get("lean_lib", []):
        globs = lib.get("globs", [])
        if any(re.fullmatch(g.replace(".", r"\.").replace(r"\.+", r"\..+"), module) for g in globs):
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


def code_mask(text: str) -> list[bool]:
    """True for characters outside comments and string literals."""
    mask = [True] * len(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth += 1; mask[i] = mask[i + 1] = False; i += 2; continue
            if text.startswith("-/", i):
                depth -= 1; mask[i] = mask[i + 1] = False; i += 2; continue
            mask[i] = False; i += 1; continue
        if text.startswith("/-", i):
            depth = 1; mask[i] = mask[i + 1] = False; i += 2; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = False
            i = j; continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i, min(j + 1, n)):
                mask[k] = False
            i = j + 1; continue
        i += 1
    return mask


WORD = re.compile(r"(?<![\w.'!?])nlinarith(?![\w'!?])")


def occurrences(text: str) -> list[tuple[int, int, str]]:
    """(start, end, arguments) for each `nlinarith [only] [[hints]]` in code."""
    mask = code_mask(text)
    found = []
    for m in WORD.finditer(text):
        if not mask[m.start()]:
            continue
        j = k = m.end()
        while k < len(text) and text[k] in " \t":
            k += 1
        if text.startswith("only", k) and not re.match(r"[\w'!?]", text[k + 4:k + 5]):
            j = k = k + 4
            while k < len(text) and text[k] in " \t\n":
                k += 1
        if k < len(text) and text[k] == "[":
            depth, e = 0, k
            while e < len(text):
                if mask[e]:
                    if text[e] in "[(⟨{":
                        depth += 1
                    elif text[e] in "])⟩}":
                        depth -= 1
                        if depth == 0:
                            break
                e += 1
            if depth != 0:
                continue
            j = e + 1
        if found and m.start() < found[-1][1]:
            continue  # inside the hints of the previous occurrence
        found.append((m.start(), j, text[m.end():j]))
    return found


def rewrite(text: str, occ, choose) -> tuple[str, list[int]]:
    """Apply `choose` to every occurrence; also return where each replacement starts."""
    out, last, starts, pos = [], 0, [], 0
    for i, (s, e, args) in enumerate(occ):
        out.append(text[last:s])
        pos += s - last
        starts.append(pos)
        new = choose(i, args, text[s:e])
        out.append(new)
        pos += len(new)
        last = e
    out.append(text[last:])
    return "".join(out), starts


def closing(text: str, b: int) -> int:
    """Index of the bracket closing the one at `b`."""
    depth = 0
    for e in range(b, len(text)):
        if text[e] in "[(⟨{":
            depth += 1
        elif text[e] in "])⟩}":
            depth -= 1
            if depth == 0:
                return e
    return -1


def call_end(text: str, s: int) -> int:
    m = re.match(r"\(?n?l?inarith(\s+only)?\s*", text[s:]) or re.match(r"", text[s:])
    b = s + m.end()
    return closing(text, b) + 1 if b < len(text) and text[b] == "[" else s + len(m.group(0).rstrip())


def wrap(text: str, starts: list[int], chosen: set[int], width: int = 100) -> tuple[str, list[int]]:
    """Break the hint list of each chosen `linarith` call whose line is too long.

    Continuation lines are indented two columns past `linarith`: Lean reads a line that starts
    at or left of the tactic as the end of the call. Calls starting past column 60 are left
    on one line. Returns the new text and the shifted start of every occurrence.
    """
    starts = list(starts)
    for i in sorted(chosen, key=lambda i: starts[i]):
        s = starts[i]
        ls = text.rfind("\n", 0, s) + 1
        le = text.find("\n", s)
        le = len(text) if le < 0 else le
        m = re.match(r"linarith(\s+only)?\s*\[", text[s:])
        if le - ls <= width or not m or s - ls + 2 > 60:
            continue
        b = s + m.end() - 1
        e = closing(text, b)
        if e < 0 or e > le:
            continue
        items, depth, cur = [], 0, ""
        for ch in text[b + 1:e]:
            if ch in "[(⟨{":
                depth += 1
            elif ch in "])⟩}":
                depth -= 1
            if ch == "," and depth == 0:
                items.append(cur.strip()); cur = ""
            else:
                cur += ch
        items.append(cur.strip())
        indent = " " * (s - ls + 2)
        lines, line = [], text[ls:b + 1]
        for k, item in enumerate(items):
            piece = item + ("," if k < len(items) - 1 else "")
            joined = line + piece if line.endswith("[") else line + " " + piece
            if len(joined) > width and line.strip() and not line.endswith("["):
                lines.append(line)
                line = indent + piece
            else:
                line = joined
        block = "\n".join(lines + [line])
        delta = len(block) - (e - ls)
        text = text[:ls] + block + text[e:]
        starts = [t + delta if t > s else t for t in starts]
    return text, starts


def spans(text: str, starts: list[int]) -> list[tuple[int, int]]:
    """First and last line of each call."""
    return [(text.count("\n", 0, s) + 1, text.count("\n", 0, call_end(text, s)) + 1) for s in starts]


def with_probe(text: str) -> str:
    """Add the probe tactic, and the meta imports it needs, after the import block."""
    lines = text.split("\n")
    last = max((i for i, l in enumerate(lines)
                if re.match(r"(public |private )?(meta )?import ", l)), default=-1)
    if last < 0:
        raise ValueError("no import block")
    kind = "meta import" if text.lstrip().startswith("module") else "import"
    header = [f"{kind} Lean", f"{kind} Mathlib.Lean.Meta.Simp"]
    return "\n".join(lines[:last + 1] + header + PROBE.split("\n") + lines[last + 1:])


def linarith_call(args: str, hints: list[str]) -> str:
    """`linarith` with the original arguments plus the product hints not already among them."""
    given = re.sub(r"\s+", "", args)
    hints = [h for h in hints if h and re.sub(r"\s+|:[^()]*\)$", "", h).rstrip("(") not in given
             and re.sub(r"\s+", "", re.sub(r" : [^()]*\)$", ")", h)) not in given]
    if not hints:
        return f"linarith{args}"
    extra = ", ".join(hints)
    body = args.rstrip()
    if body.endswith("]"):
        inner = body[body.index("[") + 1:-1].strip()
        return f"linarith{body[:body.index('[')]}[{inner + ', ' if inner else ''}{extra}]"
    return f"linarith{args} [{extra}]"


def elaborate(path: Path, args: list[str]) -> tuple[int, str, float]:
    start = time.monotonic()
    proc = subprocess.run(["lake", "env", "lean", *args, str(path)], cwd=ROOT,
                          capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr, time.monotonic() - start


DIAG = re.compile(r"^(?P<file>.*?):(?P<line>\d+):\d+: (?P<kind>error|warning)(\([^)]*\))?: (?P<msg>.*)$",
                  re.M)


def diagnostics(output: str) -> list[tuple[int, str]]:
    return [(int(m["line"]), f"{m['kind']}: {m['msg']}") for m in DIAG.finditer(output)]


def process(path: Path, dry_run: bool) -> dict:
    original = path.read_text()
    occ = occurrences(original)
    report = {"file": str(path.relative_to(ROOT)), "occurrences": len(occ), "replaced": 0}
    if not occ:
        return report
    args = lean_args(path)
    probe, _ = rewrite(original, occ, lambda i, a, whole: f"(nl2l_probe {i} ({whole}))")
    try:
        path.write_text(with_probe(probe))
        _, out, _ = elaborate(path, args)
    finally:
        path.write_text(original)
    seen: dict[int, set[str]] = {}
    for i, payload in re.findall(rf"{TAG}\|(\d+)\|(.*)", out):
        seen.setdefault(int(i), set()).add(payload.strip())
    usable = {i: next(iter(p)) for i, p in seen.items() if len(p) == 1 and next(iter(p)) != "NEG"}
    report.update(usable=len(usable),
                  negated_goal=sum(1 for p in seen.values() if "NEG" in p),
                  varying=sum(1 for p in seen.values() if len(p) > 1 and "NEG" not in p),
                  not_reached=len(occ) - len(seen))
    if not usable or dry_run:
        return report
    code0, out0, t0 = elaborate(path, args)
    before = {msg for _, msg in diagnostics(out0)}
    chosen = set(usable)
    try:
        for _ in range(4):
            new, starts = rewrite(original, occ, lambda i, a, whole:
                                  linarith_call(a, usable[i].split("@@")) if i in chosen else whole)
            new, starts = wrap(new, starts, chosen)
            lines = spans(new, starts)
            path.write_text(new)
            code1, out1, t1 = elaborate(path, args)
            fresh = [(line, msg) for line, msg in diagnostics(out1) if msg not in before]
            if code1 == code0 and not fresh:
                break
            blamed = {i for i in chosen for line, _ in fresh if lines[i][0] <= line <= lines[i][1]}
            if not blamed:
                chosen = set()
                break
            chosen -= blamed
        else:
            chosen = set()
        if not chosen:
            path.write_text(original)
            report.update(reverted=True)
            return report
    except BaseException:
        path.write_text(original)
        raise
    report.update(replaced=len(chosen), seconds_before=round(t0, 1), seconds_after=round(t1, 1))
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--jobs", type=int, default=1,
                        help="files processed at once; timings are only comparable with 1")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--dry-run", action="store_true", help="probe only, change nothing")
    opts = parser.parse_args()
    paths = [p.resolve() for p in opts.files]
    results = []
    with concurrent.futures.ThreadPoolExecutor(opts.jobs) as pool:
        for r in pool.map(lambda p: process(p, opts.dry_run), paths):
            results.append(r)
            print(json.dumps(r, ensure_ascii=False), flush=True)
    if opts.report:
        opts.report.write_text(json.dumps(results, indent=1, ensure_ascii=False) + "\n")
    total = sum(r["occurrences"] for r in results)
    done = sum(r["replaced"] for r in results)
    print(f"{done}/{total} nlinarith calls replaced in {sum(1 for r in results if r['replaced'])} files",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
