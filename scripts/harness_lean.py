#!/usr/bin/env python3
"""Lean-dependent harness gates (need a built library; run from scripts/check.sh).

  G6 statement pins     docs/protected_pins/ProtectedStatements.lean pins the intended
                        Lean statement of each protected central claim, and
                        definitions.lock freezes (by hash) every library definition the
                        pins mention. --check-pins fails if a pin does not elaborate, if
                        its hypotheses are contradictory, if any pinned definition drifted,
                        or if a pinned claim is labelled PROVED-LEAN while none of its audit
                        symbols proves the pinned Prop ("implies" check: unfold the pin,
                        intro, apply the theorem, close the rest by assumption; only
                        propext / Classical.choice / Quot.sound allowed).
  Vacuity lint          report-only. Per theorem: Prop hypotheses absent from the proof
                        term, a hypothesis definitionally equal to the conclusion, False
                        derivable from the hypotheses (omega / simp_all / grind), and a
                        conclusion closed by automation without any Recaman constant.
                        "?" = heartbeat timeout (not probed), never "clean".

Usage:
  python3 scripts/harness_lean.py --check-pins
  python3 scripts/harness_lean.py --update-lock            (human-approved pin changes only)
  python3 scripts/harness_lean.py --check-theorem PIN THEOREM [PIN THEOREM ...]
  python3 scripts/harness_lean.py --vacuity-row E-NNN      (paste into the G5 statement audit)
  python3 scripts/harness_lean.py --vacuity-module Recaman/Foo.lean
  python3 scripts/harness_lean.py --vacuity-recent N [--strict]
  python3 scripts/harness_lean.py --vacuity-symbols NAME [NAME ...] [--strict]
Exit status: 0 pass, 1 gate failure (the lint fails only with --strict), 2 tool error.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import harness_gate  # noqa: E402

TOOLS = ROOT / "scripts/lean/HarnessTools.lean"
FIXTURES = ROOT / "scripts/lean/PinFixtures.lean"
VACUITY_FIXTURES = ROOT / "scripts/lean/VacuityFixtures.lean"
PIN_DIR = ROOT / "docs/protected_pins"
PINS_LEAN = PIN_DIR / "ProtectedStatements.lean"
PINS_TSV = PIN_DIR / "PINS.tsv"
LOCK = PIN_DIR / "definitions.lock"
BUILD = ROOT / ".lake/build/harness"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


class ToolError(Exception):
    pass


def lake_lean_path() -> str:
    r = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise ToolError("cannot read LEAN_PATH from lake: " + r.stderr.strip())
    return r.stdout.strip()


_LEAN_PATH: str | None = None


def env() -> dict:
    global _LEAN_PATH
    if _LEAN_PATH is None:
        _LEAN_PATH = lake_lean_path() + os.pathsep + str(BUILD)
    return dict(os.environ, LEAN_PATH=_LEAN_PATH)


def compile_module(src: Path) -> None:
    """Compile a helper file outside the library into BUILD/<stem>.olean."""
    BUILD.mkdir(parents=True, exist_ok=True)
    r = subprocess.run(["lake", "env", "lean", "-o", str(BUILD / (src.stem + ".olean")), str(src)],
                       cwd=ROOT, env=env(), capture_output=True, text=True, timeout=900)
    out = r.stdout + r.stderr
    if r.returncode != 0 or re.search(r"\berror\b", out):
        raise ToolError(f"{src.relative_to(ROOT)} does not compile:\n{out[-3000:]}")


def build(fixtures: bool = False) -> None:
    compile_module(TOOLS)
    compile_module(PINS_LEAN)
    if fixtures:
        compile_module(FIXTURES)


def run_lean(source: str, timeout: int = 1800) -> str:
    with tempfile.TemporaryDirectory(prefix="recaman-harness-") as tmp:
        path = Path(tmp) / "Check.lean"
        path.write_text(source, encoding="utf-8")
        r = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, env=env(),
                           capture_output=True, text=True, timeout=timeout)
    return (r.stdout + r.stderr).replace(str(path), "<check>")


# ---------------------------------------------------------------- pins

def read_pins(path: Path = PINS_TSV) -> list[dict]:
    rows = []
    with open(path, encoding="utf-8") as fh:
        header = next(fh).rstrip("\n").split("\t")
        for line in fh:
            if not line.strip() or line.startswith("#"):
                continue
            rows.append(dict(zip(header, line.rstrip("\n").split("\t"))))
    return rows


def deps_output(pins: list[str]) -> list[str]:
    src = "import HarnessTools\nimport ProtectedStatements\n"
    src += "".join(f"#pin_sanity {p}\n" for p in pins)
    src += "#pin_deps " + " ".join(pins) + "\n"
    out = run_lean(src)
    if re.search(r"\berror\b", out):
        raise ToolError("pin dependency dump failed:\n" + out[-3000:])
    return out.splitlines()


def parse_deps(lines: list[str]) -> list[str]:
    try:
        i = lines.index("PIN-DEPS-BEGIN")
        j = lines.index("PIN-DEPS-END")
    except ValueError as exc:
        raise ToolError("no PIN-DEPS block in Lean output") from exc
    return lines[i + 1:j]


def read_lock(path: Path = LOCK) -> list[str]:
    return [l for l in path.read_text(encoding="utf-8").splitlines() if l and not l.startswith("#")]


def lock_text(deps: list[str]) -> str:
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    return ("# G6 definitions lock: every library constant the pinned statements mention, with\n"
            "# 64-bit fingerprints of its type and value. Human-owned (RECAMAN_HUMAN_APPROVED=1).\n"
            "# Regenerate only after reviewing the change: python3 scripts/harness_lean.py --update-lock\n"
            "# Drift limited to auxiliary names (*.match_N, *._f) usually comes from editing a\n"
            "# neighbouring definition that shares the matcher; `#print` the pinned definitions\n"
            "# before regenerating. Drift only causes false rejections, never acceptances.\n"
            f"# toolchain: {toolchain}\n"
            "# name\tkind\ttype\tvalue\n" + "\n".join(deps) + "\n")


def diff_lock(expected: list[str], actual: list[str]) -> list[str]:
    exp = {l.split("\t")[0]: l for l in expected}
    act = {l.split("\t")[0]: l for l in actual}
    errors = []
    for name in sorted(set(exp) | set(act)):
        if name not in act:
            errors.append(f"{name} is in the lock but no longer used by the pins")
        elif name not in exp:
            errors.append(f"{name} is used by the pins but missing from the lock")
        elif exp[name] != act[name]:
            errors.append(f"{name} changed (lock: {exp[name].split(chr(9), 1)[1]} / now: "
                          f"{act[name].split(chr(9), 1)[1]})")
    return errors


def implies_checks(cases: list[tuple[str, str]], fixtures: bool = False) -> list[tuple[bool, str]]:
    """For each (pin, theorem): does the theorem prove the pinned Prop?"""
    src = "import Recaman\nimport ProtectedStatements\n" + ("import PinFixtures\n" if fixtures else "")
    spans = []
    for i, (pin, thm) in enumerate(cases):
        start = src.count("\n") + 2
        src += (f"\ntheorem pin_check_{i} : {pin} := by\n  unfold {pin}\n  intros\n"
                f"  apply @{thm} <;> assumption\n#print axioms pin_check_{i}\n")
        spans.append((start, src.count("\n")))
    out = run_lean(src)
    # split the output into messages and keep the first open goal of each case's first error
    goals: dict[int, str] = {}
    for block in re.split(r"\n(?=<check>:\d+:\d+: )", "\n" + out):
        head = re.match(r"\s*<check>:(\d+):\d+: error", block)
        if not head:
            continue
        line = int(head.group(1))
        case = next((k for k, (lo, hi) in enumerate(spans) if lo <= line <= hi), None)
        goal = re.search(r"^⊢ (.+)$", block, re.M)
        if case is not None and case not in goals:
            goals[case] = goal.group(1).strip() if goal else block.split("error:", 1)[-1].strip().splitlines()[0]
    flat = re.sub(r"\n[ \t]+", " ", out)
    results = []
    for i, (pin, thm) in enumerate(cases):
        m = re.search(rf"'pin_check_{i}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", flat)
        if m is None:
            results.append((False, "no axiom report (the check did not elaborate)"))
            continue
        used = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
        if used <= ALLOWED:
            results.append((True, "proves the pin"))
        elif "sorryAx" in used:
            results.append((False, "does not prove the pin" +
                            (f"; first error: {goals[i][:160]}" if i in goals else "")))
        else:
            results.append((False, f"uses non-standard axioms {sorted(used - ALLOWED)}"))
    return results


def check_pins(registry: Path = ROOT / "docs/EVIDENCE_REGISTRY.tsv", lock: Path = LOCK) -> int:
    build()
    rows = read_pins()
    pinned = [r for r in rows if r["pin"] != "-"]
    errors = []
    lines = deps_output([r["pin"] for r in pinned])
    for r in pinned:
        sanity = next((l for l in lines if l.startswith(f"PIN-SANITY {r['pin']} ")), "")
        if not sanity.endswith(" consistent"):
            errors.append(f"{r['id']}: pin {r['pin']} sanity: {sanity or 'missing'}")
    actual = parse_deps(lines)
    errors += [f"G6 definitions lock: {e}" for e in diff_lock(read_lock(lock), actual)]
    labels = {c[0]: (c[1], c[5]) for c in harness_gate.read_registry(registry)}
    proved = [r for r in pinned if labels.get(r["id"], ("", ""))[0] == "PROVED-LEAN"]
    for r in proved:
        symbols = [s for s in labels[r["id"]][1].split(";") if s and s != "-"]
        results = implies_checks([(r["pin"], s) for s in symbols]) if symbols else []
        if not any(ok for ok, _ in results):
            detail = "; ".join(f"{s}: {why}" for s, (_, why) in zip(symbols, results)) or "no audit symbols"
            errors.append(f"{r['id']}: G6 labelled PROVED-LEAN but no audit symbol proves {r['pin']} ({detail})")
    for e in errors:
        print("error:", e, file=sys.stderr)
    if errors:
        return 1
    unpinned = [r["id"] for r in rows if r["pin"] == "-"]
    print(f"G6 statement pins: {len(pinned)} pinned ({', '.join(r['id'] for r in pinned)}), "
          f"{len(unpinned)} unpinned ({', '.join(unpinned) or '-'}); definitions lock matches "
          f"({len(actual)} constants); {len(proved)} pinned claims labelled PROVED-LEAN.")
    return 0


def update_lock() -> int:
    build()
    pinned = [r["pin"] for r in read_pins() if r["pin"] != "-"]
    deps = parse_deps(deps_output(pinned))
    LOCK.write_text(lock_text(deps), encoding="utf-8")
    print(f"wrote {LOCK.relative_to(ROOT)} ({len(deps)} constants); commit it with RECAMAN_HUMAN_APPROVED=1")
    return 0


def check_theorems(pairs: list[str]) -> int:
    if len(pairs) % 2:
        raise ToolError("--check-theorem takes PIN THEOREM pairs")
    cases = list(zip(pairs[::2], pairs[1::2]))
    fixtures = any(p.startswith("PinFixtures.") or t.startswith("PinFixtures.") for p, t in cases)
    build(fixtures=fixtures)
    bad = 0
    for (pin, thm), (ok, why) in zip(cases, implies_checks(cases, fixtures=fixtures)):
        print(f"{'pass' if ok else 'fail'}\t{pin}\t{thm}\t{why}")
        bad += not ok
    return 1 if bad else 0


# ---------------------------------------------------------------- vacuity lint

def module_name(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def vacuity(symbols: list[str] | None = None, module: str | None = None) -> list[str]:
    compile_module(TOOLS)
    src = "import Recaman\nimport HarnessTools\n"
    if any(s.startswith("VacuityFixtures.") for s in symbols or []):
        compile_module(VACUITY_FIXTURES)
        src += "import VacuityFixtures\n"
    if module:
        src += f"#vacuity_probe_module {module}\n"
    else:
        src += "#vacuity_probe " + " ".join(symbols or []) + "\n"
    out = run_lean(src)
    if re.search(r"\berror\b", out):
        raise ToolError("vacuity probe failed:\n" + out[-3000:])
    return [l for l in out.splitlines() if re.match(r"^(FLAG|ok  |\?   |module )", l)]


def proved_rows(registry: Path = ROOT / "docs/EVIDENCE_REGISTRY.tsv") -> list[list[str]]:
    return [c for c in harness_gate.read_registry(registry) if c[1] == "PROVED-LEAN" and c[5] != "-"]


def lint_report(lines: list[str], strict: bool, title: str) -> int:
    flagged = [l for l in lines if l.startswith("FLAG")]
    unknown = [l for l in lines if l.startswith("?")]
    print(f"Vacuity lint ({title}; report-only): {len(flagged)} flagged, {len(unknown)} unknown, "
          f"{sum(1 for l in lines if l.startswith(('FLAG', 'ok', '?')))} theorems")
    for l in lines:
        if not l.startswith("ok"):
            print("  " + l)
    return 1 if strict and flagged else 0


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    strict = "--strict" in argv
    argv = [a for a in argv if a != "--strict"]
    cmd, rest = argv[0], argv[1:]
    if cmd == "--check-pins":
        return check_pins(*(Path(a) for a in rest[:2]))
    if cmd == "--update-lock":
        return update_lock()
    if cmd == "--check-theorem":
        return check_theorems(rest)
    if cmd == "--vacuity-row":
        row = next((c for c in proved_rows() if c[0] == rest[0]), None)
        if row is None:
            raise ToolError(f"{rest[0]} is not a PROVED-LEAN row with audit symbols")
        return lint_report(vacuity(row[5].split(";")), strict, rest[0])
    if cmd == "--vacuity-module":
        return lint_report(vacuity(module=module_name(rest[0])), strict, rest[0])
    if cmd == "--vacuity-symbols":
        return lint_report(vacuity(rest), strict, "named theorems")
    if cmd == "--vacuity-recent":
        n = int(rest[0]) if rest else 5
        rows = sorted(proved_rows(), key=lambda c: int(c[0][2:]))[-n:]
        symbols = [s for c in rows for s in c[5].split(";")]
        return lint_report(vacuity(symbols), strict, f"audit symbols of {', '.join(c[0] for c in rows)}")
    print(__doc__)
    return 2


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except ToolError as exc:
        print("error:", exc, file=sys.stderr)
        sys.exit(2)
