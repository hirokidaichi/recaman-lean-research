#!/usr/bin/env python3
"""Recaman/*.lean と docs/human-proofs/*.md を走査して viewer/manifest.json を生成する。

ビューワー(viewer/index.html)のサイドバーとステータス表示のためのメタデータ。
レポート追加後に再実行すれば反映される。
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "Recaman"
REPORT_DIR = ROOT / "docs" / "human-proofs"
OUT = Path(__file__).resolve().parent / "manifest.json"

DECL_RE = re.compile(r"^(theorem|lemma|def|structure|inductive|abbrev)\s+([A-Za-z0-9_'.]+)")
IMPORT_RE = re.compile(r"^import\s+Recaman\.([A-Za-z0-9_.]+)")


def scan_module(path: Path) -> dict:
    name = path.stem
    lines = path.read_text(encoding="utf-8").splitlines()
    decls = []
    imports = []
    has_docstring = False
    for idx, line in enumerate(lines, start=1):
        if line.startswith("/-!"):
            has_docstring = True
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))
        m = DECL_RE.match(line)
        if m:
            decls.append({"kind": m.group(1), "name": m.group(2), "line": idx})
    report = REPORT_DIR / f"{name}.md"
    return {
        "name": name,
        "lines": len(lines),
        "imports": imports,
        "decls": decls,
        "theorems": sum(1 for d in decls if d["kind"] in ("theorem", "lemma")),
        "defs": sum(1 for d in decls if d["kind"] not in ("theorem", "lemma")),
        "hasEnglishDocstring": has_docstring,
        "hasReport": report.exists(),
    }


def main() -> None:
    modules = sorted(
        (scan_module(p) for p in LEAN_DIR.glob("*.lean")),
        key=lambda m: m["name"],
    )
    manifest = {
        "modules": modules,
        "total": len(modules),
        "withReport": sum(1 for m in modules if m["hasReport"]),
    }
    OUT.write_text(json.dumps(manifest, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"manifest.json: {manifest['total']} modules, {manifest['withReport']} reports", file=sys.stderr)


if __name__ == "__main__":
    main()
