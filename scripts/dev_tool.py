#!/usr/bin/env python3
"""Recamán Research Development & Knowledge Assistant CLI.

Provides automation for:
- Searching past evidence, no-go theorems, countermodels, and stopped branches
- Scaffolding hypothesis cards following AI_RESEARCH_PROTOCOL.md
- Registering new Lean frontier modules into Recaman.lean, contracts, and Audit.lean
- Checking repository health and synchronization
"""

from __future__ import annotations

import argparse
import datetime
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS_DIR = ROOT / "docs"
RECAMAN_DIR = ROOT / "Recaman"
REGISTRY_TSV = DOCS_DIR / "EVIDENCE_REGISTRY.tsv"
CONTRACTS_TSV = DOCS_DIR / "MODULE_IMPORT_CONTRACTS.tsv"
RECAMAN_ROOT_LEAN = ROOT / "Recaman.lean"
AUDIT_LEAN = RECAMAN_DIR / "Audit.lean"
TEMPLATE_CARD = DOCS_DIR / "HYPOTHESIS_CARD_TEMPLATE.md"
FRONTIER_MD = DOCS_DIR / "CURRENT_FRONTIER.md"


def search_evidence(args: argparse.Namespace) -> None:
    """Search evidence registry by keyword, label, or branch."""
    if not REGISTRY_TSV.exists():
        print(f"error: {REGISTRY_TSV} not found", file=sys.stderr)
        sys.exit(1)

    lines = REGISTRY_TSV.read_text(encoding="utf-8").splitlines()
    if not lines:
        return
    header = lines[0].split("\t")
    rows = [line.split("\t") for line in lines[1:] if line.strip()]

    query = (args.query or "").strip().lower()
    label_filter = (args.label or "").strip().upper()
    branch_filter = (args.branch or "").strip().lower()

    matches = []
    for r in rows:
        if len(r) < 7:
            continue
        eid, label, branch, claim, artifact, symbols, reopen = r[:7]
        if label_filter and label != label_filter:
            continue
        if branch_filter and branch_filter not in branch.lower():
            continue
        if query:
            haystack = f"{eid} {label} {branch} {claim} {artifact} {symbols} {reopen}".lower()
            if query not in haystack:
                continue
        matches.append((eid, label, branch, claim, artifact, symbols, reopen))

    if not matches:
        print(f"No evidence matches found (query='{query}', label='{label_filter}', branch='{branch_filter}').")
        return

    print(f"Found {len(matches)} evidence records:\n")
    for eid, label, branch, claim, artifact, symbols, reopen in matches:
        color = {
            "PROVED-LEAN": "\033[92m",
            "PROVED-PAPER": "\033[94m",
            "COMPUTED": "\033[96m",
            "REFUTED": "\033[91m",
            "STOPPED": "\033[93m",
            "CONJECTURED": "\033[95m",
            "OBSERVED": "\033[90m",
        }.get(label, "")
        reset = "\033[0m"

        print(f"[{color}{label:12s}{reset}] {eid}  ({branch})")
        print(f"  Claim:    {claim}")
        print(f"  Artifact: {artifact}")
        if symbols != "-":
            print(f"  Symbols:  {symbols}")
        if reopen != "-":
            print(f"  Reopen:   {reopen}")
        print()


def new_card(args: argparse.Namespace) -> None:
    """Create a new hypothesis card with today's date and unique ID."""
    today = datetime.date.today().strftime("%Y-%m-%d")
    slug = args.slug.strip().replace(" ", "_").upper()
    if not slug:
        print("error: slug cannot be empty", file=sys.stderr)
        sys.exit(1)

    today_cards = list(DOCS_DIR.glob(f"HYPOTHESIS_CARD_{today}*.md"))
    card_num = len(today_cards) + 1
    card_id = f"H-{today.replace('-', '')}-{card_num:02d}"

    card_filename = f"HYPOTHESIS_CARD_{today}_{slug}.md"
    card_path = DOCS_DIR / card_filename

    if card_path.exists() and not args.force:
        print(f"error: card file already exists: {card_path}", file=sys.stderr)
        sys.exit(1)

    template = TEMPLATE_CARD.read_text(encoding="utf-8")
    card_content = template.replace("<short name>", slug)
    card_content = re.sub(r"ID:\s*`H-[^`]+`", f"ID: `{card_id}`", card_content)
    card_content = re.sub(r"Created:\s*", f"Created: {today}\n", card_content)

    card_path.write_text(card_content, encoding="utf-8")
    print(f"Created hypothesis card: {card_path}")
    print(f"  Card ID: {card_id}")
    print(f"  Status:  CONJECTURED")


def add_module(args: argparse.Namespace) -> None:
    """Scaffold a new Lean module and register it with Recaman.lean and contracts."""
    name = args.name.strip()
    if name.startswith("Recaman."):
        name = name[len("Recaman.") :]

    lean_file = RECAMAN_DIR / f"{name}.lean"
    full_module_name = f"Recaman.{name}"

    imports = [i.strip() for i in (args.imports or "").split(";") if i.strip()]
    if not imports:
        imports = ["Recaman.Basic"]
    imports_str = ";".join(imports)

    purpose = (args.purpose or f"Formalization for {name}").strip()

    # 1. Create Lean file if it doesn't exist
    if not lean_file.exists():
        import_lines = "\n".join(f"import {imp}" for imp in imports)
        content = f"{import_lines}\n\n/-!\n# {name}\n\n{purpose}\n-/\n\nnamespace Recaman.{name}\n\n-- Declarations\n\nend Recaman.{name}\n"
        lean_file.write_text(content, encoding="utf-8")
        print(f"Created Lean module source: {lean_file}")
    else:
        print(f"Lean file already exists: {lean_file}")

    # 2. Add to Recaman.lean
    recaman_text = RECAMAN_ROOT_LEAN.read_text(encoding="utf-8")
    import_stmt = f"import {full_module_name}"
    if import_stmt not in recaman_text:
        RECAMAN_ROOT_LEAN.write_text(f"{import_stmt}\n{recaman_text}", encoding="utf-8")
        print(f"Added '{import_stmt}' to Recaman.lean")
    else:
        print(f"'{import_stmt}' already present in Recaman.lean")

    # 3. Add to MODULE_IMPORT_CONTRACTS.tsv
    contract_lines = CONTRACTS_TSV.read_text(encoding="utf-8").splitlines()
    header = contract_lines[0]
    existing = [line.split("\t")[0] for line in contract_lines[1:] if line.strip()]

    if full_module_name not in existing:
        new_row = f"{full_module_name}\t{imports_str}\t{purpose}"
        contract_lines.insert(1, new_row)
        CONTRACTS_TSV.write_text("\n".join(contract_lines) + "\n", encoding="utf-8")
        print(f"Added contract entry to {CONTRACTS_TSV}")
    else:
        print(f"Contract for {full_module_name} already exists in {CONTRACTS_TSV}")

    print("\nNext steps:")
    print(f"  1. Implement proofs in {lean_file}")
    print("  2. Run 'make check' to verify module architecture and axiom boundaries.")


def register_evidence(args: argparse.Namespace) -> None:
    """Register a new evidence row in EVIDENCE_REGISTRY.tsv and sync Audit.lean."""
    label = args.label.strip().upper()
    valid_labels = ["PROVED-LEAN", "PROVED-PAPER", "COMPUTED", "OBSERVED", "CONJECTURED", "REFUTED", "STOPPED"]
    if label not in valid_labels:
        print(f"error: invalid label '{label}'. Must be one of {valid_labels}", file=sys.stderr)
        sys.exit(1)

    branch = args.branch.strip()
    claim = args.claim.strip()
    artifact = args.artifact.strip()
    symbols = args.symbols.strip() if args.symbols else "-"
    reopen = args.reopen.strip() if args.reopen else "-"

    if not (ROOT / artifact).exists() and not Path(artifact).exists():
        print(f"warning: artifact '{artifact}' does not exist on disk yet.", file=sys.stderr)

    lines = REGISTRY_TSV.read_text(encoding="utf-8").splitlines()
    header = lines[0]
    rows = [l.split("\t") for l in lines[1:] if l.strip()]

    # Find highest evidence id
    max_id = 0
    for r in rows:
        m = re.match(r"^E-(\d+)$", r[0])
        if m:
            max_id = max(max_id, int(m.group(1)))

    new_id = f"E-{max_id + 1:03d}"
    if args.id:
        new_id = args.id.strip()

    if label == "PROVED-LEAN" and symbols == "-":
        print("error: PROVED-LEAN requires --symbols (semi-colon separated declaration names)", file=sys.stderr)
        sys.exit(1)

    # If PROVED-LEAN, check / add to Audit.lean
    if label == "PROVED-LEAN" and symbols != "-":
        audit_text = AUDIT_LEAN.read_text(encoding="utf-8")
        added_syms = []
        for sym in symbols.split(";"):
            sym = sym.strip()
            line = f"#print axioms {sym}"
            if line not in audit_text:
                audit_text += f"\n{line}"
                added_syms.append(sym)
        if added_syms:
            AUDIT_LEAN.write_text(audit_text.rstrip() + "\n", encoding="utf-8")
            print(f"Added #print axioms for {len(added_syms)} declarations to Recaman/Audit.lean")

    new_row = f"{new_id}\t{label}\t{branch}\t{claim}\t{artifact}\t{symbols}\t{reopen}"
    lines.insert(1, new_row)
    REGISTRY_TSV.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Registered evidence {new_id} ({label}) in docs/EVIDENCE_REGISTRY.tsv")
    print(f"\nRemember to reference {new_id} in docs/CURRENT_FRONTIER.md before running make check.")


def main() -> None:
    parser = argparse.ArgumentParser(description="Recamán Research Development CLI")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    # search
    p_search = subparsers.add_parser("search", help="Search evidence registry")
    p_search.add_argument("query", nargs="?", default="", help="Keyword query")
    p_search.add_argument("--label", "-l", help="Filter by label (e.g. REFUTED, PROVED-LEAN, STOPPED)")
    p_search.add_argument("--branch", "-b", help="Filter by branch substring")
    p_search.set_defaults(func=search_evidence)

    # new-card
    p_card = subparsers.add_parser("new-card", help="Scaffold a new hypothesis card")
    p_card.add_argument("slug", help="Short identifier / topic for the card (e.g. T6_INTERNAL_S)")
    p_card.add_argument("--force", "-f", action="store_true", help="Overwrite existing card file")
    p_card.set_defaults(func=new_card)

    # add-module
    p_mod = subparsers.add_parser("add-module", help="Add and register a new Lean frontier module")
    p_mod.add_argument("name", help="Module name under Recaman (e.g. T6LocalDonation)")
    p_mod.add_argument("--imports", "-i", default="Recaman.Basic", help="Semi-colon separated direct imports")
    p_mod.add_argument("--purpose", "-p", default="", help="Purpose of module for contracts TSV")
    p_mod.set_defaults(func=add_module)

    # register-evidence
    p_ev = subparsers.add_parser("register-evidence", help="Register a new evidence claim")
    p_ev.add_argument("--id", help="Explicit evidence ID (e.g. E-183). Defaults to auto-increment.")
    p_ev.add_argument("--label", "-l", required=True, help="Evidence label (PROVED-LEAN, REFUTED, COMPUTED, etc.)")
    p_ev.add_argument("--branch", "-b", required=True, help="Research branch")
    p_ev.add_argument("--claim", "-c", required=True, help="Mathematical claim description")
    p_ev.add_argument("--artifact", "-a", required=True, help="Path to proof, code, or data artifact")
    p_ev.add_argument("--symbols", "-s", help="Semi-colon separated Lean declarations (required for PROVED-LEAN)")
    p_ev.add_argument("--reopen", "-r", help="Condition to reopen branch")
    p_ev.set_defaults(func=register_evidence)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
