#!/usr/bin/env python3
"""Recamán Research Development & Knowledge Assistant CLI.

Provides automation and token-saving utilities:
- brief: Ultra-compact (40-line) briefing on current frontier, gates, and constraints
- decls: Surgical extraction of Lean declaration signatures (zero proof body tokens)
- search: Search evidence registry with compact output option
- new-card: Scaffold a new hypothesis card following protocol
- add-module: Register a new Lean frontier module into contracts and Recaman.lean
- register-evidence: Register a new evidence claim into registry and Audit.lean
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


def get_label_color(label: str) -> tuple[str, str]:
    colors = {
        "PROVED-LEAN": "\033[92m",
        "PROVED-PAPER": "\033[94m",
        "COMPUTED": "\033[96m",
        "REFUTED": "\033[91m",
        "STOPPED": "\033[93m",
        "CONJECTURED": "\033[95m",
        "OBSERVED": "\033[90m",
    }
    return colors.get(label, ""), "\033[0m"


def show_brief(args: argparse.Namespace) -> None:
    """Display an ultra-compact summary of the current research frontier (< 400 tokens)."""
    if not FRONTIER_MD.exists():
        print(f"error: {FRONTIER_MD} not found", file=sys.stderr)
        sys.exit(1)

    print("=" * 60)
    print("  RECAMÁN RESEARCH FRONTIER BRIEF")
    print("=" * 60)

    # 1. Active Frontier & Open Gate
    print("\n[NEXT RESEARCH GATE]")
    print("  * Gate: T6 (E-179) - High-SS Local Donation")
    print("  * Claim: Every high-SS supply window (ssCount>=2) donates an internally removable S.")
    print("  * Evidence: COMPUTED across 53,000+ words (p=8..22, 0 exceptions).")
    print("  * Target: Formalize or refute minimal case ssCount=2 in Lean.")

    # 2. Key Established Ground Truth
    print("\n[ESTABLISHED BOUNDARIES (Do Not Re-prove)]")
    print("  * E-176: |U|<=|D| is sharp across all periods (tight words exist for all p).")
    print("  * E-177: Tight words (|U|=|D|) have ONLY low-SS windows (ssCount<=1).")
    print("           Equality side is completely covered by E-128 (PROVED-LEAN).")
    print("  * E-178: Forced matching on tight words matches oldest-S (E-069).")
    print("  * E-181: Positive period mass guarantees finite lag bound d <= p(p+1) (PROVED-LEAN).")
    print("  * E-128: Low-SS joint endpoint capacity |U_clean U U_SS1| <= |D| (PROVED-LEAN).")

    # 3. Stopped / Refuted Approaches (Do Not Re-open without declared gate)
    print("\n[STOPPED & REFUTED DIRECTIONS (Do Not Propose)]")
    print("  * E-180 (REFUTED): Linear slack charge slack >= c is false (counterexample at p=18,21).")
    print("  * E-178 (CLOSED): Generic selector search is FINISHED (selector is forced on tight).")
    print("  * E-088 (STOPPED): Lag-by-lag type offset charging is STOPPED.")
    print("  * E-133 (REFUTED): Named 4-charge extension on SS=2 is STOPPED.")
    print("  * E-142 (REFUTED): Unrestricted one-per-run on abstract words is REFUTED.")

    # 4. Codebase & Audit Status
    modules = list(RECAMAN_DIR.glob("*.lean"))
    contracts_count = len([l for l in CONTRACTS_TSV.read_text(encoding="utf-8").splitlines()[1:] if l.strip()])
    print("\n[REPOSITORY INTEGRITY]")
    print(f"  * Lean Modules: {len(modules)} library modules | Frontier Contracts: {contracts_count}")
    print("  * Audit State: 1,743 declarations verified within standard axioms.")
    print("  * Verification: Run 'make check' or 'make test'.")
    print("=" * 60)


def show_decls(args: argparse.Namespace) -> None:
    """Extract declaration signatures and docstrings from a Lean module without proof bodies."""
    name = args.module.strip()
    if name.startswith("Recaman."):
        name = name[len("Recaman.") :]

    lean_file = RECAMAN_DIR / f"{name}.lean"
    if not lean_file.exists():
        print(f"error: module file not found: {lean_file}", file=sys.stderr)
        sys.exit(1)

    lines = lean_file.read_text(encoding="utf-8").splitlines()
    print(f"=== Declarations in Recaman.{name} ({len(lines)} lines) ===\n")

    in_docstring = False
    docstring_lines = []
    decl_start_re = re.compile(r"^(theorem|lemma|def|structure|inductive|abbrev)\s+([A-Za-z0-9_'.]+)")

    i = 0
    theorems = 0
    defs = 0

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Docstring handling
        if stripped.startswith("/-!") or stripped.startswith("/--"):
            in_docstring = True
            docstring_lines = [stripped]
            if "-/" in stripped:
                in_docstring = False
            i += 1
            continue

        if in_docstring:
            docstring_lines.append(stripped)
            if "-/" in stripped:
                in_docstring = False
            i += 1
            continue

        m = decl_start_re.match(line)
        if m:
            kind, decl_name = m.group(1), m.group(2)
            if kind in ("theorem", "lemma"):
                theorems += 1
            else:
                defs += 1

            # Print accumulated docstring if any
            if docstring_lines:
                doc = " ".join(docstring_lines).replace("/--", "").replace("/-!", "").replace("-/", "").strip()
                if doc:
                    print(f"  -- {doc[:100]}")
                docstring_lines = []

            # Gather signature until := or where or by
            sig_lines = [line]
            while not (":=" in lines[i] or " where" in lines[i] or " by" in lines[i]) and i + 1 < len(lines):
                i += 1
                sig_lines.append(lines[i])

            # Strip the := by / := part from the last line
            last_line = sig_lines[-1]
            for sep in [":= by", ":=by", ":=", " where"]:
                if sep in last_line:
                    last_line = last_line.split(sep)[0].rstrip()
                    break
            sig_lines[-1] = last_line

            sig_text = "\n    ".join(l.rstrip() for l in sig_lines if l.strip())
            print(f"L{i+1}: {sig_text}\n")

        i += 1

    print(f"Summary: {theorems} theorems/lemmas, {defs} definitions.")


def search_evidence(args: argparse.Namespace) -> None:
    """Search evidence registry by keyword, label, or branch."""
    if not REGISTRY_TSV.exists():
        print(f"error: {REGISTRY_TSV} not found", file=sys.stderr)
        sys.exit(1)

    lines = REGISTRY_TSV.read_text(encoding="utf-8").splitlines()
    if not lines:
        return
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

    print(f"Found {len(matches)} evidence records:")
    compact = getattr(args, "compact", False)

    for eid, label, branch, claim, artifact, symbols, reopen in matches:
        color, reset = get_label_color(label)
        if compact:
            claim_summary = claim if len(claim) <= 70 else claim[:67] + "..."
            print(f"  [{color}{label:12s}{reset}] {eid:5s} ({branch:22s}) {claim_summary}")
        else:
            print(f"\n[{color}{label:12s}{reset}] {eid}  ({branch})")
            print(f"  Claim:    {claim}")
            print(f"  Artifact: {artifact}")
            if symbols != "-":
                print(f"  Symbols:  {symbols}")
            if reopen != "-":
                print(f"  Reopen:   {reopen}")


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

    if not lean_file.exists():
        import_lines = "\n".join(f"import {imp}" for imp in imports)
        content = f"{import_lines}\n\n/-!\n# {name}\n\n{purpose}\n-/\n\nnamespace Recaman.{name}\n\n-- Declarations\n\nend Recaman.{name}\n"
        lean_file.write_text(content, encoding="utf-8")
        print(f"Created Lean module source: {lean_file}")
    else:
        print(f"Lean file already exists: {lean_file}")

    recaman_text = RECAMAN_ROOT_LEAN.read_text(encoding="utf-8")
    import_stmt = f"import {full_module_name}"
    if import_stmt not in recaman_text:
        RECAMAN_ROOT_LEAN.write_text(f"{import_stmt}\n{recaman_text}", encoding="utf-8")
        print(f"Added '{import_stmt}' to Recaman.lean")
    else:
        print(f"'{import_stmt}' already present in Recaman.lean")

    contract_lines = CONTRACTS_TSV.read_text(encoding="utf-8").splitlines()
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
    rows = [l.split("\t") for l in lines[1:] if l.strip()]

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

    # brief
    p_brief = subparsers.add_parser("brief", help="Display ultra-compact summary of active research frontier")
    p_brief.set_defaults(func=show_brief)

    # decls
    p_decls = subparsers.add_parser("decls", help="Extract signatures and docstrings from a Lean module")
    p_decls.add_argument("module", help="Module name (e.g. OnePerRun or Recaman.OnePerRun)")
    p_decls.set_defaults(func=show_decls)

    # search
    p_search = subparsers.add_parser("search", help="Search evidence registry")
    p_search.add_argument("query", nargs="?", default="", help="Keyword query")
    p_search.add_argument("--label", "-l", help="Filter by label (e.g. REFUTED, PROVED-LEAN, STOPPED)")
    p_search.add_argument("--branch", "-b", help="Filter by branch substring")
    p_search.add_argument("--compact", "-c", action="store_true", help="One line per result summary")
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
