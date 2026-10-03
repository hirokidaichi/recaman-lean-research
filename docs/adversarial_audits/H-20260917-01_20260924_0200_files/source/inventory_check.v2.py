#!/usr/bin/env python3
"""Fixed weekly-audit consistency checks; no search and no new mathematics."""

from pathlib import Path

ROOT = Path("/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research")

checks = {
    "weekly_h01_proved": (ROOT / "docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md", "E-360 の最終Q"),
    "weekly_h02_incomplete": (ROOT / "docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md", "H-20260920-02、H-20260920-03、H-20260920-05"),
    "weekly_h04_scope": (ROOT / "docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md", "非最小lag15 donorへの延長だけ"),
    "weekly_h05_unreviewed": (ROOT / "docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md", "紙§3-5"),
    "weekly_no_general_lag": (ROOT / "docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md", "一般lagルートを延長しない"),
    "h02_status": (ROOT / "docs/HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md", "Status: `CONJECTURED`"),
    "h03_status": (ROOT / "docs/HYPOTHESIS_CARD_2026-09-20_SHORT_PREFIX_REDUCTION.md", "Status: `CONJECTURED`"),
    "h04_status": (ROOT / "docs/HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md", "Status: `REFUTED`"),
    "h05_status": (ROOT / "docs/HYPOTHESIS_CARD_2026-09-20_MINIMAL_DONOR_PATTERNS.md", "Status: `CONJECTURED`"),
    "e360_registry": (ROOT / "docs/EVIDENCE_REGISTRY.tsv", "E-360\tPROVED-LEAN\tshort-tight-donor-avoidance"),
    # The certificate is PROVED-LEAN; what it refutes is the pure-AAS/lag-3-forcing route.
    "e240_certificate": (ROOT / "docs/EVIDENCE_REGISTRY.tsv", "E-240\tPROVED-LEAN"),
    "e345_computed": (ROOT / "docs/EVIDENCE_REGISTRY.tsv", "E-345\tCOMPUTED"),
    "e351_proved": (ROOT / "docs/EVIDENCE_REGISTRY.tsv", "E-351\tPROVED-LEAN"),
    "h05_local_1": (ROOT / "Recaman/SS2OldestPattern.lean", "theorem moment_ending_A_budget"),
    "h05_local_2": (ROOT / "Recaman/SS2OldestPattern.lean", "theorem moment_ending_AA_ss2"),
    "h05_local_3": (ROOT / "Recaman/SS2OldestPattern.lean", "theorem ss2_intervening_prefix"),
    "h05_downstream": (ROOT / "Recaman/SS2OldestPattern.lean", "theorem past_oldest_cover_decomposition"),
    "h03_downstream_avoid": (ROOT / "Recaman/ShortTightDonorAvoidance.lean", "theorem short_p2_tight_avoids_ss2_window"),
    "h03_downstream_delete": (ROOT / "Recaman/ShortTightDonorAvoidance.lean", "theorem short_p2_ss2_deletion"),
}

failed = []
for name, (path, needle) in checks.items():
    ok = needle in path.read_text()
    print(f"{name}: {'PASS' if ok else 'FAIL'} | {path.relative_to(ROOT)} | {needle}")
    if not ok:
        failed.append(name)

print(f"checked={len(checks)} failed={len(failed)}")
raise SystemExit(1 if failed else 0)
