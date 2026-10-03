#!/usr/bin/env python3
"""Fixed weekly-audit consistency checks; no search and no new mathematics."""

import re
from pathlib import Path

ROOT = Path("/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research")
WRITER = ROOT / "docs/data/issue73_20260924/slot0200"

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

source = (ROOT / "Recaman/SS2OldestPattern.lean").read_text()
decls = re.findall(r"^(?:private )?theorem\s+([A-Za-z0-9_']+)", source, flags=re.MULTILINE)
audited = {
    "moment_ending_A_budget",
    "moment_ending_AA_ss2",
    "ss2_intervening_prefix",
}
expected_unreviewed = [
    "moment_replicate_A_nonneg",
    "p2_append_A_tail_data",
    "ss2_aas_oldest_has_prefix",
    "ss2_no_w1_oldest",
    "oldestOffset_le_length",
    "oldestOffset_split",
    "ssCount_append_replicate_A",
    "past_oldest_split",
    "oldest_cover_clock_lt",
    "past_oldest_cover_decomposition",
]
unreviewed = [name for name in decls if name not in audited]
for name, ok, detail in [
    ("h05_theorem_count_13", len(decls) == 13, str(decls)),
    ("h05_unreviewed_count_10", unreviewed == expected_unreviewed, str(unreviewed)),
]:
    print(f"{name}: {'PASS' if ok else 'FAIL'} | {detail}")
    if not ok:
        failed.append(name)

packet = (WRITER / "candidate_packet.md").read_text()
append = (WRITER / "weekly_report_append_draft.md").read_text()
handoff = (WRITER / "handoff_append_draft.md").read_text()
writer_checks = {
    "writer_h05_13_and_10": "全13宣言中、残る10宣言" in packet,
    "writer_p15_failed_run": all(
        "exit130" in text and "stdout空" in text for text in (packet, append, handoff)
    ),
    "writer_reopen_unsatisfied": all("再開条件" in text and "未充足" in text for text in (packet, append, handoff)),
    "writer_delta_not_approved_math": all("承認済み新数学ではない" in text for text in (packet, append, handoff)),
    "writer_e240_label": "E-240は`PROVED-LEAN`" in packet,
    "writer_e345_label": "E-345はSS>=3 true-oldest削除反例を含む`COMPUTED`" in packet,
    "writer_no_finite_boundary": "有限な境界" not in packet + append + handoff,
    "writer_no_minimum_counterexample": "最小の新反例" not in packet + append + handoff,
}
for name, ok in writer_checks.items():
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        failed.append(name)

print(f"checked={len(checks) + 2 + len(writer_checks)} failed={len(failed)}")
raise SystemExit(1 if failed else 0)
