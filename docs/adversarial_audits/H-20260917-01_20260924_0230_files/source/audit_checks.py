#!/usr/bin/env python3
"""Read-only fixed checks for the 2026-09-24 02:30 closure candidate."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

REPO = Path("/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research")
SLOT = REPO / "docs/data/issue73_20260924/slot0230"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sign(c: str) -> int:
    return 1 if c == "A" else -1


def mass(w: str) -> int:
    return sum(sign(c) for c in w)


def moment(w: str) -> int:
    return sum(i * sign(c) for i, c in enumerate(w, 1))


def p2(w: str) -> bool:
    return mass(w) == 1 and moment(w) == 0


def ss_count(w: str) -> int:
    return sum(w[i : i + 2] == "SS" for i in range(len(w) - 1))


def bit(cycle: str, t: int) -> str:
    return cycle[t % len(cycle)]


def past(cycle: str, t: int, d: int) -> str:
    return "".join(bit(cycle, t - i) for i in range(1, d + 1))


def neighborhood(cycle: str, members: list[int], lags: dict[int, int]) -> list[int]:
    p = len(cycle)
    return sorted(
        {
            (b - i) % p
            for b in members
            for i in range(1, lags[b] + 1)
            if bit(cycle, b - i) == "S"
        }
    )


expected_originals = {
    "original_weekly_report_at_freeze.md": "00b149ea96eafdddcbfbe4a4e09031ca0779ab1ffdfd93fa941d02bb57dfd9d2",
    "original_main_card_at_freeze.md": "7f73cc1ec105e699b571e5f0df78d5ddcef670dc304f44a9d5df9efee078b479",
    "original_handoff_at_freeze.md": "1846cf280c8f911a5e5358f6ef24e23134dd4b7cd3b68bae3cedf245c939d13c",
}
for name, expected in expected_originals.items():
    assert sha256(SLOT / name) == expected, name

weekly = (SLOT / "proposed_weekly_report_full.md").read_text()
card = (SLOT / "proposed_main_card_full.md").read_text()
handoff = (SLOT / "proposed_handoff_full.md").read_text()
joined = "\n".join((weekly, card, handoff))

required = [
    "08c08565c743f39350c9b959e1df7d30aa1cae5d",
    "E-360",
    "一般p",
    "short-lag",
    "all-short U",
    "OwnerFamily",
    "4フィールド",
    "E-351",
    "H-02/H-03/H-05",
    "CONJECTURED",
    "downstream 2本",
    "残る10宣言",
    "紙§3-5",
    "周期接続",
    "p32/33",
    "lag19 shards",
    "非最小lag15",
    "REFUTED",
    "STOPPED",
    "最小lag15",
    "一般lag",
    "完全all-lag U",
    "一般Gate T6",
    "実軌道",
    "delta=r-kx",
    "再開条件",
    "未充足",
    "量化子",
    "非空例",
    "入口監査",
    "新しい数学",
    "vacuity/lint/check",
    "未監査10宣言の認証",
]
missing = [term for term in required if term not in joined]
assert not missing, missing

for forbidden in [
    "一般lagルート全体を `STOPPED`",
    "最小lag15を `REFUTED`",
    "automation停止済み",
    "全process終了済み",
]:
    assert forbidden not in joined, forbidden

# Independent fixed recomputation of every premise used for the H-04 literal.
cycle = "SAAASSSASASASAAA"
u0 = 15
donor = past(cycle, u0, 15)
B = [3]
N = neighborhood(cycle, B, {3: 3})
proper = [d for d in range(1, 15) if p2(past(cycle, u0, d))]
oldest_offset = max(i for i, c in enumerate(donor, 1) if c == "S")
true_phase = (u0 - oldest_offset) % len(cycle)
fixed11_phase = (u0 - 11) % len(cycle)
assert donor == "AASASASASSSAAAS"
assert mass(cycle) == 2 and bit(cycle, u0) == "A"
assert p2(donor) and ss_count(donor) == 2 and proper == [3]
assert past(cycle, 3, 3) == "AAS" and p2(past(cycle, 3, 3))
assert not any(p2(past(cycle, 3, d)) for d in range(1, 3))
assert len(set(B)) == len(B) and all(b < len(cycle) for b in B)
assert all(bit(cycle, b) == "A" for b in B) and u0 not in B
assert N == [0] and len(N) == len(B)
assert oldest_offset == 15 and true_phase == 0 and true_phase in N
assert fixed11_phase == 4 and fixed11_phase not in N
deleted = [s for s in N if s != true_phase]
assert deleted == [] and not (len(B) <= len(deleted))

out = {
    "candidate_sha256": {
        name: sha256(SLOT / name)
        for name in [
            "proposed_weekly_report_full.md",
            "proposed_main_card_full.md",
            "proposed_handoff_full.md",
        ]
    },
    "required_terms": len(required),
    "missing_terms": missing,
    "H04": {
        "cycle": cycle,
        "period_mass": mass(cycle),
        "u0": u0,
        "donor": donor,
        "donor_current": bit(cycle, u0),
        "donor_mass": mass(donor),
        "donor_moment": moment(donor),
        "donor_ss": ss_count(donor),
        "proper_p2_prefixes": proper,
        "B": B,
        "B_nodup": len(set(B)) == len(B),
        "B_in_phase_range": all(b < len(cycle) for b in B),
        "B_current": [bit(cycle, b) for b in B],
        "B_window": past(cycle, 3, 3),
        "B_minimal": not any(p2(past(cycle, 3, d)) for d in range(1, 3)),
        "donor_outside_B": u0 not in B,
        "N": N,
        "tight": len(N) == len(B),
        "true_oldest_offset": oldest_offset,
        "true_oldest_phase": true_phase,
        "oldest_in_N": true_phase in N,
        "deleted_N": deleted,
        "deletion_hall": len(B) <= len(deleted),
        "fixed_offset11_phase": fixed11_phase,
        "fixed_offset11_in_N": fixed11_phase in N,
    },
}
print(json.dumps(out, indent=2, sort_keys=True))
