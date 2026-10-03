# Subagent probes of 2026-10-03 (H-20261003-01)

Scripts written by the session's subagents and cited in the hypothesis card
`docs/HYPOTHESIS_CARD_2026-10-03_GENERAL_LAG_CLOSURE.md`. Kept for reproducibility; their numerical claims are
recorded in the card with the note whether the parent session re-checked them. Run them from a scratch
directory (several scripts cache minimal words as `mw_L.pkl` in the current directory).

| dir | card item | what |
|---|---|---|
| `level/` | 3, 4 | `lsearch.py Lv [--level|--rel=le0|--newest|--owners=K]`: matching-closure search with level / UP-FREE / newest restrictions |
| `claimn/` | 10 | `nsearch.cpp` (Claim N, case a = 0, owner lag independent of v), `count_check.py` (Theorem R counting over all (v, own v)) |
| `case2/` | 13 | `gr_check.py` (generalized Theorem R, same as R'), `aw_check.py` (closures with only AAS/w1 members decompose) |
| `claimp/` | 15 | `leftend3.py min Lmax H [--show]` (local test of Lemma OS at the oldest S), `relax.py` (arbitrary-P2 / area-inequality relaxations) |
| `os/` | 16 | `auto.py LMAX KMAX` (left-to-right automaton of open windows; co-reachable states), `show.py`, `auto_rel.py` (area relaxations), `macro.py`, `close1.py` (OS => classification block walk) |

The parent's own probes are one directory up (`matching_closure_search*.cpp`, `private_member_motif_check.py`,
`peak_search_top.py`, `tight_cover_census.cpp`, `audit_lagmax19_shards.py`).
