# Hypothesis card: d-independent selector extending φ7 ∪ φ11 ∪ φ15

- ID: `H-20260908-06`
- Owner: root
- Created: 2026-09-09
- Status: this selector family `STOPPED`; E-070 still `CONJECTURED`; E-080/E-086 stand
- Research branch: issue #73, remaining edge of H-20260908-01 / H-20260908-04
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`

## One bounded question

Is there a closed-form rule F, depending only on the S-offset set of a
minimal P2 window (or only on the U7/φ11-blocked subset of that set), such
that F reproduces the three φ7 charges and is a blocked pairwise-injective
assignment on the 17 min-lag-11 types and the 155 min-lag-15 types?

Declared family, one shot, no repair:

```text
raw S-set: min, max, median, min{x≥3}, closest to d/2
blocked subset: min, max, median, closest to d/2
```

A surviving F would be a d-independent local obstruction, not another
per-lag table. Failure of the family stops lag-by-lag. It does not refute
E-070, E-080, or E-086.

## Why it would matter

- Continuation gate of H-20260908-01/04: the type-to-offset method must be
  visibly uniform in d ≡ 3 (mod 4), or the class stops.
- Stronger than E-086 if F works for all such d. Weaker than E-070 if F is
  only checked at d≤15.

## Falsification plan

- Boundary: F must fit φ7 on `{3}`, `{1,6,7}`, `{2,5,7}`.
- Weakened: blocked-set selectors need not equal the CSP table, only land
  in the blocked set and be pairwise Z-injective at δ=j−i.
- Discovery: exact finite type lists already frozen (17 and 155).
- No holdout period census. No lag-19 table.
- One repair: none. The lag-11 gap-class repair was consumed as E-085.
- Stop if every declared selector fails φ7 or has a Z-open pair at lag-15.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-09 | `COMPUTED` | `python3 experiments/issue73_20260908/uniform_selector.py` | φ7: no raw-S selector fits all 3 types. Unique blocked: 0/17 and 1/155. lag-11 max/median blocked have 0 open pairs; all 4 blocked selectors have 8–14 open pairs at lag-15 |

## Decision

- Continue / formalize / refute / stop: stop the lag-by-lag type-to-offset
  class. E-080 remains `PROVED-LEAN`. E-086 remains `PROVED-PAPER`. Do not
  `decide` the 155-row table. Do not run lag-19. Do not extend p.
- Reopen only if a d-independent local obstruction is injective on the 155
  min-lag-15 types without a new per-lag table, or a closed-form potential
  raises F on `SSAAAAAASSS` and drops by at most 1 on S from `AAASAASSSSS`.
