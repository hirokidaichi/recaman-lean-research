# Hypothesis card: SS=2 min P2 cannot start AAAA

- ID: `H-20260910-36`
- Created: 2026-09-10 21:45 JST
- Status: NoSAAS case `PROVED-LEAN` (E-161). NoSAAS dropped in E-166: any P2 with ssCount=2 has leading run <4. Combined with E-132, remaining runs are 0, 1, 3. Matches orbit E-158.
- Research branch: issue #73, after E-132 forbade leading AAS

## Exact statement

There is no word w with P2(w), ssCount(w)=2, minimum (no proper prefix
P2), and leading A-run ≥4.

E-132 already forbids leading run 2 (AAS is P2). The remaining values
on the canonical 10^7 prefix are 0, 1, and 3 only.

## Evidence log

| Date | Label | Result |
|---|---|---|
| 2026-09-10 | `COMPUTED` | canonical 10^7 a≥4 is 0 |
| 2026-09-10 | `COMPUTED` | abstract AAAA min SS=2 lengths 15..31 ≡3 mod 4 is 0 |
| 2026-09-10 | `PROVED-LEAN` | NoSAAS SS=2 P2 cannot have leading run ≥5 (E-159) |
| 2026-09-10 | `COMPUTED` | a=4 NoSAAS shape (two zero-gaps, rest ones, v=0) has no P2 for parameters <25 |

## Falsification

- Canonical 10^7: a≥4 count 0 (E-158)
- Abstract min SS=2 words of length 15,19,23,27,31 starting AAAA: 0
- Holdout: longer lengths, or a Lean proof from leading_run_bound plus
  ssCount=2
- Stop if a single min P2 SS=2 word starting AAAA is found

## Proof sketch (not yet Lean)

Under NoSAAS, E-126 gives `a+v+2B≤SS+2=4`. For `a=4` this forces `v=0`
and `B=0`, hence extraAs=0 and zeroGaps=2. The word is `AAAA` followed
by a `{0,1}`-gap encoding with exactly two zero gaps and trailing S.
Mass 1 holds; moment 0 is the remaining obstruction. Isolated a=0
windows are all NoSAAS (E-139). Do not assume NoSAAS for a general
counterexample search.

## Decision

Under NoSAAS the statement is proved (E-161). Do not drop NoSAAS without
a new obstruction. Named S-charges stay closed.
