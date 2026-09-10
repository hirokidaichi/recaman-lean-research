# Hypothesis card: P2 leading A-run cannot attain ssCount+2

- ID: `H-20260910-38`
- Created: 2026-09-10 22:30 JST
- Status: `PROVED-LEAN` (E-169). For `ssCount ≥ 1`, leading A-run `≤ ssCount+1`. SS=0 still allows AAS.
- Research branch: issue #73, after E-166/E-167 killed the SS=2 and SS=3 equality cases

## Exact statement

Let `w` satisfy `P2 w` and contain an S. Write `w` as
`gapWord a (gs ++ [v])`. Then it is not possible that
`a = ssCount w + 2`. Equivalently, the leading A-run satisfies
`a ≤ ssCount w + 1`.

Mass already gives `a + v + extraAs gs = ssCount w + 2` (E-168), so
the remaining case is `v = 0` and `extraAs gs = 0` with
`zeroGaps gs = a - 2`. The encoded word is `A^{n+2}` followed by an
`{0,1}`-gap list with exactly `n` internal zeros and a trailing S,
where `n = ssCount w`.

Proposed Lean:

```
theorem p2_leading_le_ssCount_succ (k : Nat) (rest : List Bool) (n : Nat)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = n) :
    k ≤ n + 1
```

## Why it would matter

- Frontier obligation discharged: E-168's equality remainder for every
  SS, not just 2 and 3.
- Stronger than E-126's NoSAAS bound `a ≤ SS+2` because NoSAAS is
  dropped and the equality is killed.
- Smallest useful consequence: SS=4 cannot start AAAAAA; orbit E-163
  already has a≤4.

## Provenance and dependencies

- `every_P2_exact`, `a4_family_not_P2`, `a5_family_not_P2`,
  `two_gapWeight_replicate_one`, `gapWord_moment`.
- Unverified: the closed form
  `2·moment = -2(m²-1) - Σ_j (4(m-j)-2) p_j`
  for `m = n+1` one-run lengths `p_j`. All coefficients are ≥2 for
  `m≥2`, hence `2·moment ≤ -6`.

## Falsification plan

- Boundary: all-zero word `A^{n+2} S^{n+1}` has
  `2·moment = -2n(n+2) < 0` for n≥1.
- Insert ones in each slot; moment should decrease.
- Discovery: n=1..8, one-run lengths ≤5.
- Holdout: n=9..12, or a Lean proof.
- One repair: none. If a P2 equality word appears, stop.
- Stop: one P2 example with `a = SS+2`, or Lean.

## Evidence log

| Date | Label | Result |
|---|---|---|
| 2026-09-10 | `PROVED-LEAN` | n=2 is E-160; n=3 is E-164 |
| 2026-09-10 | `COMPUTED` | `eq_family_moment.py`: 33887 words, formula 0 fail, P2 0 |
| 2026-09-10 | `PROVED-LEAN` | E-169 `p2_leading_le_ssCount_succ` |

## Decision

- Continue / formalize / refute / stop: proved. Do not try to kill
  `a = SS+1`; SS=2 companions with a=3 are real.
- Reopen only if: the intended claim included SS=0, which is false
  because AAS is P2.
