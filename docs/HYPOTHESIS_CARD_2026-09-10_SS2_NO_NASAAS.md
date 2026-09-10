# Hypothesis card: SS=2 P2 cannot start AAAA, even without NoSAAS

- ID: `H-20260910-37`
- Created: 2026-09-10 22:25 JST
- Status: `PROVED-LEAN` (E-166). SS=3 analogue `PROVED-LEAN` (E-167). General leading bound `k ≤ SS+2` is E-168.
- Research branch: issue #73, after E-161 which still assumed NoSAAS

## Exact statement

There is no word `w : List Bool` with `P2 w` and `ssCount w = 2` whose
newest-first leading A-run has length `k ≥ 4`. Minimality and NoSAAS
are not hypotheses.

Proposed Lean:

```
theorem ss2_leading_run_lt_four (k : Nat) (rest : List Bool)
    (hk : 4 ≤ k)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = 2) : False
```

The same mass identity gives `k ≤ ssCount w + 2` for every P2 word that
contains an S, and the SS=3 equality case `k = 5` is the a5 family,
already not P2 (E-164).

## Why it would matter

- Frontier obligation discharged: the remaining hole of E-161
  ("NoSAAS-free AAAA SS=2").
- Stronger than E-161 because NoSAAS is dropped. SAAS (internal gap 2)
  costs `extraAs ≥ 1`, so it cannot restore mass 1 when `a ≥ 4` and
  `ssCount = 2`.
- Smallest useful consequence: SS=2 P2 leading runs are in `{0,1,3}`
  after combining with E-132 (no leading AAS). Matches orbit E-158
  with no extra hypothesis.

## Provenance and dependencies

- Definitions used: `P2`, `ssCount`, `gapWord`, `extraAs`, `a4Gaps`.
- Lean theorems used: `word_gap_representation`, `exact_word_budget`,
  `leading_run_eq_gap_a`, `two_zero_gaps_form`, `a4_family_not_P2`.
- Unverified mathematical assumptions: none once `every_P2_exact` is
  proved. `every_P2_budget` currently threads NoSAAS only for the
  enlarged-gap inequality, which this statement does not need.
- Literature source or analogy: E-126 exact form `a+v+extraAs = SS+2`.

## Falsification plan

- Small and boundary cases: all-zero a4 word `AAAASSS`; a4 family
  with ones in each slot; SAAS words `AAAASAAS…`.
- Adversarial or weakened-history model: free binary words, no
  Recamán reachability.
- Discovery range: all newest-first words of odd length 7..19 starting
  AAAA with ssCount=2.
- Frozen holdout range: length 23, and the a4 family with
  `p,q,r ≤ 40`.
- Maximum one permitted repair: if a SAAS counterexample appears,
  stop; do not add NoSAAS back.
- Stop condition: a single P2 SS=2 word with leading run ≥4, or Lean
  proof of the statement above.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-10 | `COMPUTED` | orbit 10^7 (E-158) | a≥4 count 0 |
| 2026-09-10 | `PROVED-LEAN` | E-160 / E-161 | NoSAAS case already dead |
| 2026-09-10 | `COMPUTED` | `python3 experiments/issue73_20260910/two_ss/ss2_aaaa_nosaas.py` | AAAASSS moment=-8; a4 family pqr≤20 is 0; free words length≤19 starting AAAA with ssCount=2 and P2: 0 |
| 2026-09-10 | `PROVED-LEAN` | E-166 / E-167 / E-168 | NoSAAS dropped |

## Semantic audit

- Informal statement implies formal statement: yes; the Lean drops
  minimality, which makes it stronger.
- Formal statement implies intended consequence: SS=2 P2 cannot begin
  AAAA, with or without SAAS.
- Counterfactual examples that should make the statement false:
  `gapWord 4 [2,0]` has mass 1 but extraAs=1 so ssCount≠2; AAS is P2
  but ssCount=0 and leading run 2.
- Could the theorem be proved from weaker or vacuous assumptions?:
  mass=1 plus ssCount=2 already forces a≤4; moment=0 is used only to
  kill the a=4 extraAs=0 family.
- Are reachability, freshness, time order, or actual-orbit provenance
  accidentally omitted?: yes, deliberately. The claim is about free
  words.

## Decision

- Continue / formalize / refute / stop: proved. Do not reopen NoSAAS
  as a repair. Named S-charges stay closed.
- Reason: `exact_word_budget` never used NoSAAS; the a=4 remainder is
  the extraAs=0 family already killed by E-160.
- Reopen only if: the intended claim was minimality-only, which this
  theorem does not use.
