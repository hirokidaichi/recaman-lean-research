# Hypothesis card: all-lag capacity when subtraction phases have one parity

- ID: `H-20260910-08`
- Owner: Codex, four roles sequentially
- Created: 2026-09-10 JST
- Status: `PROVED-LEAN` (E-104)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For every periodic sign stream with e(2n+1)=A for all integers n, does
the FULL set of P2-supplied A phases have size at most the number of S
phases? There is no lag bound. The even subsequence f(n)=e(2n) is arbitrary.
This includes words assembled from SA and SAAA, but also longer odd A runs.
It excludes parity changes caused by SS or even-length A runs; no theorem
that the standard infinite orbit has fixed subtraction parity is proposed.

## Exact proposed classification and charge

An even current phase never has P2. At t=2n+1, P2 holds exactly when some
k≥0 satisfies d=8k+3 and the even-phase indices in[n−4k−1,n] contain
exactly one A, at n−k. All others in that interval are S.
The proposed charge is the S at original time
`q=t−4k−3=2(n−2k−1)`.

The mass equation fixes the number of exceptional As to one; the moment
equation fixes its position. If two charges agree and k<ell, the exceptional
A of the smaller witness lies in the larger witness's required S region.
Thus the charge should be injective on the integer line, and after periodic
lifting modulo the period. This is an all-lag structural subclass, not a
new table of lag types and not a proof of E-070 without the parity premise.

## Falsifier and acceptance / stopping condition

- Search found no existing same-parity P2 capacity theorem in the portfolio
  or hypothesis cards. Generic reuse-interval laminarity is not assumed.
- Exhaustive even-subsequence words of periods1..10 discovery,11..14 holdout.
- For every A phase compute all P2 signatures, including lags longer than
  a period, with an exact algebraic bound for positive total sign sum.
  Here total sign sum=2*(number of even As)≥0. In the zero case the word
  alternates exactly and must be checked separately at unbounded-lag level.
- Compare every hit with the exact classification, verify charge S and
  injectivity, and try both cycle origins. Include all A, pure alternation,
  one isolated even A, adjacent even As, and sparse/dense defects.
- Test a negative control that drops the fixed-odd-A premise; it should
  invalidate the classification or charge, not necessarily the full E-070 bound.
- Freeze script parameters before execution. Stop on any valid counterexample.
- Acceptance: complete all-lag paper proof and Lean classification/capacity,
  or an explicit countermodel. Computation alone is insufficient.

## Evidence

`PROVED-LEAN`: `Recaman/ParitySupply.lean` proves both directions of
`odd_P2_iff`, impossibility at even current phases, uniqueness of the P2
lag, and the line charge injection. `Recaman/ParityPeriodicSupply.lean`
proves the full all-lag periodic capacity with no lag bound, long-run
condition, or assumed injection. The period need not be even: lifting
still works, and the odd-period case is vacuous if all signs become A.
The list U may contain every supplied phase, not merely supplied A phases,
because P2 itself forces an odd current phase under the parity premise.

`COMPUTED`: command
`python3 -u experiments/issue73_20260910/parity_supply_capacity.py`, exact
log `docs/data/issue73_20260910/parity_supply_capacity.txt` with the frozen
closed-form solver hash. All even-subsequence words through period14
(original period28) pass; the holdout period14 includes16,384 words,
61,180 supplied phases across words,14 hits with lag>28, maximum lag35,
and843 equality words. Direct lag enumeration independently checks every
word through compressed period6, and the zero-sum alternating case is
checked separately. Every positive-sum signature is algebraically complete,
not a fixed-lag truncation.

`REFUTED` control is also Lean-certified: periodic `SSSAAAA`, phase5,
P2 lag11 has the proposed charge phase5, which is A. Thus this is not a
proof of unrestricted E-070. The trajectory census motivates the model
but does not establish its global parity premise for the standard orbit.

Audit: `./scripts/check.sh` passed; exact log
`docs/data/issue73_20260910/check08_parity_capacity.txt`. Both new modules
are root-imported and all their theorems are included in Audit.

Decision: accept this complete all-lag structural subclass. Next test
whether the parity premise can be confined to each supply window, and
whether those local charges coexist with the already proved short map.
This is a new bounded question; do not silently remove the global premise
from the theorem just proved.

## Paper chain after the falsifier, before Lean implementation

The exhaustive protocol passed through compressed period14 (original
period28), including lags35>28 and both origins. Dropping parity fails for
`SSSAAAA`, phase5, lag11, where the proposed charge is the A phase5.

For a newest-first compressed word v, insert a fixed A after each letter:
`pairs(v)=[v0,A,v1,A,...]`. Its mass is2ones(v), and its moment is
4positions(v)−2ones(v)+length(v). An even-current odd window is
`A::pairs(v)`, with moment4positions(v)+length(v)+1>0, so cannot be P2.
An odd-current odd window is `pairs(v)++[b]`. If b=A, the mass condition
forces ones(v)=0 and the moment is positive. Therefore b=S, ones(v)=1,
and length(v)+3=4positions(v). The unique A position j=k+1 then gives
length(v)=4k+1 and total lag8k+3. This proves the full classification.

The selected even S has compressed index n−2k−1, inside the required S
interval and different from the unique A index n−k. Equal selected positions
for two witnesses with k<ell put the earlier exceptional A strictly before
the later exceptional A but inside its required S interval, a contradiction.
Periodic lifting completes the injection. This is the weakest new mathematical
input; it must be formalized before registering an all-lag theorem.
