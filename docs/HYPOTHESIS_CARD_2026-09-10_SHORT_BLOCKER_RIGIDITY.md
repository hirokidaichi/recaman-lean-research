# Hypothesis card: sharp short-blocker rigidity

- ID: `H-20260910-15`
- Created: 2026-09-10 JST
- Owner: Codex, four roles sequentially
- Status: `PROVED-LEAN` (E-114)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For any nonempty Bool word w of length d and integer clock n>0 satisfying
the actual collision equation `moment(w)=n*(mass(w)−1)`, must
`mass(w)≠1` imply `4n≤d(d+4)`?
Consequently, for canonical u+d=t and `a(t)=a(u)+t+1`, the strict bound
`d(d+4)<4(t+1)` should force P2(t,d).

The word bound should be sharp for every r≥1 at
`w=S^(r−1) A^(r+1)`, d=2r, mass2, moment=n=r(r+2).
This is sharpness in the sign-word collision model; it is NOT a claim
that this all-r family is reachable canonically. At r1 the actual initial
AA window realizes equality, with the historical candidate0.

## Dependency chain / why this is useful

The existing fixed-mass minimum moment bound and its maximum counterpart
give `4M ≤ d²+2dm−m²+2m`. For m≥2, subtracting this from
`(m−1)d(d+4)` factors as `(m−2)(d²+2d+m)≥0`. For m≤0, the minimum moment
bound gives the corresponding negative-M estimate. Integer separation then
forces m1 below the stated clock threshold, and the collision equation
forces M0. E-111 connects the collision equation to actual recurrence.

This is a quantitative input for the fixed-lag/eventual-periodic reduction,
not a proof that all actual blockers have short lag or that E-070 holds.

## Falsifier / acceptance / stop

- All binary words d1..13 discovery,d14..19 holdout. For m≠1 and an integer
  n=M/(m−1) with n≥d+1, check4n≤d(d+4). This permits arbitrary sign history.
- Equality family r1..32 discovery,r33..256 holdout; verify exact moment,
  collision clock, and zero slack.
- Check the canonical prefix through2,000 for the actual collision bound,
  including a0, positive blockers, t5's non-P2 blocker, and both parity cases.
- Acceptance: the universal word inequality, canonical corollary, and the
  correctly scoped all-r equality family in Lean. Stop on any failed sign,
  clock, or history boundary; do not silently assume a fixed-mass bound.

## Evidence

- `COMPUTED`: `python3 experiments/issue73_20260910/short_blocker_rigidity.py > docs/data/issue73_20260910/short_blocker_rigidity.txt` passed every declared range. Canonical through2,000:559 collision pairs,168 non-P2 pairs,126 strict-rigid pairs.
- `PROVED-LEAN`: `Recaman/ShortBlockerRigidity.lean` proves both universal mass cases, the canonical bridge, and the all-r word equality family. The initial AA canonical window certifies that strict inequality is necessary.
- `./scripts/check.sh > docs/data/issue73_20260910/check15_short_blocker_rigidity.txt 2>&1`: PASS,1,452 audited declarations.
- Auditor: no finite-history upper bound or periodicity was assumed in the word theorem. Family sharpness is not asserted to be canonically reachable beyond the explicitly checked r1 case.
- Remaining uncertainty: long actual blockers need not be P2; this theorem does not make them short. Next decision: derive a uniform lag bound from positive periodic drift before invoking this rigidity theorem.
