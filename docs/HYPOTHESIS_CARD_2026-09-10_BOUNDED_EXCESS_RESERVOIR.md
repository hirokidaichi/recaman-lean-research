# Hypothesis card: S reservoir for bounded-excess supplies

- ID: `H-20260910-03`
- Owner: Codex; proposer, falsifier, formalizer, auditor sequentially
- Created: 2026-09-10 JST
- Status: `PROVED-LEAN` for density (E-098); fixed-charge extension `REFUTED` (E-099)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For every m≥3, R≥0 and newest-first Boolean word w, suppose P2(w), the
first m signs are A, and length(w)≤4m−1+4R. Must the block of offsets
m+1,...,2m−1 contain at most2R A signs (hence at least m−1−2R S signs)?
No exact-run or minimum-lag assumption. The block is inside w by E-090.

This is a density claim, not a claim of a contiguous S block. In particular
the former sharp charge at offset m+2 may fail for any positive excess.

## Dependency chain / proposed argument

P2 parity writes d=4m−1+4s with0≤s≤R. In the tail after the leading m As,
q=m+2s As have position deficit
q(2n−q+1)−2positions = 2m(2s+1)+4s².
For any split u++v this deficit is at least
2 ones(u)(length(v)−ones(v)), by the maximal-position bound in both pieces.
Take length(u)=m−1 and b=ones(u); then length(v)=2m+4s and
length(v)−ones(v)=m+2s+b. If b≥2s+1 the lower bound exceeds the budget.
Therefore b≤2s≤2R. The weakest new lemma is this two-piece deficit bound.

Sharpness candidate, R≥1 and m=6R²:
`A^m S^(m−2R−1) A^(2R) S^(m+4R) A^m`.
It should have P2, length4m+4R−1, and exactly2R As in the middle block.

Negative-control candidate, every m≥3:
`A^m S A S^(m−2) A S^(m+2) A^m`.
It should have P2, length4m+3, but offset m+2 is A. Thus simply reusing
the former fixed protected S charge would fail even at excess4.

## Frozen falsifier / acceptance / stopping condition

- Enumerate all P2 words of lengths11,15,19 discovery;23,27 holdout.
- For every leading m≥3 compute exact s and the A count in the block.
- These finite word ranges were already used for H-02 with a different
  statistic; they are a held-out range for this declared test, not new blind data.
- Sharpness family R=1..8 discovery,9..64 holdout; negative control
  m=3..16 discovery,17..128 holdout. Check P2 directly from signed sums.
- Acceptance: universal paper/Lean proof, with the negative control recorded.
- Stop on any word with more than2s middle As or failed family member.
- This card does not assert a global periodic capacity theorem.

## Evidence

`PROVED-LEAN`: `Recaman/BoundedExcessReservoir.lean` proves the two-piece
deficit inequality, the word and stream density bounds, and the fixed-charge
counterfamily for every m≥3. An ordinary `decide` certificate attains the
2R bound at R1,m6,d27. Seven declarations are included in Audit; full
`./scripts/check.sh` passed with1,286 declarations. Exact log:
`docs/data/issue73_20260910/check03_reservoir.txt`.

`COMPUTED`: command
`python3 -u experiments/issue73_20260910/bounded_excess_reservoir.py`, output
`docs/data/issue73_20260910/bounded_excess_reservoir.txt` records source and
script/generator hashes. For d11,15,19,23,27, eligible words were
3,30,325,3712,44322, with zero violations. R1..64 sharpness words and
m3..128 fixed-charge counterexamples all passed exact sign/moment checks.
These are finite computations, not a proof of the parameter families.

`PROVED-PAPER`: the all-R≥1 sharpness family has m=6R², middle lengthm−1
and b=2R As. All As in each of its middle/final pieces occur at the end,
so the tail deficit is exactly2b(m+4R)=4Rm+16R². This equals the required
P2 deficit2m(2R+1)+4R² because m=6R². Its total length is4m+4R−1 and
A count2m+2R, so mass1; the displayed deficit identity then gives moment0.
The middle has exactly2R As. Nonnegative block lengths follow fromR≥1.
This universal sharpness argument is recorded but only its R1 instance is
Lean-certified here; do not describe the entire family as PROVED-LEAN.

`REFUTED`: the claim that offset m+2 must be S for excess at most4 is
false for every m≥3, by `fixed_charge_failure`. This is stronger than a
small-word counterexample and forbids repairing the fixed position just
by increasing the run-length threshold.

Audit of scope: first m signs need not be the maximal A run, and the P2
lag need not be minimal. The stream theorem proves that the block exists
inside the supply window rather than assuming it. The density conclusion
does not assert a contiguous S block or a canonical S to charge.

Decision: accept the density input, stop the old fixed-offset extension,
and separately test disjoint reservoirs plus unused-S counting (H-04).
