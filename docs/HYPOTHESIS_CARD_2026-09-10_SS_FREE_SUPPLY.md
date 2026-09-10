# Hypothesis card: SS-free supply in the no-SAAS language

- ID: `H-20260910-11`
- Created: 2026-09-10 JST
- Owner: Codex, four roles sequentially
- Status: `PROVED-LEAN`; finite SS census `COMPUTED`
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For every finite newest-first Bool word w, if mass(w)=1, moment(w)=0,
and w contains neither SS nor SAAS as contiguous subwords, must every
positive even offset be A? This would identify SS-free P2 supply in the
canonical no-SAAS language with the already proved clean class.

The no-SAAS premise is supplied on the actual standard orbit by the existing
`double_forcedAddition_extends`. Do not assume this premise for arbitrary
periodic words. The local statement should explicitly retain it.

## Paper chain / weakest new lemma

A word with n S, n+1 A and no SS can be described by n+1 A gaps: the
n−1 internal gaps have at least one A, leaving exactly two extra As to
distribute, with the two end gaps starting at zero. No SAAS excludes an
internal gap of length2. Therefore the two extra As either form one internal
triple-A gap, both lie at one end, or one lies at each end. The latter two
end patterns have nonzero first moment except the initial AAS word.
The surviving words have every even offset A, as required.

The exact language implication, not another parity wrapper, is the new
input. Combined with H-09 it would give all-lag capacity for all SS-free
P2 phases in the no-SAAS language.

## Falsifier / acceptance / stopping condition

- Enumerate all no-SS mass1 words via all allocations of the two extra As:
  n1..32 discovery and n33..256 holdout (d=2n+1). Independently sum signs
  and moments, check forbidden subwords and the even-offset condition.
- Cross-check the gap generator with ALL binary words through length15.
- Remove no-SAAS as a negative control: newest-first AS AASAS (lag7)
  is P2 and no-SS but not clean; record the exact unspaced word.
- Measure adjacent SS counts in minimum finite-history P2 windows of the
  standard10^7 prefix, keeping H-07's discovery/holdout ranges. Also count
  SAAS occurrences directly; no-SS/non-clean is an explicit failure gate.
- Acceptance: complete language proof and Lean theorem with concrete
  negative control, or a counterexample. Stop if the proof needs a hidden
  boundary assumption; do not replace the intended language by an assumed
  decomposition without proving that decomposition.

## Evidence and semantic audit

`PROVED-LEAN`: `SSFreeSupply.p2_noSS_iff_even` proves the exact word-language
claim in both directions under no-SAAS. The proof first proves that a no-SS
word has mass≥−1, then that mass0 words avoiding SAAS alternate exactly.
Induction gives: mass1 words in this language either have all even slots A
or have strictly positive moment. P2 excludes the latter. This proves the
original word premise; no unproved gap decomposition is assumed.

`PROVED-LEAN`: `CanonicalSSFreeSupply.canonical_noSAAS` derives the forbidden
word directly from the existing actual recurrence theorem, using zero-based
sign times and a finite-history bound d≤t. `canonical_noSS_iff_clean` then
establishes the equivalence on the actual standard sequence. Negative-time
values of canonicalSign are never used by this theorem.

`PROVED-LEAN`: `SSFreePeriodicSupply.periodic_SSFree_capacity` and
`short_plus_SSFree_capacity` connect this language to the already proved
all-lag capacity and full short-map extension. Arbitrary periodic words
retain the explicit no-SAAS premise on counted windows.

`COMPUTED`: `python3 experiments/issue73_20260910/ss_free_supply.py` checks
2,862,208 no-SS mass1 words through length513;64 pass P2 and no-SAAS and
all are clean. The generator agrees with all binary words through length15.
The no-SAAS negative control is newest-first ASAASAS, lag7, with S at
an even offset. It is also certified by
`SSFreeSupply.noSAAS_premise_counterexample`.

`COMPUTED`: exact SS census through10^7 steps passes no-SAAS and the
no-SS iff clean test for every supplied A. Among393,913 residual phases,
70,208 have one adjacent SS and52,350 have two. Output and compile/hash
metadata: `docs/data/issue73_20260910/orbit_ss_census.txt`.

`./scripts/check.sh`: PASS,1,410 declarations, allowed axioms only; log
`docs/data/issue73_20260910/check11_ss_free_supply.txt`.

Decision: accept the language theorem and canonical bridge. The remaining
supplied windows contain SS; this is now a proved structural distinction,
not just an empirical choice of parity origin. Counting SS alone does not
supply an injection. A next gate must control interactions of windows across
SS transitions and must not assume the desired matching.

