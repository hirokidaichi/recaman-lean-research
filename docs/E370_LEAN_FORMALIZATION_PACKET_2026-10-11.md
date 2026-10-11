# E-370 Lean formalization work packet (2026-10-11)

Status: **PROVED-PAPER only; Lean source, compilation, statement audit, and CI are outstanding.** This packet is an implementation boundary, not a new evidence-registry row. Base: `167d07df424b85217010935934bd583d8995af23`.

## Bounded question

Can the `NoSAAS` / single-SSS collision-pair capacity statement from [the October 6 research plan](RESEARCH_PLAN_2026-10-06_SS2_REMAINING.md) be derived in Lean from actual periodic sign streams and actual current-A minimal P2 windows, for **every positive period and every positive lag**, with neither positive period mass nor an assumed Hall/owner condition?

Acceptance: one substantive `Recaman/*.lean` module states the complete restricted two-excluded-phase result and proves it, then `python3 scripts/harness_gate.py --lint-module ...`, `./scripts/check.sh`, statement audit, independent controls and full CI pass. A first internal-SSS lemma is an intermediate result and must not be registered or described as E-370 complete. Stop if the paper classification requires a missing theorem equivalent to the target capacity claim; preserve that obligation explicitly.

## Exact first lemma and source interfaces

Use `import Recaman.SS2LowSSTight` and, for counting, `Recaman.OnePerRun.ssCount_append` (available transitively or import explicitly). Existing APIs are `LeadingRunSupply.past`, `LeadingRunSupply.P2`, `OneSSMultiplicity.ssCount`, `LagSevenDonorCoverage.oldestOffset`, `SharpPeriodicSupply.phase/phase_eq_mod/lift_equal_mod`, `SS2LowSSTight.oldest_phase_ne_lowSS_endpoint`, `SS2LowSSTight.lowSS_endpoint_image`, `SS2LowSSTight.donor_oldest_is_S`, and `TwoSSTightDisjoint.neighborhood`.

Proposed direct endpoint signature (adjust namespace openings, not quantifiers):

```lean
theorem internal_sss_ne_lowSS_endpoint
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (q : Int)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false)
    (t : Int) (l : Nat) (htA : e t = true)
    (htP : LeadingRunSupply.P2 (LeadingRunSupply.past e t l))
    (htss : OneSSMultiplicity.ssCount (LeadingRunSupply.past e t l) ≤ 1) :
    LowSSEndpoint.endpointPhase p t l ≠ SharpPeriodicSupply.phase p q
```

Here `htP` ensures a positive lag, not the local SS contradiction itself. From phase equality, `phase_eq_mod` and `lift_equal_mod` translate `t-l` to `q`; apply `LagElevenPeriodic.e_shift` and `LeadingRunSupply.past_shift` to move the candidate current and window to endpoint clock `q`. For `l=1` and `l=2`, the current is respectively `q+1` and `q+2`, contradicting `htA`. For `l≥3`, use `past_append e t (l-3) 3` to expose chronological `q,q+1,q+2` as the trailing newest-first list `[false,false,false]`. Its two overlapping SS edges imply count≥2 through `OnePerRun.ssCount_append`. Do not assume a terminal S or a fixed lag in this statement.

An auxiliary phase-distinctness lemma needs actual donor bounds, not merely three unbounded S bits. Write `W = past e u d`, `s = u - oldestOffset W`, `ssCount W = 2`, `u-d ≤ s < q`, `q+2 < u`, and `e q=e(q+1)=e(q+2)=false`. `donor_oldest_is_S` gives `e s=false`. If `phase p s=phase p q`, periodicity gives `e(s+1)=e(q+1)=false`. Thus the three **distinct** edge starts `s,q,q+1` lie in `W`, contradicting `ssCount W=2`. Counting three distinct starts requires a real list/stream lemma; merely simplifying `ssCount [false,false,false]` proves only two.

Combine the two lemmas with E-368: `phase p s` and `phase p q` are distinct actual S phases in the donor neighborhood, both absent from the normalized lowSS endpoint image. E-368's `lowSS_endpoint_image` gives a nodup image of size `L.length` inside the actual neighborhood for every nodup current-A lowSS family, with **no lag cutoff**. Use list nodup/subset cardinality to conclude the image plus both donor phases has size `L.length + 2`. The donor must occur among the two supplied high-SS windows of the pair; never silently use the ambient set of all subtraction phases in place of the pair's concrete neighborhood.

## Complete E-370 edge still needed

The internal lemma only handles SSS at `q>s`. For `q=s`, the actual collision geometry must be derived from **two current-A minimal P2 donor windows sharing the true oldest-S phase**, including the chronology `W_A=C ++ [A]`, `W_S=X ++ C` (in the paper's chronological notation; reverse appropriately for `past`), their mass/moment equalities, `ssCount C=2`, and global circular NoSAAS. Do not take those identities as a new opaque `Prop` hypothesis while claiming the original pair theorem.

The paper case split, which needs its own Lean dependency chain, is:

1. `X=(AS)^(d_A-1) A` and `q=s`: contradiction by the NoSAAS run classification and P2 moment.
2. `X=(SA)^j A` and `q=s`: derive `C=(AS)^a AAA (SA)^b SSS`, `a=3b+2`, `b=3r+1`, `j=8r+6`. Exclude `phase(s+1)` from **all** current-A lowSS P2 endpoints: up to `t_A` the only mass-one/current-A candidate has moment `-1`; through `t_S` mass stays 2 or 3; later a window with its already used SS edge can only extend by an A-starting SS-free segment with nonnegative mass.
3. `q>s`: the internal-SSS lemma supplies `phase(q)`.

The final theorem must state global NoSAAS on the periodic stream, both actual minimal P2/current-A donors, common oldest S, one single SSS run accounting for the two overlapping SS edges, the lowSS finite family, and `|N(L∪{v,w})|≥|L|+2` (or the strictly stronger two-excluded-phase statement from which this follows). No positive period mass, owner map, finite census bound, or conclusion-shaped assumption. A theorem only under already-classified `C,X` shapes is a useful conditional sublemma, not full E-370.

## Falsification and statement audit

- Exercise `l=0,1,2,3`, `p=1`, wraparound, `q=s+1`, and donor offset at the earliest possible clock.
- Recheck the fixed p33 pure-alternating collision, p22 second-prefix collision, and p32 `q=s` family; the latter must route through case 2 rather than falsely satisfy the internal `q>s` premise.
- The p33 example with NoSAAS removed and `q=s` refutes the pure-prefix conclusion without NoSAAS; it does not refute the general two-phase capacity claim.
- Existing source and replay: [H-03 card](HYPOTHESIS_CARD_2026-10-06_SS2_INTERNAL_SSS.md), [final independent audit](data/ss2_pair_endpoints_20261006/audit/oldest-sss-endpoint-addendum.md), [E-368 module](../Recaman/SS2LowSSTight.lean).
- In the G5 audit quote every actual Lean theorem signature and answer whether its hypotheses include actual `e`, windows, phase list, donor provenance, or an unproved defined `Prop`. Check that the result is not a wrapper around the desired exclusion and that two actual donor S phases appear inside the concrete union neighborhood. The negative controls must fail when minimality, NoSAAS, current-A, or true oldest provenance is removed where used.

Evidence remains `PROVED-PAPER` until the exact full statement compiles, the harness/audit/controls pass, and an independent reader verifies the quantifiers and the geometry. The internal-SSS theorem can be landed separately only with its narrower claim and appropriate evidence label.
