# Hypothesis card: short P2 prefix reduction preserves tight neighborhoods

- ID: `H-20260920-03`
- Created: 2026-09-20 15:05 JST
- Owner: same-session four-role research pass
- Status: `CONJECTURED`

## Exact question

Let e be any integer-indexed periodic Bool stream with period p>0. Let B be
a nodup list of A phases below p. Each b is assigned a P2 window of length
d(b)<=11, with no minimality requirement. For each b choose the least positive
P2 prefix m(b). If |N_d(B)|=|B|, is N_m(B)=N_d(B)?

Intended consequence: for every integer donor clock u0 with P2(past e u0 11)
and ssCount=2, its true oldest S phase is outside N_d(B). For any such short
list B (without tightness), deleting that phase preserves |B|<=|N_d(B) minus s|.
No minimality on either side, no positive drift, no current-A donor premise,
no full supply set or period upper bound. All B members still current A.

## Existing work and smallest new edge

H-01 short_window_hall already uses P2 length<=11 without minimality.
H-02 short_tight_avoids_ss2_window accepts arbitrary donor but minimal B windows.
Repository search found take_past and the existing neighborhood membership lemma,
but no theorem asserting neighborhood equality under minimal-prefix reduction.
No stopped all-AAS route is reopened; w1 triples remain admissible.

Chain before implementation: every finite P2 window has a shortest P2 prefix;
its neighborhood is included in the original. Short Hall gives |B|<=|N_m(B)|,
and tightness gives |N_d(B)|=|B|, so the finite neighborhoods are equal. Apply H-02
to m and transport the nonmembership. In the nontight case one deletion consumes
at most the already-positive slack. The genuinely new edge is shrinking the
windows while preserving the whole tight neighborhood, not a new coverage name.

## Falsifier protocol and acceptance

- Discovery: all binary cycles p1..12, all period masses, all assignments of
  P2 windows with length<=11 to every sublist of A phases; multiple windows at
  one phase are alternative assignments, never duplicate B elements.
- Frozen holdout: the same exhaustive protocol at p=15 only, not H-02's p13/14.
- Compare actual set unions from strings for d and independently minimized m.
- Check equality on every tight assignment and donor avoidance for every
  length-11 P2 SS=2 window at every clock, regardless of current sign.
- Controls: record shrinking that changes a nontight neighborhood; check the
  known SS3 donor counterexample survives; no identity is accepted without a
  nonminimal assigned window appearing in the evaluated domain.
- Stop on a true counterexample to equality or avoidance. Do not restore
  minimality in the statement after seeing data. If no tight nonminimal example
  exists in range, say so rather than claiming it was exercised.
- Accept only with a symbolic proof, Lean audit, quantifier audit, and frozen
  computation. Same-session review does not replace independent promotion review.

## Evidence and decision

Frozen source/card hashes: `daytime/PRE_PREFIX_REDUCTION_SHA256SUMS`.
Commands: `python3 -u experiments/issue73_20260920/short_prefix_reduction.py --mode discovery`
and `--mode holdout`. Complete original JSONL files are `short_prefix_discovery.jsonl`
and `short_prefix_holdout.jsonl`. Source revision is in each output.

Discovery evaluated1141 nonminimal assignments and609 tight donor checks.
Holdout p15:32768 cycles,62545 assignments,8115 nonminimal assignments,
39340 tight assignments,4590 tight donor checks,10890 deletion checks;
no violations. Tight nonminimal assignments:0; they were not falsely counted
as exercised. Shrinking changed7995 nontight neighborhoods, so the equality
depends on tightness. SS3 counterexample preserved.

Formal proof completed: `exists_minimal_p2_prefix`,
`neighborhood_prefix_sublist`, `tight_neighborhood_eq_of_p2_prefix`,
`short_p2_tight_avoids_ss2_window`, `short_p2_ss2_deletion`.
The strongest deletion statement has no minimality on either side, no Hall
premise, no positive mass, arbitrary period and integer donor clock, but member
lags <=11 and donor length exactly11 remain. `./scripts/check.sh` passes with
2571 audited declarations; exact log `daytime/check_prefix.log`.
Independent-session review is still pending; no registry/frontier promotion.
