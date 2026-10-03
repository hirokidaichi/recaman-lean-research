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
at most the already-positive slack. The proposed new edge was strict shrinking
under the original full-P2/tight premises; its nonvacuity still needs evidence.

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

## Historical 2026-09-20 evidence and decision

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

## 2026-09-23 02:00 independent audit

The original exact claim above is unchanged: full `P2(past e b (lag b))` for
each member, and `m b` is the least positive P2 prefix. The Lean equality
signature is broader: it assumes `m b <= lag b <= 11` and `P2` at `m b`, but
does not assume `P2` at `lag b` or minimality of `m b`. The original follows
by applying `exists_minimal_p2_prefix` and then the equality theorem. The
source theorem's extra domain does not supply a strict witness for the
original card.

The Lean proof is the direct composition of short Hall for `m`, prefix
neighborhood sublist inclusion, and equality of finite lengths from
tightness. It has no H-02 dependency. Its status as a mathematically new
input for the original strict-reduction subcase remains unverified.

Original experiment replay, byte-identical to the frozen daytime JSONL:
p1..12 had 1,141 nonminimal assignments; p15 had 8,115 nonminimal and
39,340 tight assignments, with `tight_nonminimal=0`. `PASS` checks only that
nonminimal assignments, changed nontight neighborhoods, and donor checks
are positive. It does not require a tight nonminimal assignment. Thus the
tested strict full-P2/tight case remains unexercised. This does not prove
global impossibility or make the entire exact claim vacuous: period-4
`AAAS`, `B=[2]`, `m=lag=3` has current A, P2 `AAS`, and tight `N=[3]`.

A strict tight source instance at the same period and B uses `m=3`,
`lag=4`, `past4=AASA`, `N_m=N_lag=[3]`; `P2(past4)` is false, so it is
outside the original claim. A strict full-P2 nontight control is period-9
`ASAAASASS`, `B=[4]`, `m=3`, `lag=7`, with `N_m=[1]` and
`N_lag=[1,7,8]`. No exact-premise strict tight witness is asserted.

`short_p2_tight_avoids_ss2_window` uses the equality to transport the
earlier H-02 avoidance theorem; `short_p2_ss2_deletion` depends on that
transport in its tight branch. H-02's 01:30 audit found a limited semantic
pass but an overall missing preformalization gate. These downstream claims
are inventoried, not promoted or used as established results here.

Candidate packet: `data/issue73_20260923/slot0200/` contains source and
card snapshots, exact signature audit, frozen checker source, raw outputs,
commands, and manifest. This 02:00 packet does not repair the historical
missing independent preformalization entry check. The independent Sol gave
a limited semantic pass to the original-card-to-Lean implication and to the
literal equality proof, but found the exact strict full-P2/tight subdomain
unverified. The overall procedural verdict is **未完了**. This is neither a
counterexample to the equality nor a proof that strict configurations are
globally impossible. H-03 remains `CONJECTURED`, with no new E-row,
frontier, or proof-map claim. The next decision is whether the original
strict subcase has any realized tight configuration under exactly its
premises. Until then, strict reduction is not an exercised new input.

The parent audit is
`adversarial_audits/H-20260920-03_20260923_0200.md`; the daily handoff
is `RESEARCH_HANDOFF_2026-09-23_SOL.md`. The old 2026-09-20 section above
is a historical record, not this audit's verdict.
