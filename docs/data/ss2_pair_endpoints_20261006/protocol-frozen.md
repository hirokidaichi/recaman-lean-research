# Hypothesis card: SS2 collision pair versus every lowSS endpoint

- ID: H-20261006-02
- Base: 65c25ab742ab4aa749bfd5f48438dbcb7b774d1d
- Created: 2026-10-06 20:54 JST; frozen before the new diagnostic runs
- Owner: parent proposer/falsifier; Sol6.1 investigates NoSAAS geometry independently; separate final auditor
- Initial status: CONJECTURED

## Exact bounded question

For every p>0, p-periodic e:Int→Bool with positive period sign mass, and
two phase-distinct current-A sources v,w with minimal P2 windows of SS=2
and the same true-oldest S phase sigma, define

E_low = {phase p(t-d) : e(t)=A, d>0, P2(past e t d),
         ssCount(past e t d)≤1, e(t-d)=S}.

All positive lags are included, not just each phase's first P2. Let
N_pair be the union of actual S phases in the two donor windows. The new,
stronger endpoint/core candidate is |N_pair \ E_low|≥2.

This is stronger than H-20261006-01's local Hall target: E-368's selected
injective lowSS endpoint image F is contained in E_low for every arbitrary
lowSS set L, so two phases here would extend F. A failure here is not a
counterexample to local Hall; lowSS neighborhoods and rematching can help.
No named second offset, ambient Hall, owner or NoSAAS premise is assumed.

## Why it would matter and dependencies

E-368 already excludes sigma from ALL such lowSS endpoints. A second
globally excluded S would be a new interaction between the donor core and
actual lowSS histories, independently sufficient for the single-pair
capacity problem. The previous argument merely restated failure as
N=F∪{sigma}; it did not test or prove this stronger, L-independent exclusion.

Use existing P2/mass/moment/ssCount/oldest definitions and E-368.
The paper geometry W_A=C A, W_S=X C narrows the candidate family, but is
not a proof of this endpoint claim. No new external source is used.

## Falsification plan (frozen)

- Reused discovery p1..18, reused holdout p19..22: the SAME period domain
  as H-20261006-01, for this different diagnostic. No fresh evidence or
  enlarged-range claim. Run holdout once after discovery certificates pass.
- All positive-mass binary words modulo rotation, retaining imprimitive words.
- All possible P2 lags via the already audited positive-mass quotient
  formula. For E_low collect EVERY S-ended lowSS P2 witness, not minimum
  lag only. For donors use the first P2 window and test SS=2.
- Emit all donor pairs and all endpoint witnesses, including endpoints
  whose windows lie outside the donor union in integer time.
- Independently verify each emitted pair and endpoint set by direct
  mass/moment scanning to p(p+1). E-133 is mandatory. LowSS S-endedness,
  periodic wrap, arbitrary lags, and common-oldest membership are checked.
- Report NoSAAS only as a diagnostic; do not silently filter the target.
- Small/weakened-history cases are the same abstract binary histories as
  before, without any orbit, matching or NoSAAS constraint.
- Source experiments/ss2_pair_endpoints.cpp SHA256
  fd55113d524a85189df42aa05a66f3cec644775a5df2909ea03aa9a0eacbc03e;
  included helper source experiments/ss2_collision_pair.cpp SHA256
  184f9c96d9f9c24d4b4a009e555adbd6c6a66b401e42eb351efc22e8ef9343b4.
- Commands:
  clang++ -O3 -std=c++17 experiments/ss2_pair_endpoints.cpp -o /tmp/recaman-ss2-pair-endpoints ;
  /tmp/recaman-ss2-pair-endpoints 1 18 ;
  /tmp/recaman-ss2-pair-endpoints 19 22.

## Acceptance / stop

Accept a complete paper proof of the new exclusion or an exact counterexample.
Finite survival is only COMPUTED. No theorem is inferred from the 24 pairs.
No offset repair or range extension is permitted in this short pass.
After 20–30 minutes without a structural proof, leave the candidate
CONJECTURED and stop this route; use the result to select the next question.

The independent NoSAAS pass asks whether the paper prefix families can
be reduced or refuted when an explicitly additional orbit-compatible
assumption forbids SAAS. Its exact card and controls will be saved separately.
Any result applies to that narrower class only; H-20261006-01/02 are unchanged.

## Semantic audit

E_low is a union over every eligible witness. Minimum-lag reduction applies
to the original neighborhood inequality, NOT automatically to E_low.
Passing the strong condition suffices for each chosen L, while failing it
does not refute H-20261006-01. Positive mass is used in the exhaustive
periodic lag bound; no zero-mass all-lag conclusion is claimed.

## Evidence and decision

Frozen before execution. Outcomes, failed attempts, audit and next decision
will be appended, preserving the exact target and ranges above.

