# Hypothesis card: SS2 donors versus arbitrary-length low-SS tight sets

- ID: H-20261002-01; parent issue #73.
- Status: CONJECTURED, before falsification and Lean implementation.
- Owner: Codex proposer/falsifier/formalizer, separate read-only auditor.
- Branch: codex/ss2-lowss-tight-avoidance.
- Base: 8ee8588f1015955c2474674ba1656cb296f8157c (main CI passed).
- Route gate starts 2026-10-02 09:47 UTC (18:47 JST); stop at 10:47 UTC
  unless a complete all-length proof route is established.

## Exact statement

For every p>0 and periodic e:Int→Bool, every nodup B:List Nat of phases
less than p and lag:Nat→Nat, assume every b in B is current A and
P2(past e b (lag b)) with ssCount<=1. Member minimality is not assumed.
Assume |neighborhood e p B lag|=|B|. For every u:Int, d:Nat, if
W=past e u d is P2, ssCount W=2 and every positive proper prefix is not
P2, then phase p (u-oldestOffset W) is outside neighborhood e p B lag.
All p,d,lag(b) are unbounded. No ambient Hall, NoSAAS, drift, distance
bound, owner-family Prop or orbit realization is assumed. Donor current A
is not needed by the proposed word/stream argument.

Central intermediate statement: a minimal SS2 donor's true oldest S
cannot equal the old endpoint of any current-A P2 window with SS<=1,
of any length, on the integer line or modulo p. This is endpoint
disjointness, not full neighborhood avoidance for an arbitrary singleton.

If this route succeeds, also derive its quantitative consequence:
any nodup set U of current-A low-SS suppliers satisfies |U|+1<=|D|
in the presence of a minimal SS2 donor. This adds one unit of slack,
not one per donor; different donor oldest positions are not assumed distinct.

Planned final Lean signature uses explicit e,p,B,lag,u,d and the concrete
P2/ssCount/proper-prefix hypotheses above, with conclusion
`phase p (u - oldestOffset (past e u d)) ∉ neighborhood e p B lag`.
No new defined hypothesis or coverage wrapper may substitute for this claim.

## Why it matters and prior search

E-366 (#81) proves avoidance only for short tight members (lag3/7/11).
E-128 supplies the all-length low-SS endpoint injection. The present result
would remove the member-length cutoff for the low-SS class, while high-SS
members remain outside scope. E-367 (#82) refutes word-only constant-span
bounds, so no such bound is sought. Existing LowSSTwoSSJointCapacity
restricts SS0 suppliers to lag3, SS2 donors to lag<15, and assumes S ends;
it does not supply this true-oldest/all-length/minimal-donor statement.

README/status/roadmap, glossary/proof map, portfolio, current frontier and
existing LowSS/SS2/Tight/Owner modules were inspected. Stopped pure-AAS,
lag-by-lag census extensions and owner-distance repairs are not reopened.

## Informal dependency chain before implementation

1. Generalize E-366's `ss2_aas_oldest_has_prefix` from the literal AAS
   suffix to any P2 suffix v. If W=(x A) v A^n is P2 and SS<=2, append
   equations give mass(x A)=-n and
   M(x A)+len(x A)+(len(x A)+len(v))*n+M(A^n)=0.
2. For n=0, E-366's derived prefix-ceiling/first-P2 argument gives a
   proper P2 prefix of x A. Since v is nonempty, it is proper in W.
   For n>0, the A-ended SS2 moment budget plus nonnegative tail moment
   contradicts the equation. This is the weakest new structural edge.
3. Existing `oldest_cover_clock_lt` forces the low-SS current A to be
   earlier than the donor. The exact same-history split about the true
   oldest S gives the shape in (1); donor minimality contradicts (2).
4. Periodic lifting transports an alleged equal phase to an equal
   integer endpoint, preserving actual current A, P2 and SS count.
5. Normalize each low-SS member to its S-ended P2 prefix (E-128), inside
   its original window. The E-128 endpoint map is injective and lies in
   N(B). Tightness forces its image to equal N(B). This derives endpoint
   ownership for this class without assuming general OS or Hall.
6. Endpoint disjointness gives avoidance. The actual donor oldest S is
   also outside the injective image for arbitrary U, yielding |U|+1<=|D|.

## Frozen falsification plan

- Reuse binary P2 lengths3/7/11/15/19 for discovery and length23 for
  holdout. These repository-used ranges are not fresh holdout data.
- For each minimal SS2 donor, scan every actual earlier current-A suffix
  ending at its true oldest S, checking P2/SS exactly. Include both zero
  and positive terminal A tails, and all prefix lengths.
- Weakened-history model: arbitrary finite binary words; no greedy orbit
  or NoSAAS condition. The already proved SS-count chronology rules out
  later low-SS covers; do not silently assume this for other cover classes.
- Negative controls: remove donor minimality (existing SS2 shared-AAS
  example), remove the cover SS<=1 restriction (the donor itself), remove
  tightness (existing p17 w1-covering singleton). Search the fixed ranges
  for controls removing SS2 or the covering current-A condition; report
  absence honestly rather than extending the ranges to manufacture one.
- Positive theorem applications must include a nonempty tight set and a
  low-SS supplier of lag>11 (for endpoint/strict-slack results), not only
  empty-set or short-window cases. Fixed construction: concatenate the
  reversed E-122 k1 word + current A and reversed E-367 k1 donor + current A
  into a periodic stream; verify all hypotheses before using it.
- Freeze script/card hashes before running discovery and holdout. No new
  census ceiling, core search, owner condition repair or mathematical repair.

## Acceptance, audit and stop

All-length Lean proof of the structural prefix lemma, integer/modular
endpoint disjointness and actual tight-neighborhood avoidance; independent
binder/RWCT audit and theorem-applied kernel controls; root/Audit, G5,
registry/proof map, full check and make test. A conjunction of existing
short-window results or a defined unproved owner hypothesis cannot pass.
Stop on a counterexample, missing generic prefix argument after60 minutes,
or wrapper-only content. Protected labels remain unchanged.

## Evidence / decision

Pending frozen falsifier. Do not claim general all-lag/high-SS tight
avoidance, arbitrary donor SS>=3, deletion Hall, E-070/E-067 or any orbit
result. If accepted, the remaining question is high-SS members of B.
