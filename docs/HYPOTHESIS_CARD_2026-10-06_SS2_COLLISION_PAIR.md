# Hypothesis card: two minimal SS2 windows with the same oldest S

- ID: H-20261006-01
- Owner: parent proposer/falsifier; GPT-6.1-Sol independent paper researcher; issue81_auditor independent audit
- Created: 2026-10-06 19:05 JST; protocol frozen before discovery
- Status at freeze: CONJECTURED
- Research branch: issue #73 periodic supply; next question in [the saved plan](RESEARCH_PLAN_2026-10-03.md)
- Base: ba7fe41e3c96d0762198731d658b10dbfd9f53d1
- Scope: the GitHub branch at that base. Local main 75491ee contains different, unmerged research and overlapping evidence IDs; none of its results are premises here.

## Exact statement

For every p>0 and p-periodic e:Int→Bool with positive period sign mass,
let L be a finite set of distinct current-A phases in [0,p). Every b∈L
has a specified positive P2 lag d_b with ssCount≤1, not necessarily minimal
or S-ended. Let v,w be distinct current-A phases outside L. Their specified
windows are P2, minimal among **all** positive P2 prefixes, and have exactly
two overlapping SS edges. All words are newest-first; A=+1, S=-1,
P2 means mass=1 and one-based moment=0.

Let sigma(x)=phase p (x-oldestOffset(past e x d_x)).
Assume sigma(v)=sigma(w). For B=L∪{v,w}, let N(B) be the union of
actual S phases appearing in the specified windows. The target is
|N(B)|≥|L|+2. There are no bounds on p, lag or |L|, and no ambient Hall,
owner, NoSAAS, reachability or Recaman-orbit assumptions.

## Why it would matter

E-368 (on this base) supplies an injective lowSS endpoint image and one
additional phase, the oldest S of a minimal SS2 donor. Distinct oldest
phases therefore settle the two-donor case. This unit concerns the remaining
collision. It does not settle multiple collision groups, SS≥3, E-070,
E-067, or surjectivity E-001.

## Provenance and dependencies

- SS2LowSSTight.lowSS_endpoint_image, oldest_phase_ne_lowSS_endpoint,
  donor_oldest_is_S: PROVED-LEAN.
- TerminalASSBound.minimal_p2_terminal_bound and
  TwoSSPeriodicSupply.two_SS_endpoint_mod_injective: PROVED-LEAN.
- Paper consequence checked at entry: one oldest phase has at most two
  distinct minimal SS2 current-A sources. Its terminal A count is 0 or 1;
  equal terminal counts give equal full endpoint phases and hence the same
  source. This is a corollary, not a new frontier result.
- The missing second S may require rematching L. Demanding it from the
  donors alone while fixing all old endpoint assignments is stronger.
- No new external source or unproved defined Prop is used.

## Falsification plan (frozen)

- Discovery: all binary periods p=1..18 with positive sign mass.
- Holdout: all binary periods p=19..22 with positive sign mass, run once
  after discovery and its independent checks. These disjoint partitions
  are frozen for this unit; some period ranges were explored for other
  hypotheses before, so no claim of historically untouched data is made.
- Enumerate one representative per cyclic rotation, including imprimitive
  words. Record both representative and rotation-weighted word counts.
- For every current-A phase find its minimum positive P2 lag, without a
  lag<p restriction. Exact search uses d=kp+r, 0≤r<p: for period mass M>0
  and prefix mass m_r, k=(1-m_r)/M is the only possible nonnegative
  integer. Test the exact moment
  k Q + p M k(k-1)/2 + kp m_r + Q_r = 0.
  Since m_r≥-r, k≤p and d<p(p+1); direct scanning through p(p+1) is
  an independent safe check. The quotient formula covers all lags.
- For each same-oldest donor pair, enumerate **every subset** of eligible
  lowSS phases, including L empty. Check the union of actual S phases,
  not the count of all period S phases.
- Arbitrary lowSS specified lags are covered by monotonic reduction:
  its first P2 prefix d0≤d has SS≤1 and N(d0)⊆N(d). Checking every subset
  at these minimum witnesses implies the claim for any larger specified
  lowSS witnesses. Donor classification uses first P2, not first SS2 P2.
- Checks: direct lag scan for all representative current-A phases at p≤12
  and every collision word; independent Python checks of emitted examples
  and binary word counts; mandatory E-133 control:
  forward AAAASAASASASASSS, p=16, v=3/d=11, w=12/d=19,
  common oldest phase 9, period mass 2. This includes lag≥p.
- Boundary: p=1, no donors, L empty, terminal A 0/1, cyclic wrap,
  nonminimal lowSS witnesses via the monotonic argument above.
- Weakened history: all periodic binary histories, including SAAS; no
  actual-orbit or matching premise. A nonminimal donor is not allowed to
  repair a failed minimum-donor test.
- Source: experiments/ss2_collision_pair.cpp, SHA256
  184f9c96d9f9c24d4b4a009e555adbd6c6a66b401e42eb351efc22e8ef9343b4.
- Commands: clang++ -O3 -std=c++17 experiments/ss2_collision_pair.cpp -o /tmp/recaman-ss2-collision-20261006 ;
  /tmp/recaman-ss2-collision-20261006 1 18 ;
  /tmp/recaman-ss2-collision-20261006 19 22.
  Exact outputs will be retained under docs/data/ss2_collision_pair_20261006/.

## Acceptance and stopping condition

A complete audited inequality proof or a checked exact counterexample is
decisive. A genuinely new local structural lemma may justify formalization.
A new wrapper or an equivalent Hall formulation does not.

Paper-route gate: within 60–90 minutes of the 19:05 JST start, produce an
independent structural input or stop that proof route. Stop earlier for
a counterexample or circularity. At most one explicit cause-based repair
is permitted; do not extend census limits or named charges indefinitely.
Finite zero violations is COMPUTED only and does not pass the proof gate.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-10-06 | CONJECTURED | ba7fe41; frozen protocol above | Target and partitions fixed before runs |
| 2026-10-06 | OBSERVED | independent entry review, issue81_auditor | PASS with all-subset, arbitrary-lag reduction and lag≥p requirements incorporated |
| 2026-10-06 | COMPUTED | frozen C++ source, discovery p1–18 | 13,677 rotation representatives; 3 collision pairs, 10 lowSS subsets; violations 0 |
| 2026-10-06 | COMPUTED | unchanged source, holdout p19–22 | 164,696 representatives; 21 collision pairs, 76 lowSS subsets; violations 0 |
| 2026-10-06 | COMPUTED | independent Python direct replay | 16 record examples and 22 binomial word-count summaries pass; known E-133 pair reproduced |
| 2026-10-06 | PROVED-PAPER | [Sol report](data/ss2_collision_pair_20261006/sol61/report.md) | A-ending donor precedes S-ending donor after common-oldest lift; W_A=C A, W_S=X C, SS(X)=0, mass(X)=1, moment(X)=d_A |
| 2026-10-06 | STOPPED | independent capacity paper route | Geometry does not constrain lowSS endpoints inside C/X enough to supply a second S |
| 2026-10-06 | COMPUTED | [independent final audit](data/ss2_collision_pair_20261006/audit/report.md) | PASS: direct-scan implementation matches all 22 periods/10 fields; paper geometry also passes semantic review |

Exact outputs, source hashes, independent audit and command details are in
[the handoff](data/ss2_collision_pair_20261006/README.md). The total is
178,373 rotation representatives accounting for 3,716,111 words, but only
24 collision pairs and 86 lowSS-subset cases actually exercise the claim.
No range extension or hypothesis repair was used. The Python verifier's
initial int.bit_count compatibility failure was fixed before holdout.

## Semantic audit

The target is the local Hall inequality for one collision pair plus all
selected lowSS members. Positive mass is a target premise and a finite-search
device; dropping it would be a stronger claim. The paper route may prove
more, but must say so. No endpoint injectivity of true oldest S is assumed:
E-133 explicitly refutes it. Full endpoint injectivity and true oldest
collision are distinct. All finite data will retain COMPUTED status.

## Decision

Capacity proof route: STOPPED after the attempted second-S argument reduced
to an equivalent Hall restatement without a structural transition rule.
The general local Hall claim stays CONJECTURED; finite results are COMPUTED.
The auxiliary geometry is recorded as PROVED-PAPER, not as a capacity theorem
or a new allocation mechanism. Existing noSS classification E-145 is not
counted again. There is no new Lean module or evidence-registry promotion.

Reopen only with a concrete, separately falsifiable constraint on actual
lowSS windows whose endpoints lie at internal S positions of C/X, sufficient
to force additional neighborhood phases. A larger period census, a fixed-F
donor-only condition, or an unproved Hall/owner hypothesis is insufficient.
Multiple collision groups, SS≥3, E-070, E-067 and E-001 remain unresolved.
