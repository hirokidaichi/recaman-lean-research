# Hypothesis card: the extremal boundary of the periodic supply capacity

- ID: `H-20260911-01`
- Created: 2026-09-11 09:10 JST
- Status: `COMPUTED` (E-175..E-179). Self-strengthening `slack ≥ collision excess` is
  `REFUTED` (E-180). E-070 / E-067 remain `CONJECTURED`.
- Research branch: issue #73, after E-128 (low-SS joint capacity) and E-131 (endpoint
  repetition budget)

## Exact statement

Fix an integer `p ≥ 1` and a periodic sign word `e : Z → {A,S}` of period `p` with
positive period sum `σ > 0`. Write

- `D` = the subtraction phases,
- `U` = the addition phases admitting a P2 supplier at some lag `d ≥ 1`,
- for `t ∈ U`, `d_t` = the least such lag, `w_t = past e t d_t` the minimal window,
- `U_low  = { t ∈ U : ssCount w_t ≤ 1 }` — exactly the class of E-128,
- `U_high = { t ∈ U : ssCount w_t ≥ 2 }` — the remainder E-130 blocks.

Call the word **tight** when `|U| = |D|`. The card freezes four claims.

```text
T1 (sharpness)     for every p there is a positive-sum word of period p with |U| = |D|
T2 (extremality)   tight  =>  U_high = empty,  i.e. every minimal window has ssCount <= 1
T3 (strict slack)  U_high nonempty  =>  |U| <= |D| - 1
T4 (forced charge) on a tight word the bipartite graph
                     t in U  ->  { subtraction phases inside w_t }
                   has exactly ONE perfect matching, and that matching sends every
                   t to the OLDEST subtraction of w_t
T6 (local donation) if ssCount w_t >= 2 then some subtraction s inside w_t can be
                   deleted and the graph above still saturates U
```

T6 is the local form of T3: it does not merely count the spare subtraction, it places it
inside the offending window. It is the statement a Lean proof would consume.

T2 and T3 are contrapositives of each other only up to the trivial direction; both are
recorded because they are measured separately.

The natural quantitative strengthening is stated in order to be killed:

```text
T5 (false)   slack >= c,  where c = |U| - |image of the oldest-S charge|
```

## Why it would matter

- T2 says the extremal boundary of E-070 lies **entirely inside the class E-128 already
  proves**. The part of E-070 that is tight is therefore already a theorem, and the whole
  remaining content of E-070 is the strict inequality T3. No future capacity argument has
  to be sharp on the uncovered class.
- T4 explains the entire history of refuted charges in one sentence. The oldest-S map of
  E-069 is not a bad guess: it is the *unique* charge on every tight word. It is refuted
  only on words that carry slack, where its collisions are harmless. So no fixed selector
  can be repaired into a general charge, and no fixed selector can be wrong on the
  extremal boundary either. This is a constraint on admissible proofs, in the style of
  the E-050 phase-capacity no-go.
- T5 being false says the obvious way to convert T4 into a proof — pay one spare
  subtraction per collision — does not work. The accounting must be sublinear in the
  collision count.

None of T1..T4 proves E-070 or E-067, and none of them bears on surjectivity directly.

## Provenance and dependencies

- Definitions used: `ShortPeriodicSupply.P2`, `LeadingRunSupply.past`, `mass`, `moment`,
  `OneSSMultiplicity.ssCount`, `LagElevenPeriodic.subPhases`.
- Proved results consumed, not re-derived: E-128 (`periodic_lowSS_capacity`) for the
  meaning of `U_low`; E-131 for "two windows sharing an endpoint force `ssCount ≥ 2`",
  which is the `m = 1` case and is what links a collision to a high-SS window;
  E-130 for why the S-ended normalisation stops at `ssCount = 2`.
- The backward scan terminates by a drift bound rather than a cap: for a fixed start the
  backward partial sums satisfy `g(l) = g(l-p) + σ`, so `min_{l≥1} g(l) = min_{1≤l≤p} g(l)`,
  and once the running sum exceeds `1 - Gmin` no longer lag can return it to 1. The same
  argument yields the lag bound `d ≤ p(p+1)` from `σ > 0` alone. This is being formalised
  as `Recaman/PeriodicSupplyBound.lean`; until then the probes carry it as an unproved
  (but elementary) termination criterion, and that is recorded as a dependency.
- Unverified mathematical assumptions: none beyond the above. No Recamán reachability,
  subtraction freshness, NoSAAS or minimal-lag hypothesis enters any of T1..T5.

## Falsification plan

- Positive controls: the all-A word of every period has `U = D = empty` and is tight;
  `A^{p-1}S` has `|U| = |D| = 1`. Both must come out tight.
- Negative control: dropping the moment equation makes every phase of `AA` supplied while
  `D` is empty; the checker must not report that word as tight.
- Independent cross-check: the probe recounts the positive-sum words of period 19..22 and
  must reproduce E-081's recorded 3,487,066. It aborts otherwise.
- Discovery range: all necklace representatives of positive-sum words with `p ≤ 22`.
- Frozen holdout range: `p = 23..31`, run only after discovery passed unrepaired.
- Every counterword is re-derived by direct summation in a second, independent
  implementation (`verify_counterword.py`) before being recorded.
- Maximum one permitted repair: none. T5 is stated before execution precisely so that its
  failure is recorded rather than repaired into a weaker exponent.
- Stop condition: a positive-sum periodic word with `|U| > |D|` (which refutes E-070), or
  a tight word with a high-SS minimal window (which refutes T2), or a tight word with two
  perfect matchings (which refutes T4).

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-11 | `COMPUTED` | `capacity_extremal 2 24 1` | no E-070 or E-067 violation; `|U| = |D|` attained at every period; every tight word has `tightMaxSS = 1`; local Hall matching saturates |
| 2026-09-11 | `COMPUTED` | `capacity_extremal 25 31 1` (frozen holdout) | same, through period 31 |
| 2026-09-11 | `COMPUTED` | `forced_matching 8 22` | 336 tight words, 336 with a unique perfect matching, 1,110 forced edges, 1,110 equal to the oldest-S target and 1,110 with the window's oldest position itself an S |
| 2026-09-11 | `COMPUTED` | slack table in `capacity_extremal.txt` | `U_high` nonempty forces slack `≥ 1` at every period 10..31 |
| 2026-09-11 | `REFUTED` | `collision_slack 4 24` | T5 fails at period 18 on `AAAASSAAAASAAASSSS` (`|U|=6`, `|D|=7`, `c=2`, slack 1) and at period 21 on `AAASASAASAAASSSAAASSS` |
| 2026-09-11 | `COMPUTED` | `verify_counterword.py` | both counterwords re-derived by direct summation; phases 1 and 11 collide on subtraction 4, phases 3 and 13 on subtraction 10 |
| 2026-09-11 | `COMPUTED` | `seam_pumping 16` | 627,264 glued pairs and 6,751,269 glued triples of tight blocks, periods up to 40: no net surplus |
| 2026-09-11 | `COMPUTED` | `tight_density 4 22` | largest `\|D\|` attaining `\|U\| = \|D\|` grows with the period: 1 through `p=9`, 2 at 8, 3 from 10, 4 from 14, 5 from 18, 6 from 20 |
| 2026-09-11 | `COMPUTED` | `local_surplus 8 22` | T6 holds in the strong form: in every word carrying a high-SS window, **every** such window donates a deletable subtraction from inside itself. No failure |

## Semantic audit

- Informal statement implies formal statement: yes. "The tight cases are already covered"
  is exactly T2 with `U_low` defined by the same `ssCount ≤ 1` predicate E-128 uses.
- Formal statement implies intended consequence: T2 gives that E-070 restricted to tight
  words is E-128, because on such a word `U = U_low`. It does not give E-070.
- Counterfactual examples that should make the statement false: a tight word containing
  the E-130 shape `AAASSSASASA` as a minimal window; a tight word where the window's
  oldest sign is an A. Neither occurs in `p ≤ 31`.
- Could the claims be proved from weaker or vacuous assumptions?: T1 is nearly vacuous at
  `|D| ≤ 1` (all-A and `A^{p-1}S`), so the content of T1 is that tightness survives at
  `|D|` growing with `p`. `tight_density.txt` is included for exactly this reason and
  shows the largest tight `|D|` rising to 6 by period 20. T2 and T4 are not vacuous: 336
  tight words with 1,110 supplied phases are exercised.
- Are reachability, freshness, time order, or actual-orbit provenance accidentally
  omitted?: yes, deliberately. These are free-word claims about periodic sign words and
  say nothing about the canonical Recamán orbit.
- Horizon caveat: extending `p` alone never promotes a label here. T1..T4 stay `COMPUTED`
  and T5 is `REFUTED` by an exhibited word, which is the only label change earned.

## Decision

- Continue / formalize / refute / stop: record T1..T4 and T6 as `COMPUTED`, T5 as
  `REFUTED`, and formalise the drift bound (`PeriodicSupplyBound`), which is a genuine
  theorem and is what every probe in this branch silently relies on.
- Reason: the epoch's usable output is a restriction on proofs plus one new local target.
  The oldest-S charge is forced where the inequality is tight, so the search for a better
  *selector* is over; what is missing is an accounting for collisions that is not linear
  in their number, and T5 shows the linear one is false. T6 is the replacement target:
  it is local, it places the spare subtraction rather than counting it, and it is the
  form a Lean proof can consume.
- Next gate: prove T6 for the smallest high-SS shape — a minimal window whose `ssCount`
  is exactly 2 — using the leading-run bounds E-166/E-169 and the endpoint budget E-131.
  Do not restart a named selector; T4 shows selectors are already determined where it
  matters and already refuted where it does not.
- Reopen only if: a tight word with a high-SS minimal window is found (which would put the
  extremal boundary outside E-128 and revive the class-extension program), or a
  sublinear collision accounting is proposed with its own falsifier.
