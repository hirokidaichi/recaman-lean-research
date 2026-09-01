# Round 17: target-low reset-repayment audit

Date: 2026-09-01 (JST)

Computation source state: base revision
`e7c86ad4e7d0e3395c34991c8b0270375e5c7042` plus the working-tree experiment files identified
below by SHA-256. This records the source even though the round has not been committed.

## Conclusion

The exact reset-repayment conjecture was **not refuted**, but this research branch is now
`STOPPED`.  The strongest result of the round is an audited and strictly stronger residual
interface, not a repayment theorem:

- `PROVED-LEAN`: the fixed-root branch retains the universal no-escape property, arbitrarily late
  terminal **start** clocks, and the target-low predicate at every selected start;
- `PROVED-LEAN`: from any target-low terminal comb in that stream, the least later target-low clock
  produces a genuine consecutive `TargetMacroSuccessor`;
- `REFUTED`: interval order, blocker one-use, local actual-step legality, addition origin, and a
  fixed reset-time history do not force repayment;
- `CONJECTURED`: a permanent-missing canonical tail might still force non-uniform repayment, but no
  independently testable causal lemma found in this round implies it.

The direct-surjectivity branch count remains zero.  Reset repayment is downgraded from 40/100 to
15/100 and should not be resumed until a new global invariant bounds blocker births after a reset.

## Bounded research question

Question:

> In the fixed-root branch of a hypothetical permanent missing-target tail, does every upward
> terminal reset eventually receive a later target-low terminal entry strictly below the reset
> blocker?

Acceptance test:

1. preserve the exact same-target and fixed-root provenance in Lean;
2. produce a causal lemma which implies repayment without mentioning target occurrence, future
   return, or canonical reachability;
3. survive boundary cases, weakened-history countermodels, discovery, and frozen holdout.

Stopping condition:

- an exact-step seeded counterexample kills the only independently testable causal bridge;
- the repaired bridge becomes repayment or target occurrence in different words; or
- supply and demand remain of the same unbounded order with no strict drift.

The stopping condition was met by the fixed-history-preload audit below.

## Exact residual interface

The Round 16 definition discarded three facts which its construction already knew:

1. the selected terminal start was target-low;
2. arbitrarily late low clocks gave arbitrarily late **starts**, not only late final times;
3. the fixed root separated every future terminal comb, not just the selected witnesses.

The repaired definition is:

```lean
def UnboundedRightTerminalStream (target tailStart root : Nat) : Prop :=
  (∀ start length blocker,
    tailStart ≤ start →
    HistoryTerminatedComb start length blocker →
    root ≤ a start) ∧
  ∀ cutoff,
    ∃ start length blocker,
      cutoff < start ∧
      tailStart ≤ start ∧
      nextSubtractionCandidate start < target ∧
      HistoryTerminatedComb start length blocker
```

`MissingPermanentAboveTail.eventualHigh_or_unboundedRightTerminal` constructs this stronger object
without any new mathematical assumption.  Its axiom set remains
`{propext, Classical.choice, Quot.sound}`.

The theorem

```lean
UnboundedRightTerminalStream.exists_targetMacroSuccessor
```

chooses the least later target-low start after a completed comb.  Minimality excludes an
intermediate low clock, and the missing-target candidate dichotomy upgrades every intermediate
clock to strict high.  Thus the fixed-root branch really does support indefinitely repeatable
same-target macro analysis.  This closes a proof-engineering gap only; it proves no return below a
blocker.

## Strongest attempted causal bridge

Let an upward reset install blocker `B = blocker₂` at the second comb.  The strongest finite
resource statement which did not explicitly mention repayment was:

> While all later target-low terminal entries stay at least `B`, every later terminal blocker was
> already first-seen before the reset start `s₂`.

Call this fixed-history blocker preload.  If it held, repayment would follow as a complete paper
argument:

1. `a s₁ ≤ B` follows from the upward-reset interval order.
2. If repayment fails, every later terminal entry is at least `B`.
3. Applying `next_entry_below_or_blocker_lt` from the reset comb to every later comb gives
   `B < blockerⱼ`.
4. Preload assigns every such blocker a `FirstAt` clock `< s₂`.
5. `same_blocker_finalTime_eq` makes chronological terminal blockers distinct; distinct first
   values have distinct first clocks.
6. The unbounded stream supplies `s₂ + 1` later blockers, contradicting injection into the
   `s₂` clocks below `s₂`.

This implication is `PROVED-PAPER`.  Its only unproved input is precisely the preload statement.

## Falsification

### Exact seeded continuation

The finite seed

```text
seen={0,1,6,8,13}, current=13, nextClock=7
```

is followed by the exact greedy Recamán step rule.  It is not claimed reachable from the canonical
initial state.  The reproducible command is:

```bash
ruby experiments/target_reset_preload_counterexample.rb 1200
```

Script SHA-256:
`2f0fdb32b38492371c37f2e4e47e2a69ff8ba333a586f09a89a39f2410729fd6`.

The target-4 terminal sequence contains:

```text
start 37: entry 7,   blocker 6
start 54: entry 17,  blocker 14   (upward reset)
start 69: entry 61,  blocker 51
start 101: entry 25, blocker 24
start 110: entry 113, blocker 84
start 190: entry 31, blocker 28
start 207: entry 200, blocker 199
```

Before the first later entry below 14, blocker 199 is newly generated at clock 65 by the forced
addition `134 + 65 = 199`.  Since `65 ≥ 54`, fixed-history preload is `REFUTED`.  The same trace
also refutes immediate repayment and shows why blocker one-use alone is not a finite resource.
The trace eventually reaches entry 11 at start 353 and target 4 at clock 1107, so it does not
refute the exact permanent-missing hypothesis.

The exact output is:

```text
seeded-preload-counterexample target=4 current=13 nextClock=7 steps=1200 seen={0,1,6,8,13}
  terminal start=16 finish=20 entry=10 blocker=8 blockerOrigin=seed
  terminal start=23 finish=31 entry=24 blocker=20 blockerOrigin=add@7(13) UPWARD
  terminal start=37 finish=39 entry=7 blocker=6 blockerOrigin=seed
  terminal start=54 finish=60 entry=17 blocker=14 blockerOrigin=add@12(2) UPWARD
  terminal start=69 finish=89 entry=61 blocker=51 blockerOrigin=add@30(21) UPWARD
  terminal start=101 finish=103 entry=25 blocker=24 blockerOrigin=sub@23(47)
  terminal start=110 finish=168 entry=113 blocker=84 blockerOrigin=add@39(45) UPWARD
  terminal start=190 finish=196 entry=31 blocker=28 blockerOrigin=add@19(9)
  terminal start=207 finish=209 entry=200 blocker=199 blockerOrigin=add@65(134) UPWARD
  terminal start=217 finish=235 entry=177 blocker=168 blockerOrigin=add@43(125)
  terminal start=243 finish=263 entry=150 blocker=140 blockerOrigin=add@88(52)
  terminal start=273 finish=277 entry=117 blocker=115 blockerOrigin=add@34(81)
  terminal start=301 finish=307 entry=77 blocker=74 blockerOrigin=sub@47(121)
  terminal start=311 finish=321 entry=66 blocker=61 blockerOrigin=sub@69(130)
  terminal start=331 finish=333 entry=42 blocker=41 blockerOrigin=add@14(27)
  terminal start=337 finish=341 entry=33 blocker=31 blockerOrigin=sub@190(221)
  terminal start=353 finish=355 entry=11 blocker=10 blockerOrigin=sub@16(26)
  terminal start=358 finish=412 entry=361 blocker=334 blockerOrigin=add@104(230) UPWARD
  terminal start=432 finish=474 entry=286 blocker=265 blockerOrigin=add@66(199)
  terminal start=502 finish=506 entry=197 blocker=195 blockerOrigin=add@61(134)
  terminal start=516 finish=548 entry=166 blocker=150 blockerOrigin=sub@243(393)
  terminal start=578 finish=582 entry=79 blocker=77 blockerOrigin=sub@301(378)
  terminal start=608 finish=610 entry=18 blocker=17 blockerOrigin=sub@54(71)
  terminal start=619 finish=639 entry=608 blocker=598 blockerOrigin=add@187(411) UPWARD
  terminal start=649 finish=919 entry=575 blocker=440 blockerOrigin=add@107(333)
  terminal start=1013 finish=1031 entry=209 blocker=200 blockerOrigin=sub@207(407)
  terminal start=1057 finish=1061 entry=119 blocker=117 blockerOrigin=sub@273(390)
  terminal start=1087 finish=1089 entry=46 blocker=45 blockerOrigin=add@38(7)
  target-hit clock=1107 value=4
```

The existing abstract `finiteBasin_rightLadder_countermodel` independently shows that interval
order, one-use, unboundedness, and no-escape alone permit permanent non-repayment.  It does not
carry the canonical orbit or target-low provenance and therefore refutes only the weakened model.

### Canonical boundary and frozen ranges

The canonical target-4 upward resets at starts 23 and 38 are not repaid before `a 131 = 4`.
They cannot instantiate `TargetMacroSuccessor.tail`, because the global target-missing field is
false.  They are boundary tests, not exact counterexamples.

The standard-prefix proxy was reproduced with:

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_upward_provenance_probe.cpp \
  -o /tmp/round17_target_upward_provenance
/tmp/round17_target_upward_provenance 20000000
/tmp/round17_target_upward_provenance 2000000000
```

Probe SHA-256:
`704ab0071a269c8d5186a660616a233f5182fe35adb7489a9a68c43a0ded92e6`.

- discovery through 20M: 20 upward resets, 18 repaid, two target-4 boundary cases;
- frozen holdout 20M+1 through 2B: eight additional resets, all eight repaid;
- cumulative through 2B: 28 resets, 26 repaid, the same two boundary cases.

These results are `COMPUTED`, not evidence for a permanent missing tail, whose antecedent cannot be
observed in a finite prefix.

A separate seeded falsification harness freezes its RNG and discovery/holdout parameters:

```bash
ruby experiments/target_reset_repayment_probe.rb 5000 200 10000 20260901
ruby experiments/target_reset_repayment_probe.rb 1000 200 50000 20260902
```

Script SHA-256:
`5c299676ea5dc48ec247ae02777f8b627e4827e9cb3f4ef8f51aa7b43d2cb51c`.

| range | upward macros | repaid | target ended | horizon censored | max resolved wait |
|---|---:|---:|---:|---:|---:|
| discovery | 31,894 | 31,259 | 337 | 298 | 9 episodes |
| holdout | 8,753 | 8,652 | 77 | 24 | 9 episodes |

The holdout had no censor older than half its horizon; this is still finite seeded evidence and not
a proof.  The discovery run had one mature censor, reinforcing the decision not to assume a waiting
bound.

Exact aggregate outputs, including the frozen sample lines, were:

```text
seeded-repayment-holdout seeds=5000 maxNextClock=200 steps=10000 rng=20260901
  exactMacroUpward=31894 repaid=31259 targetEnded=337 censored=298
  maximumRepayWaitEpisodes=9 matureCensored=1 maximumCensorAge=9989 maximumCensorLaterEpisodes=56
  censored sample=11 target=15 sourceStart=9530 anchor=9244
  target-ended sample=18 target=2 sourceStart=55 anchor=46 hitClock=91
  censored sample=27 target=4 sourceStart=8611 anchor=8086
  censored sample=54 target=4 sourceStart=9534 anchor=9275
seeded-repayment-holdout seeds=1000 maxNextClock=200 steps=50000 rng=20260902
  exactMacroUpward=8753 repaid=8652 targetEnded=77 censored=24
  maximumRepayWaitEpisodes=9 matureCensored=0 maximumCensorAge=6802 maximumCensorLaterEpisodes=0
  censored sample=4 target=43 sourceStart=48712 anchor=48214
  censored sample=20 target=9 sourceStart=47554 anchor=46492
  target-ended sample=26 target=4 sourceStart=23 anchor=13 hitClock=131
  target-ended sample=26 target=4 sourceStart=38 anchor=25 hitClock=131
```

## Decision and roadmap

Hypothesis-card status: `STOPPED`.

The exact repayment statement remains logically `CONJECTURED`; it is not installed as a Lean
assumption.  The branch stops because its only finite-capacity proof route is refuted, while the
global repair

```text
post-reset blocker birth → target occurrence or left return
```

is the desired conclusion in different words.  A claim that only finitely many blockers are born
inside a no-return corridor has the same problem.

Updated assessment:

| branch | score | decision |
|---|---:|---|
| audited A/B residual architecture | 85/100 | keep as the exact handoff theorem |
| fixed-root target-low successor stream | 80/100 | `PROVED-LEAN` infrastructure |
| upward reset repayment | 15/100 | `STOPPED`; exact statement retained only as conjecture |
| fixed-history blocker preload | 0/100 | `REFUTED` by seeded exact continuation |
| eventual-high discharge | 12/100 | still parked; arbitrary finite seeded corridors survive |

Reopen repayment only after finding an independently testable global invariant which bounds
post-reset blocker births without mentioning future return, target occurrence, or canonical
reachability.  Until then, further macro wrappers, record-gap coefficient tuning, fresh-token
charging, and local origin refinements should not be pursued.

## Validation and changed files

Lean changes:

- `Recaman/TargetTailResidualKernel.lean`
- `Recaman/Audit.lean`

Research artifacts:

- `docs/HYPOTHESIS_CARD_2026-09-01_RESET_REPAYMENT.md`
- `docs/RESET_REPAYMENT_AUDIT_2026-09-01.md`
- `experiments/target_reset_repayment_probe.rb`
- `experiments/target_reset_preload_counterexample.rb`

Targeted validation completed:

```text
lake build Recaman.TargetTailResidualKernel  # 177/177 jobs
lake build Recaman.Audit                     # 230/230 jobs
git diff --check                             # clean
```

Full repository validation completed after the documentation update:

```text
./scripts/check.sh
# Build completed successfully (230 jobs).
# Axiom audit: 1082 declarations, all within
# {propext, Classical.choice, Quot.sound}.
# All Lean builds and audits passed.
```

The prohibited-token scan also found no `sorry`, `admit`, `native_decide`, or user-defined
`axiom`.
