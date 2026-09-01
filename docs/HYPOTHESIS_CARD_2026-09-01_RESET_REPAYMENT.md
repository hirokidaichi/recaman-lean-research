# Hypothesis card: target-low upward-reset repayment

- ID: `H-20260901-17`
- Owner: Codex research loop (proposer / falsifier / formalizer / auditor separated)
- Created: 2026-09-01 (JST)
- Status: `STOPPED`
- Research branch: Round 17, finite-root / right-terminal residual

## Exact statement

The existing residual stream must retain both the universal fixed-root no-escape property and the
target-low provenance from which each selected terminal comb was extracted:

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

The research hypothesis is the following non-uniform repayment statement.  The third comb is not
required within a bounded number of episodes.

```lean
def TargetLowUpwardResetRepayment : Prop :=
  ∀ target tailStart root s₁ k₁ blocker₁ s₂ k₂ blocker₂,
    UnboundedRightTerminalStream target tailStart root →
    TargetMacroSuccessor target tailStart
      s₁ k₁ blocker₁ s₂ k₂ blocker₂ →
    blocker₁ < blocker₂ →
    ∃ s₃ k₃ blocker₃,
      s₂ + 2 * k₂ < s₃ ∧
      nextSubtractionCandidate s₃ < target ∧
      HistoryTerminatedComb s₃ k₃ blocker₃ ∧
      a s₃ < blocker₂
```

The stream hypothesis already contains `MissingPermanentAboveTail` indirectly only through the
theorem which constructs it; `TargetMacroSuccessor` retains that actual missing-tail certificate
explicitly.  No uniform waiting bound is asserted.

## Why it would matter

- Frontier obligation discharged: Gate 6 of the finite-root no-escape decomposition.
- Stronger than an existing identity or equivalent reformulation because: the conclusion forces a
  strict return below a particular historical blocker; it is not merely target occurrence, tail
  return, or chronological unboundedness.
- Smallest useful consequence: a particular upward-reset anchor eventually gets a strict
  target-low return.  A separate nesting or drift argument would still be required to consume the
  fixed root globally; this card does not claim that repayment alone completes that assembly.

## Provenance and dependencies

- Definitions used: `MissingPermanentAboveTail`, `nextSubtractionCandidate`,
  `HistoryTerminatedComb`, `TargetMacroSuccessor`, `UnboundedRightTerminalStream`.
- Lean theorems used: `candidateBelow_exists_historyTerminatedComb`,
  `next_entry_below_or_blocker_lt`, `fresh_intervals_ordered`,
  `upward_reset_origin`, `eventualHigh_or_unboundedRightTerminal`.
- Unverified mathematical assumptions: `TargetLowUpwardResetRepayment` itself.
- Literature source or analogy: opportunity counting and frontier-window balance are analogies
  only; no cited result currently implies the statement.

Informal dependency chain:

```text
unbounded target-low clocks
  → maximal fresh terminal combs with target provenance
  → consecutive same-target macro successors
  → upward reset origin plus actual first-occurrence chronology
  → later entry below the reset blocker
  → fixed-root escape / coverage progress
```

The weakest new lemma which would move the mathematical frontier is the fourth arrow: a causal
generation-versus-reuse inequality for the actual orbit which the abstract right ladder cannot
satisfy.  Merely preserving target-low provenance is a semantic repair, not that lemma.

## Falsification plan

- Small and boundary cases: target 4 early upward resets; singleton combs; reset gap 1; blocker 0;
  the first possible target-low start after a terminal final time.
- Adversarial or weakened-history model: `finiteBasin_rightLadder_countermodel`, arbitrary-history
  comb schedules, and exact-`Basic.step` seeded walks from `seeded_right_record_search`.
- Discovery range: standard prefix through 20,000,000 terms, freezing the exact terminal episode
  extraction already used by `target_ancestry_capacity_probe`.
- Frozen holdout range: 20,000,001 through 2,000,000,000 terms, using the existing 2B audit output.
- Maximum one permitted repair: add one independently checkable actual-orbit provenance predicate;
  do not add target occurrence, future return, or canonical reachability as a field.
- Stop condition: an exact-step seeded counterexample satisfies the repaired statement's
  assumptions; the only separator is deterministic canonical reachability; or every proposed
  charge has supply and demand of the same unbounded order with no strict drift.

## Evidence log

Computation source state is base revision
`e7c86ad4e7d0e3395c34991c8b0270375e5c7042` plus the working-tree probes. The repayment probe
SHA-256 is `5c299676ea5dc48ec247ae02777f8b627e4827e9cb3f4ef8f51aa7b43d2cb51c`;
the preload probe SHA-256 is
`2f0fdb32b38492371c37f2e4e47e2a69ff8ba333a586f09a89a39f2410729fd6`.
Exact outputs are frozen in `docs/RESET_REPAYMENT_AUDIT_2026-09-01.md`.

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-01 | `OBSERVED` | Round 16, `target_ancestry_capacity_probe` at 20M discovery | 18/20 upward resets repaid by the next terminal; two target-4 epochs ended by target occurrence. |
| 2026-09-01 | `OBSERVED` | Round 16, frozen 20M–2B holdout | 26/28 upward resets repaid by the next terminal; the same two target-4 cases remained. |
| 2026-09-01 | `REFUTED` | `finiteBasin_rightLadder_countermodel` | Interval order, blocker one-use, and unboundedness alone do not imply repayment. |
| 2026-09-01 | `REFUTED` | `seeded_right_record_search --walk-record-sub` | Upward right-record plus local legality does not force forced-addition blocker origin. |
| 2026-09-01 | `PROVED-LEAN` | `lake build Recaman.TargetTailResidualKernel` | The repaired stream retains universal fixed-root no-escape, arbitrarily late start clocks, and target-low provenance. |
| 2026-09-01 | `PROVED-LEAN` | `UnboundedRightTerminalStream.exists_targetMacroSuccessor` | Least later low-clock selection packages the stream into consecutive same-target macro successors. |
| 2026-09-01 | `PROVED-PAPER` | fixed-history preload reduction in `RESET_REPAYMENT_AUDIT_2026-09-01.md` | If every blocker used before repayment were already first-seen before the reset start, blocker one-use and finite pigeonhole would force repayment. |
| 2026-09-01 | `REFUTED` | `ruby experiments/target_reset_preload_counterexample.rb 1200` | After reset `6→14` at start 54, blocker 199 is first generated at clock 65 while entry stays at least 14; local fixed-history preload is false under exact greedy continuation. |
| 2026-09-01 | `COMPUTED` | discovery `target_reset_repayment_probe.rb 5000 200 10000 20260901` | 31,894 upward macros: 31,259 repaid, 337 ended by target occurrence, 298 horizon-censored; maximum resolved wait 9 episodes. |
| 2026-09-01 | `COMPUTED` | holdout `target_reset_repayment_probe.rb 1000 200 50000 20260902` | 8,753 upward macros: 8,652 repaid, 77 target-ended, 24 end-censored; no mature censor and maximum resolved wait 9. |

## Semantic audit

- Informal statement implies formal statement: yes, the stream retains the universal fixed-root
  no-escape property, every selected witness retains its target-low start, and consecutive
  witnesses can be packaged as `TargetMacroSuccessor`.
- Formal statement implies intended consequence: yes; the returned entry is a fresh target-low
  terminal episode strictly below the reset blocker, with no waiting bound.  It does not by itself
  prove fixed-root escape without an additional nested-anchor or strict-drift assembly.
- Counterfactual examples that should make the statement false: a right-moving singleton ladder
  with no actual-history gate; an eventual-high tail with no later low episode.
- Could the theorem be proved from weaker or vacuous assumptions?: the provenance-repaired stream
  decomposition can; the repayment hypothesis must not be credited if it follows only because a
  contradictory target-occurrence or coverage oracle was smuggled into the assumptions.
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: the
  old `UnboundedRightTerminalStream` omitted both target-low provenance and the universal form of
  fixed-root no-escape, retaining it only on selected witnesses.  The proposed conjunction repairs
  both omissions.  `TargetMacroSuccessor` supplies actual orbit, freshness, chronology, and the
  no-intermediate-low condition.
- Exact falsification status: no finite computation can instantiate the permanent-missing and
  unbounded-stream antecedent.  The exact conjecture is not refuted; the branch is stopped because
  every independently testable causal bridge found in this round was refuted or became equivalent
  to repayment/target occurrence.

## Decision

- Continue / formalize / refute / stop: `STOPPED`.  Keep the exact statement `CONJECTURED` as a
  mathematical possibility, but do not implement it as a Lean assumption or spend another local
  macro cycle on it.
- Reason: the repaired interface and successor selection are complete.  The only finite-capacity
  proof route requires fixed-history blocker preload, which is refuted by an exact greedy seeded
  continuation.  Adding permanent-tail birth finiteness repairs the statement only by restating
  repayment or target occurrence.
- Reopen only if: a single independently testable global invariant bounds post-reset blocker births
  and excludes both the right-ladder and the seeded preload counterexample without mentioning
  future return, target occurrence, or canonical reachability.
