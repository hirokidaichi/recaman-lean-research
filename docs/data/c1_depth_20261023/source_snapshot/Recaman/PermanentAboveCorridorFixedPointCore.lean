import Recaman.PermanentAboveCorridorMountedIteration

namespace Recaman

noncomputable section

/-! # Common core of the two terminal fixed points

The discharge replay and the landing fixed point look different — one closes
a historical discharge cycle, the other reproduces the parent from a fresh
history landing — but they share one numeric core: a crossing clock whose
value equals the parent anchor, which straddles the missing target by a
forced addition, and whose mounted node is literally the parent.

This module extracts that core and states the final unified outcome of the
whole permanent-tail analysis: a virtual counterexample either hands the
outer recursion a semantic phase child, or terminates in a parent-node
reproduction, with its full discharge or landing provenance attached.
-/

/-- Shared numeric core of both terminal fixed points: a canonical crossing
selection that reproduces the parent node. -/
structure TailFixedPointCore
    (target : Nat) (parent : PhaseSearchNode) (crossingTime : Nat) :
    Prop where
  anchor_eq : a crossingTime = parent.anchorParent
  below : a crossingTime < target
  endpoint_ge : target ≤ a (crossingTime + 1)
  forced : a (crossingTime + 1) = a crossingTime + (crossingTime + 1)
  node_reproduction : terminalPredecessorCrossingNode parent crossingTime =
    parent

/-- The discharge replay carries the shared core. -/
theorem TerminalExactDischargeReplayCertificate.fixedPointCore
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (r : TerminalExactDischargeReplayCertificate source) :
    TailFixedPointCore target parent r.crossingTime := {
  anchor_eq := r.anchor_eq
  below := r.crossing_straddles_target.1
  endpoint_ge := r.crossing_straddles_target.2
  forced := r.forced_addition_at_crossing
  node_reproduction := r.installed_node_eq
}

/-- Unified terminal outcome of the permanent-tail analysis. -/
inductive PermanentTailUnifiedOutcome
    (target start : Nat) : Prop
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailUnifiedOutcome target start
  | discharge_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource)
      (core : TailFixedPointCore target replayParent replay.crossingTime) :
      PermanentTailUnifiedOutcome target start
  | landing_cycle
      (parent : PhaseSearchNode)
      (minimumTime predecessorFirstTime : Nat)
      (combined : PermanentTailCombinedCertificate target start parent
        minimumTime predecessorFirstTime)
      (value landingTime crossingTime : Nat)
      (value_below : value < target)
      (landing_first : FirstAt a value landingTime)
      (next_crossing : FirstWeakUpcrossingStep target landingTime
        crossingTime)
      (crossing_before_start : crossingTime + 1 ≤ start)
      (core : TailFixedPointCore target parent crossingTime)
      (landing_cursor : TerminalHistoryCursor target landingTime) :
      PermanentTailUnifiedOutcome target start

/-- Final unified theorem: a missing-target permanent tail yields a semantic
phase child or a parent-node-reproducing fixed point with full provenance. -/
theorem PermanentTailCombinedCertificate.unifiedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    PermanentTailUnifiedOutcome target start := by
  cases h.mountedIterationOutcome with
  | semantic_progress stepParent child semantic progress =>
      exact .semantic_progress stepParent child semantic progress
  | exact_replay replayParent replaySource replay =>
      exact .discharge_replay replayParent replaySource replay
        replay.fixedPointCore
  | landing_fixed_point fixedParent mTime pTime combined childTime
      parentTime value landingTime crossingTime progress value_below
      landing_first next_crossing crossing_before_start ready anchor_eq
      node_eq after_parent landing_cursor =>
      have hcore : TailFixedPointCore target fixedParent crossingTime := {
        anchor_eq := anchor_eq
        below := next_crossing.crossing.below
        endpoint_ge := next_crossing.crossing.endpoint_ge
        forced :=
          a_succ_of_not_canSubtract next_crossing.crossing.forced_addition
        node_reproduction := node_eq
      }
      exact .landing_cycle fixedParent mTime pTime combined value
        landingTime crossingTime value_below landing_first next_crossing
        crossing_before_start hcore landing_cursor

end

end Recaman
