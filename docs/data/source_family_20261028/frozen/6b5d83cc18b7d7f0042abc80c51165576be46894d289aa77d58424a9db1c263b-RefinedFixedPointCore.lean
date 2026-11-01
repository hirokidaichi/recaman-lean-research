import Recaman.RefinedMountedIteration
import Recaman.LandingFloorThirtytwo

namespace Recaman

noncomputable section

/-! # Refined summit of the permanent-tail analysis

This is the last stage of the chain.  The unified terminal outcome is
restated with the certificate-tied `RefinedSemanticEdge` payload, and the
two fixed-point branches keep the thirty-two floor established by the
landing cursor and the replay kernel sweep.

The resulting summit replaces
`LeastMissingTarget.semantic_or_thirtytwo`, whose left disjunct is derivable
from `0 < target` alone: an existentially quantified step parent can be
manufactured above any node, and a positive target always owns a canonical
semantic node.  The refined left disjunct is not of that kind, and the last
section proves it: a `RefinedSemanticEdge` carries the permanent-tail
certificate that produced it, hence already entails that the target never
occurs.
-/

/-- Refinement of `PermanentTailUnifiedOutcome`. -/
inductive RefinedPermanentTailUnifiedOutcome (target start : Nat) : Prop
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      RefinedPermanentTailUnifiedOutcome target start
  | discharge_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource)
      (core : TailFixedPointCore target replayParent replay.crossingTime) :
      RefinedPermanentTailUnifiedOutcome target start
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
      RefinedPermanentTailUnifiedOutcome target start

/-- Refined form of `unifiedOutcome`. -/
theorem PermanentTailCombinedCertificate.refinedUnifiedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    RefinedPermanentTailUnifiedOutcome target start := by
  cases h.refinedMountedIterationOutcome with
  | refined_semantic edge =>
      exact .refined_semantic edge
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

/-- Both fixed-point branches of the refined outcome carry the thirty-two
floor: the replay by its own kernel sweep, the landing by the transported
history cursor. -/
theorem RefinedPermanentTailUnifiedOutcome.refinedSemantic_or_thirtytwo
    {target start : Nat} (h : RefinedPermanentTailUnifiedOutcome target start) :
    RefinedSemanticEdge target start ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) := by
  cases h with
  | refined_semantic edge =>
      exact Or.inl edge
  | discharge_replay replayParent replaySource replay core =>
      have hmissing := replay.target_missing
      have hfloor := replay.onehundredtwelve_le_crossingTime
      exact Or.inr ⟨replayParent, replay.crossingTime, core, by omega,
        core.nineteen_le_target hmissing⟩
  | landing_cycle parent minimumTime predecessorFirstTime combined value
      landingTime crossingTime value_below landing_first next_crossing
      crossing_before_start core landing_cursor =>
      have hmissing := combined.tail.target_missing
      exact Or.inr ⟨parent, crossingTime, core,
        landing_thirtytwo_le_crossingTime core hmissing next_crossing
          landing_cursor,
        core.nineteen_le_target hmissing⟩

/-- Refined summit: a least missing target hands the outer recursion a
certificate-tied refined semantic edge on its own permanent-above tail, or a
fixed-point core whose crossing clock is at least thirty-two and whose
target is at least nineteen. -/
theorem LeastMissingTarget.refinedSemanticEdge_or_flooredCore
    {target : Nat} (h : LeastMissingTarget target) :
    (∃ start : Nat, MissingPermanentAboveTail target start ∧
      RefinedSemanticEdge target start) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ target) := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨crossingNode, minimumTime, predecessorFirstTime, hcombined⟩
  rcases hcombined.refinedUnifiedOutcome.refinedSemantic_or_thirtytwo with
    hedge | hcore
  · exact Or.inl ⟨start, htail, hedge⟩
  · exact Or.inr hcore

/-! ## The left disjunct is not free

`RefinedDomainEdge` was shown to follow from `0 < target` alone.  The
certificate-tied edge cannot: both of its constructors store a
permanent-tail certificate whose tail field already states that the target
never occurs.
-/

/-- Every refined semantic edge entails that the target is missing. -/
theorem RefinedSemanticEdge.target_missing
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    ¬ ∃ time, a time = target := by
  cases h with
  | discharge_step _dischargeParent discharge _step =>
      exact discharge.combined.tail.target_missing
  | mounted_crossing _mountedParent _minimumTime _predecessorFirstTime
      _crossingTime combined _ready _progress =>
      exact combined.tail.target_missing

/-- Free-route probe.  Unlike the forgetful edge, the certificate-tied edge
is not derivable from positivity of the target: target one occurs at time
one, so no such edge exists for it. -/
theorem not_forall_pos_exists_refinedSemanticEdge :
    ¬ ∀ target : Nat, 0 < target →
        ∃ start : Nat, RefinedSemanticEdge target start := by
  intro hall
  rcases hall 1 (by omega) with ⟨_start, edge⟩
  exact edge.target_missing ⟨1, by decide⟩

/-- The same probe against the exact left disjunct of the refined summit. -/
theorem not_forall_pos_refinedSummitLeft :
    ¬ ∀ target : Nat, 0 < target →
        ∃ start : Nat, MissingPermanentAboveTail target start ∧
          RefinedSemanticEdge target start := by
  intro hall
  rcases hall 1 (by omega) with ⟨_start, _htail, edge⟩
  exact edge.target_missing ⟨1, by decide⟩

/-- Consequently the refined summit is informative in a way the broad one is
not: its left disjunct is equivalent, over a least missing target, to real
analysis output rather than to positivity. -/
theorem LeastMissingTarget.refinedSemanticEdge_or_flooredCore_nontrivial
    {target : Nat} (h : LeastMissingTarget target) :
    ((∃ start : Nat, MissingPermanentAboveTail target start ∧
        RefinedSemanticEdge target start) ∨
      (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
        ∃ _core : TailFixedPointCore target parent crossingTime,
          32 ≤ crossingTime ∧ 19 ≤ target)) ∧
    ¬ ∀ smaller : Nat, 0 < smaller →
        ∃ start : Nat, MissingPermanentAboveTail smaller start ∧
          RefinedSemanticEdge smaller start :=
  ⟨h.refinedSemanticEdge_or_flooredCore, not_forall_pos_refinedSummitLeft⟩

end

end Recaman
