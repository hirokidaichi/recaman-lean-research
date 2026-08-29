import Recaman.PermanentAboveCorridorFixedPointFloorTwo

namespace Recaman

noncomputable section

/-! # Summit theorem for a least missing target

The whole closed analysis composes from a least missing target: it yields a
permanent tail, a combined certificate, and hence the unified terminal
outcome.  Both fixed-point branches carry the missing-target field, so the
shared kernel floors apply uniformly.  The summit statement needs no
intermediate vocabulary: a least missing target hands the outer recursion a
semantic phase child, or a fixed-point core whose crossing clock is at
least eighteen unless the target is exactly nineteen — and whose target is
at least nineteen in every case.

In particular, the surjectivity conjecture is now equivalent to breaking
this single floored core, and any counterexample below nineteen is already
impossible without further hypotheses.
-/

/-- Floors extracted from either fixed-point branch of the unified
outcome. -/
theorem PermanentTailUnifiedOutcome.semantic_or_flooredCore
    {target start : Nat}
    (h : PermanentTailUnifiedOutcome target start) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        (18 ≤ crossingTime ∨ target = 19) ∧ 19 ≤ target) := by
  cases h with
  | semantic_progress stepParent child semantic progress =>
      exact Or.inl ⟨stepParent, child, semantic, progress⟩
  | discharge_replay replayParent replaySource replay core =>
      have hmissing := replay.target_missing
      exact Or.inr ⟨replayParent, replay.crossingTime, core,
        core.eighteen_le_crossingTime_or_target_eq_nineteen hmissing,
        core.nineteen_le_target hmissing⟩
  | landing_cycle parent minimumTime predecessorFirstTime combined value
      landingTime crossingTime value_below landing_first next_crossing
      crossing_before_start core =>
      have hmissing := combined.tail.target_missing
      exact Or.inr ⟨parent, crossingTime, core,
        core.eighteen_le_crossingTime_or_target_eq_nineteen hmissing,
        core.nineteen_le_target hmissing⟩

/-- Summit: a least missing target yields a semantic phase child or a
floored fixed-point core. -/
theorem LeastMissingTarget.semantic_or_flooredCore
    {target : Nat} (h : LeastMissingTarget target) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨
    (∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore target parent crossingTime,
        (18 ≤ crossingTime ∨ target = 19) ∧ 19 ≤ target) := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨crossingNode, minimumTime, predecessorFirstTime, hcombined⟩
  exact hcombined.unifiedOutcome.semantic_or_flooredCore

/-- Any least missing target is at least nineteen or hands the outer
recursion a semantic phase child. -/
theorem LeastMissingTarget.semanticProgress_or_nineteen_le
    {target : Nat} (h : LeastMissingTarget target) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨ 19 ≤ target := by
  rcases h.semantic_or_flooredCore with hsemantic | hfixed
  · exact Or.inl hsemantic
  · rcases hfixed with ⟨_, _, _, _, htarget⟩
    exact Or.inr htarget

end

end Recaman
