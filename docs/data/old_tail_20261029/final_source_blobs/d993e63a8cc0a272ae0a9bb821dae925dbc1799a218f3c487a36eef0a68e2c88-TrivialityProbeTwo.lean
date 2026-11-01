import Recaman.LandingFloorThirtytwo
import Recaman.CrossingReadinessClosure
import Recaman.PinnedConfigurationAttack

namespace Recaman

noncomputable section

/-! # Second adversarial probe round

Positive constructions measuring the content of the newest statements.

* The right branch of `LeastMissingTarget.semantic_or_thirtytwo` is
  inhabitable, so the summit floor is not vacuously true on that side: a
  concrete `TailFixedPointCore` with clock thirty-two exists.
* `PinnedTailMinimumConfiguration` separates sharply into its four
  enumerable fields, which are satisfiable at concrete clocks, and its
  `target_missing` field, which refutes every small candidate.  A count of
  candidates satisfying the first four fields is therefore not a count of
  inhabitants.
* The purified global residual is literally the goal: tail return at every
  target is equivalent to surjectivity.
* The strengthened non-crossing step implies the canonical refined step, so
  the reorganisation of `OrbitReadyDirectRefined` weakened nothing.
-/

set_option maxRecDepth 100000 in
/-- The right branch of `semantic_or_thirtytwo` is inhabitable. -/
theorem probe_fixedPointCore_thirtytwo_inhabited :
    ∃ (parent : PhaseSearchNode) (crossingTime : Nat),
      ∃ _core : TailFixedPointCore 50 parent crossingTime,
        32 ≤ crossingTime ∧ 19 ≤ 50 :=
  ⟨⟨0, 46, .normal, 46⟩, 32, {
    anchor_eq := by decide
    below := by decide
    endpoint_ge := by decide
    forced := by decide
    node_reproduction := by decide }, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- The four enumerable fields of the pinned configuration are satisfiable. -/
theorem probe_pinned_enumerable_fields_at_21 :
    FirstAt a (62 + 1) 21 ∧ CanSubtract 22 (stateAt 21) ∧
      CanSubtract 23 (stateAt 22) ∧ 2 * 21 + 2 < 62 := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
/-- Yet the configuration itself is refuted by its own missing-target field. -/
theorem probe_not_pinned_62_21 :
    ¬ PinnedTailMinimumConfiguration 62 21 := by
  intro h
  exact h.target_missing ⟨19, by decide⟩

set_option maxRecDepth 100000 in
/-- The same at the next candidate clock: the pattern is not a one-off. -/
theorem probe_not_pinned_113_36 :
    ¬ PinnedTailMinimumConfiguration 113 36 := by
  intro h
  exact h.target_missing ⟨34, by decide⟩

/-- Purified hypothesis equals the goal. -/
theorem probe_targetTailReturn_iff_surjective :
    (∀ target, TargetTailReturnHypothesis target) ↔
      (∀ target, ∃ time, a time = target) := by
  constructor
  · exact surjective_of_targetTailReturn
  · intro hsurj target _ _
    exact Or.inl (hsurj target)

/-- The strengthened step implies the canonical one: nothing was weakened. -/
theorem probe_nonCrossing_implies_refinedStep
    {target : Nat} {parent : PhaseSearchNode}
    (h : OrbitReadyNormalInvariant target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child parent := by
  rcases h.nonCrossingRefinedStep with hoccurs | ⟨child, hchild, hprogress⟩
  · exact Or.inl hoccurs
  · refine Or.inr ⟨child, ?_, hprogress⟩
    rcases hchild with hready | hextended
    · exact Or.inl hready
    · exact Or.inr (Or.inl hextended)

end

end Recaman
