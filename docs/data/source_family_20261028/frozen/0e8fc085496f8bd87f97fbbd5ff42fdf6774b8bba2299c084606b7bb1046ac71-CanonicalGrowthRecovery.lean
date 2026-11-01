import Recaman.CanonicalComplete
import Recaman.CanonicalForcedGrowth

namespace Recaman

/-! # Canonical growth recovery

The level-one and level-two quotient-one residuals both make one forced
addition whose immediate state does not decrease the phase rank.  The common
forced-growth chamber proves that one further transition exposes a coverage
candidate.  This file packages that two-step result back into the public
canonical-start API.
-/

/-- The level-one forced residual closes after the common two-step lookahead. -/
theorem canonicalLevelOneForcedQOne_phaseSemanticStep
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (h : CanonicalLevelOneForcedQOneResidual target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent :=
  h.toForcedGrowthChamber.twoStep_phaseSemantic htarget

/-- The level-two forced residual closes by the same two-step mechanism. -/
theorem canonicalLevelTwoForced_phaseSemanticStep
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (h : CanonicalLevelTwoForcedResidual target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent :=
  h.toForcedGrowthChamber.twoStep_phaseSemantic htarget

/-- The integrated low-level residual is entirely discharged in the existing
semantic domain; no new search phase or rank component is required. -/
theorem canonicalForcedResidual_phaseSemanticStep
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (h : CanonicalForcedResidual target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent := by
  cases h with
  | level_one hone =>
      exact canonicalLevelOneForcedQOne_phaseSemanticStep htarget hone
  | level_two htwo =>
      exact canonicalLevelTwoForced_phaseSemanticStep htarget htwo

/-- Complete local oracle theorem for every canonical target start.  All sign
regions and all three low levels return a target witness or a semantic
phase-rank child. -/
theorem targetStartInvariant_phaseSemanticStep
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (hstart : TargetStartInvariant target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent := by
  rcases targetStartInvariant_phaseSemanticStep_or_forced htarget hstart with
    hoccurs | hchild | hforced
  · exact Or.inl hoccurs
  · exact Or.inr hchild
  · exact canonicalForcedResidual_phaseSemanticStep htarget hforced

end Recaman
