import Recaman.ExtendedHistoryDirectRefined

namespace Recaman

/-! # The exact refined-oracle boundary

Orbit-ready current nodes, ready debt nodes, and extended-history normal
nodes now all have direct residual-free refined steps.  The only constructor
which does not yet have such a theorem is `CrossingSearchInvariant` itself.
This module packages that remaining obligation without widening it back to
arbitrary numeric phase-search nodes.
-/

/-- The one local theorem still needed to turn the refined domain into a
restricted phase-search oracle. -/
def CrossingRefinedStepHypothesis (target : Nat) : Prop :=
  ∀ node, CrossingSearchInvariant target node →
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node

/-- Constructor-complete audit of the refined domain.  Every non-crossing
constructor is discharged by a concrete theorem; a crossing node returns its
certificate verbatim as the exact remaining boundary. -/
theorem OrbitReadyRefinedInvariant.refinedStep_or_crossing
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : OrbitReadyRefinedInvariant target node) :
    ((∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      CrossingSearchInvariant target node := by
  rcases h with hready | hextended | hcrossing
  · rcases hready with hcurrent | ⟨value, firstTime, hdebt⟩
    · exact Or.inl hcurrent.refinedStep
    · rcases node with ⟨horizon, anchor, phase, loc⟩
      have hphase : phase = .debt := hdebt.debt.phase_eq
      have hlocal : loc = firstTime := hdebt.debt.local_eq
      subst phase
      subst loc
      exact Or.inl (hdebt.refinedStep htarget)
  · exact Or.inl hextended.refinedStep
  · exact Or.inr hcrossing

/-- Assuming only the crossing-local step, the full refined domain is a
restricted phase-search oracle. -/
theorem refinedPhaseSearchOracle_of_crossing
    {target : Nat} (htarget : 0 < target)
    (hcrossing : CrossingRefinedStepHypothesis target) :
    RestrictedPhaseSearchOracle target
      (OrbitReadyRefinedInvariant target) := by
  intro node hinvariant
  rcases hinvariant.refinedStep_or_crossing htarget with hstep | hresidual
  · exact hstep
  · exact hcrossing node hresidual

/-- Canonical starts enter the current component of the refined domain. -/
theorem targetStartInvariant_orbitReadyRefined
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : TargetStartInvariant target node) :
    OrbitReadyRefinedInvariant target node :=
  Or.inl (Or.inl (h.toOrbitReadyNormalInvariant htarget))

/-- The global occurrence theorem is now reduced to the single typed
crossing-local hypothesis above. -/
theorem crossingRefinedStepHypothesis_implies_occurs
    {target : Nat} (htarget : 0 < target)
    (hcrossing : CrossingRefinedStepHypothesis target) :
    ∃ witness, a witness = target := by
  exact targetStart_reaches_of_restrictedOracle htarget
    (OrbitReadyRefinedInvariant target)
    (fun node hstart =>
      targetStartInvariant_orbitReadyRefined htarget hstart)
    (refinedPhaseSearchOracle_of_crossing htarget hcrossing)

end Recaman
