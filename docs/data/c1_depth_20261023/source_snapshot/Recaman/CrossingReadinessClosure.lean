import Recaman.CrossingReadinessBridge

namespace Recaman

noncomputable section

/-! # Closing the crossing-readiness bridge

`CrossingReadinessBridge` reduced the unready-crossing leak to a single
audit predicate, `OrbitReadyNormalNonCrossingStep`, which asserted that the
orbit-ready current producer never emits a crossing-recovery child.  That
producer now returns its child constructor, so the predicate is a theorem
and every consequence of the bridge becomes hypothesis-free.

What is left is exactly one orbit statement.  For a positive target, the
tail-return property alone produces an occurrence witness; no clock
side-condition and no crossing-local step survive.
-/

/-- The audit predicate of the bridge is a theorem.  Its content is supplied
by `OrbitReadyNormalInvariant.nonCrossingRefinedStep`, whose child lands in
the ready current/debt or extended-history constructor. -/
theorem orbitReadyNormalNonCrossingStep (target : Nat) :
    OrbitReadyNormalNonCrossingStep target := by
  intro parent hparent
  rcases hparent.nonCrossingRefinedStep with
    hoccurs | ⟨child, hchild, hprogress⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child, hchild, hprogress⟩

/-! ## Hypothesis-free forms of the bridge -/

/-- Constructor-complete step inside the horizon-ready refined domain.  The
only input left is the clock-preserving crossing-local step. -/
theorem ReadyRefinedInvariant.closedStep
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (hcrossing : ReadyCrossingReadyStepHypothesis target)
    (h : ReadyRefinedInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ child, ReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node :=
  h.readyStep htarget (orbitReadyNormalNonCrossingStep target) hcrossing

/-- The horizon-ready refined domain is a restricted phase-search oracle as
soon as the crossing-local step keeps the clock on its child. -/
theorem closedReadyRefinedPhaseSearchOracle
    {target : Nat} (htarget : 0 < target)
    (hcrossing : ReadyCrossingReadyStepHypothesis target) :
    RestrictedPhaseSearchOracle target (ReadyRefinedInvariant target) :=
  readyRefinedPhaseSearchOracle htarget
    (orbitReadyNormalNonCrossingStep target) hcrossing

/-- Hypothesis-free bridge: the clock-preserving crossing-local step alone
produces the target. -/
theorem readyCrossingReadyStepHypothesis_implies_occurs
    {target : Nat} (htarget : 0 < target)
    (hcrossing : ReadyCrossingReadyStepHypothesis target) :
    ∃ witness, a witness = target :=
  occurs_of_readyCrossingReadyStep htarget
    (orbitReadyNormalNonCrossingStep target) hcrossing

/-- Exact price of the remaining local step at a positive target. -/
theorem readyCrossingReadyStepHypothesis_iff_occurs
    {target : Nat} (htarget : 0 < target) :
    ReadyCrossingReadyStepHypothesis target ↔
      ∃ witness, a witness = target :=
  readyCrossingReadyStep_iff_occurs htarget
    (orbitReadyNormalNonCrossingStep target)

/-- Descent started at a horizon-ready semantic child, with the audit
predicate discharged. -/
theorem phaseSemanticChild_occurs_of_readyCrossingStep
    {target : Nat} (htarget : 0 < target)
    (hcrossing : ReadyCrossingReadyStepHypothesis target)
    {stepParent child : PhaseSearchNode}
    (hsemantic : PhaseSemanticInvariant target child)
    (hprogress : PhaseSearchProgress target child stepParent)
    (hready : target ≤ child.horizon + 1) :
    ∃ witness, a witness = target :=
  phaseSemanticChild_occurs_of_readyCrossingReadyStep htarget
    (orbitReadyNormalNonCrossingStep target) hcrossing hsemantic hprogress
    hready

/-! ## The remaining input is a single orbit statement -/

/-- Headline form.  At a positive target the tail-return property alone
yields an occurrence witness: the refined recursion, the horizon clock, and
the crossing-recovery constructor are all fully discharged. -/
theorem targetTailReturn_implies_occurs
    {target : Nat} (htarget : 0 < target)
    (hreturn : TargetTailReturnHypothesis target) :
    ∃ witness, a witness = target :=
  occurs_of_targetTailReturn htarget
    (orbitReadyNormalNonCrossingStep target) hreturn

/-- Equivalence at a positive target: tail return is neither weaker nor
stronger than the target occurring. -/
theorem targetTailReturn_iff_occurs
    {target : Nat} (htarget : 0 < target) :
    TargetTailReturnHypothesis target ↔ ∃ witness, a witness = target := by
  constructor
  · intro hreturn
    exact targetTailReturn_implies_occurs htarget hreturn
  · intro hoccurs _ _
    exact Or.inl hoccurs

/-- Full coverage now follows target by target.  Unlike
`all_targetTailReturn_implies_surjective`, this route uses no strong
induction and no least-counterexample detour: each target is closed by its
own recursion. -/
theorem surjective_of_targetTailReturn
    (hreturn : ∀ target, TargetTailReturnHypothesis target) :
    ∀ target, ∃ time, a time = target := by
  intro target
  by_cases hzero : target = 0
  · subst target
    exact ⟨0, by decide⟩
  · exact targetTailReturn_implies_occurs (by omega) (hreturn target)

end

end Recaman
