import Recaman.DowncrossBudgetGap

namespace Recaman

/-! # Closing the generic extended-history budget residual

A strict decrease of `missingBelowCount` has a concrete converse: some value
below the target was absent at the representative time and present at the
later history horizon.  Starting from an occurrence of that value, a future
upcrossing supplies a crossing-recovery node whose anchor is strictly below
the old above-target representative anchor.  Enlarging the real history
horizon then gives a semantic phase-search step with the existing rank.
-/

/-- Converse to `missingBelowCount_strict_of_new` along the actual monotone
history: every strict budget decrease is caused by at least one newly seen
value below the target. -/
theorem exists_newBelow_of_missingBelowCount_strict
    {target earlier later : Nat}
    (htime : earlier ≤ later)
    (hstrict : missingBelowCount target later <
      missingBelowCount target earlier) :
    ∃ value, value < target ∧
      value ∉ valuesThrough earlier ∧ value ∈ valuesThrough later := by
  induction target with
  | zero => simp at hstrict
  | succ target ih =>
      by_cases hearlier : target ∈ valuesThrough earlier
      · have hlater : target ∈ valuesThrough later :=
          valuesThrough_mono htime hearlier
        simp only [missingBelowCount_succ, if_pos hearlier,
          if_pos hlater, Nat.add_zero] at hstrict
        rcases ih hstrict with ⟨value, hvalueTarget, hnew, hseen⟩
        exact ⟨value, by omega, hnew, hseen⟩
      · by_cases hlater : target ∈ valuesThrough later
        · exact ⟨target, by omega, hearlier, hlater⟩
        · simp only [missingBelowCount_succ, if_neg hearlier,
            if_neg hlater] at hstrict
          rcases ih (by omega) with ⟨value, hvalueTarget, hnew, hseen⟩
          exact ⟨value, by omega, hnew, hseen⟩

/-- A budget decrease therefore exposes an actual below-target occurrence
strictly after the representative time and no later than the history
horizon. -/
theorem exists_newBelow_occurrence_of_missingBelowCount_strict
    {target representativeTime historyHorizon : Nat}
    (htime : representativeTime ≤ historyHorizon)
    (hstrict : missingBelowCount target historyHorizon <
      missingBelowCount target representativeTime) :
    ∃ value occurrenceTime,
      value < target ∧
      representativeTime < occurrenceTime ∧
      occurrenceTime ≤ historyHorizon ∧
      a occurrenceTime = value ∧
      value ∉ valuesThrough representativeTime ∧
      value ∈ valuesThrough historyHorizon := by
  rcases exists_newBelow_of_missingBelowCount_strict htime hstrict with
    ⟨value, hvalueTarget, hnew, hseen⟩
  rcases mem_valuesThrough_iff.mp hseen with
    ⟨occurrenceTime, hoccurrenceHorizon, hvalue⟩
  have hrepresentativeOccurrence : representativeTime < occurrenceTime := by
    by_cases hoccurrenceRepresentative : occurrenceTime ≤ representativeTime
    · exact False.elim (hnew (mem_valuesThrough_iff.mpr
        ⟨occurrenceTime, hoccurrenceRepresentative, hvalue⟩))
    · omega
  exact ⟨value, occurrenceTime, hvalueTarget, hrepresentativeOccurrence,
    hoccurrenceHorizon, hvalue, hnew, hseen⟩

/-- A generic budget-gap extended-history node has a semantic strict step.

The proof does not transport the representative's local child through the
budget gap.  Instead it uses the newly exposed below-target occurrence,
waits for its next upcrossing, and stores that crossing in the dedicated
semantic recovery constructor. -/
theorem ExtendedHistoryNormalCertificate.phaseSemanticStep_of_budgetGap
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder)
    (hgap : missingBelowCount target node.horizon <
      missingBelowCount target representativeTime) :
    (∃ witness, a witness = target) ∨
      ∃ next, PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next node := by
  rcases exists_newBelow_occurrence_of_missingBelowCount_strict
      h.representative_le_horizon hgap with
    ⟨value, occurrenceTime, hvalueTarget, hrepresentativeOccurrence,
      hoccurrenceHorizon, hvalue, hnew, hseen⟩
  have hbelow : a occurrenceTime < target := by
    rw [hvalue]
    exact hvalueTarget
  rcases exists_weakUpcrossingStep_from_below h.target_positive hbelow with
    ⟨crossingTime, hcrossing⟩
  by_cases htargetSeen : target ∈ valuesThrough crossingTime
  · rcases mem_valuesThrough_iff.mp htargetSeen with
      ⟨witness, _, htargetValue⟩
    exact Or.inl ⟨witness, htargetValue⟩
  by_cases htargetEndpoint : a (crossingTime + 1) = target
  · exact Or.inl ⟨crossingTime + 1, htargetEndpoint⟩
  have htargetStrict : target < a (crossingTime + 1) :=
    Nat.lt_of_le_of_ne hcrossing.endpoint_ge (Ne.symm htargetEndpoint)
  have hnextValue := a_succ_of_not_canSubtract hcrossing.forced_addition
  have hdebtCrossing : DebtCrossing target (a (crossingTime + 1))
      crossingTime :=
    ⟨hcrossing.below, htargetStrict, hnextValue⟩
  rcases exists_coordinatesAt (n := crossingTime + 1) (by omega) with
    ⟨nextQuotient, nextRemainder, hnextCoordinates⟩
  let nextHorizon := max node.horizon (crossingTime + 2)
  let next : PhaseSearchNode :=
    ⟨nextHorizon, a crossingTime, .normal, a crossingTime⟩
  have hrepresentativeAnchor : a crossingTime < a representativeTime :=
    Nat.lt_of_lt_of_le hcrossing.below h.target_le_value
  have hrecovery : CrossingRecoveryInvariant target nextHorizon
      (a representativeTime) crossingTime nextQuotient nextRemainder := {
    target_missing := htargetSeen
    forced_addition := hcrossing.forced_addition
    crossing := hdebtCrossing
    coordinates := hnextCoordinates
    crossing_before_horizon := by
      exact Nat.lt_of_lt_of_le (by omega)
        (Nat.le_max_right node.horizon (crossingTime + 2))
    predecessor_lt_anchor := hrepresentativeAnchor
  }
  have hsemantic : PhaseSemanticInvariant target next := by
    apply PhaseSemanticInvariant.crossing_recovery
    exact ⟨a representativeTime, crossingTime, nextQuotient, nextRemainder, {
      target_positive := h.target_positive
      node_eq := rfl
      recovery := hrecovery
    }⟩
  have hprogress : PhaseSearchProgress target next node := by
    rw [h.node_eq]
    exact phaseSearchProgress_of_horizonAndAnchor
      (Nat.le_max_left node.horizon (crossingTime + 2))
      hrepresentativeAnchor
  exact Or.inr ⟨next, hsemantic, hprogress⟩

/-- Constructor-shaped wrapper: every literal `budget_transport` residual
from `ExtendedHistoryNormalCertificate.phaseSemanticStep_or_residual` is now
closed, independently of the local representative child stored in it. -/
theorem extendedHistory_budgetTransportResidual_phaseSemanticStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (certificate : ExtendedHistoryNormalCertificate target node
      representativeTime quotient remainder)
    (_representativeReady : target ≤ representativeTime + 1)
    (_localChild : PhaseSearchNode)
    (_localSemantic : PhaseSemanticInvariant target _localChild)
    (_localProgress : PhaseSearchProgress target _localChild
      (extendedHistoryRepresentativeNode representativeTime))
    (budgetGap : missingBelowCount target node.horizon <
      missingBelowCount target representativeTime) :
    (∃ witness, a witness = target) ∨
      ∃ next, PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next node :=
  certificate.phaseSemanticStep_of_budgetGap budgetGap

/-- After closing budget transport, the only residual of the minimal generic
extended-history certificate is failure of target readiness at the
representative time. -/
inductive ExtendedHistoryReadinessResidual
    (target : Nat) (node : PhaseSearchNode) : Prop
  | representative_not_ready
      (representativeTime quotient remainder : Nat)
      (certificate : ExtendedHistoryNormalCertificate target node
        representativeTime quotient remainder)
      (not_ready : representativeTime + 1 < target)
      (value_strictly_above : target < a representativeTime) :
      ExtendedHistoryReadinessResidual target node

/-- Strengthened total classification of an extended-history normal node:
the former `budget_transport` branch is discharged by a fresh below-target
occurrence and crossing recovery. -/
theorem ExtendedHistoryNormalCertificate.phaseSemanticStep_or_readiness
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      ExtendedHistoryReadinessResidual target node := by
  rcases h.phaseSemanticStep_or_residual with hoccurs | hstep | hresidual
  · exact Or.inl hoccurs
  · exact Or.inr (Or.inl hstep)
  · cases hresidual with
    | representative_not_ready representativeTime quotient remainder
        certificate hnotReady habove =>
        exact Or.inr (Or.inr (.representative_not_ready
          representativeTime quotient remainder certificate hnotReady
          habove))
    | budget_transport representativeTime quotient remainder certificate
        hready child hsemantic hlocal hgap =>
        rcases certificate.phaseSemanticStep_of_budgetGap hgap with
          hoccurs | hstep
        · exact Or.inl hoccurs
        · exact Or.inr (Or.inl hstep)

end Recaman
