import Recaman.CrossingFrontierRefined

namespace Recaman

/-! # Direct refined closure of extended-history normal nodes

The broad extended-history completion theorem constructs proof-carrying
children and then immediately forgets their clock data through
`PhaseSemanticInvariant`.  This module keeps that data at the generating
branches.  A common future-upcrossing adapter handles all three historical
budget mechanisms which start from an actual below-target value.
-/

/-- Starting from any actual below-target state, the next weak upcrossing is
either a target occurrence or a crossing-recovery child.  The child extends
the real history horizon and lowers the historical normal anchor, so the
existing phase rank decreases without transporting a local step across a
budget gap. -/
theorem extendedNormal_crossingRecovery_refinedStep_from_below
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime startTime : Nat}
    (htarget : 0 < target)
    (hnode : node =
      ⟨node.horizon, a representativeTime, .normal,
        a representativeTime⟩)
    (htargetValue : target ≤ a representativeTime)
    (hbelow : a startTime < target) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases exists_weakUpcrossingStep_from_below htarget hbelow with
    ⟨crossingTime, hcrossing⟩
  by_cases hseen : target ∈ valuesThrough crossingTime
  · rcases mem_valuesThrough_iff.mp hseen with
      ⟨witness, _, hvalue⟩
    exact Or.inl ⟨witness, hvalue⟩
  by_cases hequal : a (crossingTime + 1) = target
  · exact Or.inl ⟨crossingTime + 1, hequal⟩
  have hstrict : target < a (crossingTime + 1) :=
    Nat.lt_of_le_of_ne hcrossing.endpoint_ge (Ne.symm hequal)
  have hforcedValue :=
    a_succ_of_not_canSubtract hcrossing.forced_addition
  have hdebtCrossing : DebtCrossing target
      (a (crossingTime + 1)) crossingTime :=
    ⟨hcrossing.below, hstrict, hforcedValue⟩
  rcases exists_coordinatesAt (n := crossingTime + 1) (by omega) with
    ⟨crossingQuotient, crossingRemainder, hcoordinates⟩
  let historyHorizon := max node.horizon (crossingTime + 2)
  let child : PhaseSearchNode :=
    ⟨historyHorizon, a crossingTime, .normal, a crossingTime⟩
  have hanchorDrop : a crossingTime < a representativeTime :=
    Nat.lt_of_lt_of_le hcrossing.below htargetValue
  have hrecovery : CrossingRecoveryInvariant target historyHorizon
      (a representativeTime) crossingTime crossingQuotient
      crossingRemainder := {
    target_missing := hseen
    forced_addition := hcrossing.forced_addition
    crossing := hdebtCrossing
    coordinates := hcoordinates
    crossing_before_horizon := by
      simp only [historyHorizon]
      exact Nat.lt_of_lt_of_le (by omega)
        (Nat.le_max_right node.horizon (crossingTime + 2))
    predecessor_lt_anchor := hanchorDrop
  }
  have hcrossingInvariant : CrossingSearchInvariant target child :=
    ⟨a representativeTime, crossingTime, crossingQuotient,
      crossingRemainder, {
        target_positive := htarget
        node_eq := rfl
        recovery := hrecovery
      }⟩
  have hprogress : PhaseSearchProgress target child node := by
    rw [hnode]
    exact phaseSearchProgress_of_horizonAndAnchor
      (Nat.le_max_left _ _) hanchorDrop
  exact Or.inr ⟨child, Or.inr (Or.inr hcrossingInvariant), hprogress⟩

/-- A strict history-budget gap exposes a new below-target occurrence.  Its
future upcrossing gives a refined crossing child directly. -/
theorem ExtendedHistoryNormalCertificate.refinedStep_of_budgetGap
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder)
    (hgap : missingBelowCount target node.horizon <
      missingBelowCount target representativeTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases exists_newBelow_occurrence_of_missingBelowCount_strict
      h.representative_le_horizon hgap with
    ⟨value, occurrenceTime, hvalueTarget, _, _, hvalue, _, _⟩
  have hbelow : a occurrenceTime < target := by
    rw [hvalue]
    exact hvalueTarget
  exact extendedNormal_crossingRecovery_refinedStep_from_below
    h.target_positive h.node_eq h.target_le_value hbelow

/-- A legal early downcross supplies the below-target start directly. -/
theorem EarlyRepresentativeResidual.legalDowncross_refinedStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (certificate : EarlyRepresentativeCertificate target node
      representativeTime quotient remainder)
    (_legal : CanSubtract (representativeTime + 1)
      (stateAt representativeTime))
    (next_below_target : a (representativeTime + 1) < target)
    (_representative_to_next_budget_drop :
      missingBelowCount target (representativeTime + 1) <
        missingBelowCount target representativeTime)
    (_history_budget_gap :
      missingBelowCount target node.horizon <
        missingBelowCount target representativeTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node :=
  extendedNormal_crossingRecovery_refinedStep_from_below
    certificate.extended.target_positive certificate.extended.node_eq
    certificate.extended.target_le_value next_below_target

/-- An already-seen below-target blocked candidate supplies an earlier actual
start for the same future-upcrossing construction. -/
theorem EarlyRepresentativeResidual.forcedBelowCandidate_refinedStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder candidate : Nat}
    (certificate : EarlyRepresentativeCertificate target node
      representativeTime quotient remainder)
    (_candidate_eq : candidate =
      a representativeTime - (representativeTime + 1))
    (_candidate_positive : 0 < candidate)
    (candidate_below_target : candidate < target)
    (candidate_seen : candidate ∈ valuesThrough representativeTime)
    (_forced : ¬ CanSubtract (representativeTime + 1)
      (stateAt representativeTime))
    (_next_value : a (representativeTime + 1) =
      a representativeTime + (representativeTime + 1)) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases mem_valuesThrough_iff.mp candidate_seen with
    ⟨startTime, _, hstartValue⟩
  have hbelow : a startTime < target := by
    rw [hstartValue]
    exact candidate_below_target
  exact extendedNormal_crossingRecovery_refinedStep_from_below
    certificate.extended.target_positive certificate.extended.node_eq
    certificate.extended.target_le_value hbelow

/-- Complete refined step for an early representative.  Forward children
remain extended-history; debt children inherit the parent's ready history
horizon; both residual mechanisms enter crossing recovery. -/
theorem EarlyRepresentativeCertificate.refinedStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  cases h.classify with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | forward_child child hforward =>
      have hextended : ExtendedHistoryNormalInvariant target child :=
        ⟨hforward.representativeTime, hforward.quotient,
          hforward.remainder, hforward.certificate⟩
      exact Or.inr ⟨child, Or.inr (Or.inl hextended),
        hforward.progress⟩
  | debt_child value firstTime child hchild hdebt _ hprogress =>
      have hready : ReadyDebtInvariant target child value firstTime := {
        debt := hdebt
        horizon_ready := by
          rw [hchild]
          exact h.extended.horizon_time_ready
      }
      exact Or.inr ⟨child,
        Or.inl (Or.inr ⟨value, firstTime, hready⟩), hprogress⟩
  | residual hresidual =>
      cases hresidual with
      | legal_downcross representativeTime quotient remainder certificate
          legal hbelow hnextDrop hhistoryGap =>
          exact EarlyRepresentativeResidual.legalDowncross_refinedStep
            certificate legal hbelow hnextDrop hhistoryGap
      | forced_below_candidate representativeTime quotient remainder
          candidate certificate hcandidate hpositive hbelow hseen hforced
          hnext =>
          exact EarlyRepresentativeResidual.forcedBelowCandidate_refinedStep
            certificate hcandidate hpositive hbelow hseen hforced hnext

/-- Extended-history normal nodes are locally total in the refined domain.
Representative-ready stable nodes reuse the direct orbit-ready theorem;
budget gaps and early representatives use the typed upcrossing closures
above. -/
theorem ExtendedHistoryNormalCertificate.refinedStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : ExtendedHistoryNormalCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  by_cases hready : target ≤ representativeTime + 1
  · by_cases hstable : missingBelowCount target node.horizon =
        missingBelowCount target representativeTime
    · rcases (h.toOrbitReadyAtRepresentative hready).refinedStep with
        hoccurs | ⟨child, hchild, hprogress⟩
      · exact Or.inl hoccurs
      · exact Or.inr ⟨child, hchild,
          h.transportProgress_of_budgetStable hstable hprogress⟩
    · have hbudgetLe := missingBelowCount_antitone (m := target)
          h.representative_le_horizon
      have hgap : missingBelowCount target node.horizon <
          missingBelowCount target representativeTime := by omega
      exact h.refinedStep_of_budgetGap hgap
  · have hearly : EarlyRepresentativeCertificate target node
        representativeTime quotient remainder := {
      extended := h
      not_ready := by omega
    }
    exact hearly.refinedStep

/-- Existential packaging of complete refined extended-history closure. -/
theorem ExtendedHistoryNormalInvariant.refinedStep
    {target : Nat} {node : PhaseSearchNode}
    (h : ExtendedHistoryNormalInvariant target node) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases h with ⟨representativeTime, quotient, remainder, hcertificate⟩
  exact hcertificate.refinedStep

end Recaman
