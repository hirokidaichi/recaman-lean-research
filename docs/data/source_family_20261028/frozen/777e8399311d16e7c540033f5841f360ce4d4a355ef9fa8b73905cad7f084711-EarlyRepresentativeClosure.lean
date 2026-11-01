import Recaman.EarlyRepresentative
import Recaman.DowncrossBudgetGap

namespace Recaman

/-! # Closing the early-representative legal downcross

The legal-downcross residual already has an actual below-target endpoint at
`representativeTime+1`.  A future weak upcrossing from that endpoint supplies
the existing `crossing_recovery` semantic state.  Its history horizon is
enlarged to `max node.horizon (crossingTime+2)`: history-budget monotonicity
then permits the extension, while the pre-crossing value is below the target
and hence strictly below the old representative anchor.  The anchor component
therefore supplies strict phase-search progress.

After this construction, only the forced-addition branch with an already-seen
below-target subtraction candidate remains from the early-representative
classification.
-/

/-- A legal early downcross always closes through a future crossing recovery.

The two budget inequalities stored by the original residual explain why
representative-local progress could not be transported.  The recovery takes
a different edge: it grows the real history horizon and strictly lowers the
anchor to the below-target pre-crossing value. -/
theorem EarlyRepresentativeResidual.legalDowncross_phaseSemanticStep
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
      ∃ child,
        CrossingSearchInvariant target child ∧
        PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases exists_weakUpcrossingStep_from_below
      certificate.extended.target_positive next_below_target with
    ⟨crossingTime, hcrossing⟩
  by_cases hseen : target ∈ valuesThrough crossingTime
  · rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
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
  have holdAnchor : node.anchorParent = a representativeTime := by
    simpa using congrArg PhaseSearchNode.anchorParent
      certificate.extended.node_eq
  have hanchorDrop : a crossingTime < a representativeTime := by
    exact Nat.lt_of_lt_of_le hcrossing.below
      certificate.extended.target_le_value
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
  have hcrossingInvariant : CrossingSearchInvariant target child := by
    exact ⟨a representativeTime, crossingTime, crossingQuotient,
      crossingRemainder, {
        target_positive := certificate.extended.target_positive
        node_eq := rfl
        recovery := hrecovery
      }⟩
  have hsemantic : PhaseSemanticInvariant target child :=
    .crossing_recovery hcrossingInvariant
  have hprogress : PhaseSearchProgress target child node := by
    rw [certificate.extended.node_eq]
    exact phaseSearchProgress_of_horizonAndAnchor
      (Nat.le_max_left _ _) hanchorDrop
  exact Or.inr ⟨child, hcrossingInvariant, hsemantic, hprogress⟩

/-- The single remaining early-representative obstruction after legal
downcross closure. -/
inductive EarlyRepresentativeForcedResidual
    (target : Nat) (node : PhaseSearchNode) : Prop
  | forced_below_candidate
      (representativeTime quotient remainder candidate : Nat)
      (certificate : EarlyRepresentativeCertificate target node
        representativeTime quotient remainder)
      (candidate_eq : candidate =
        a representativeTime - (representativeTime + 1))
      (candidate_positive : 0 < candidate)
      (candidate_below_target : candidate < target)
      (candidate_seen : candidate ∈ valuesThrough representativeTime)
      (forced : ¬ CanSubtract (representativeTime + 1)
        (stateAt representativeTime))
      (next_value : a (representativeTime + 1) =
        a representativeTime + (representativeTime + 1)) :
      EarlyRepresentativeForcedResidual target node

/-- Refined successful domain after closing legal downcrossing. -/
def EarlyClosureInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  EarlyRefinedInvariant target node ∨ CrossingSearchInvariant target node

/-- Refined early-representative classification with legal downcross removed.
Every successful child retains both its mechanism-specific refined invariant
and the broad semantic certificate.  Only the forced below-candidate chamber
remains. -/
theorem EarlyRepresentativeCertificate.refinedStep_or_forcedResidual
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      (∃ child, EarlyClosureInvariant target child ∧
        PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      EarlyRepresentativeForcedResidual target node := by
  cases h.classify with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | forward_child child hforward =>
      exact Or.inr (Or.inl ⟨child,
        Or.inl (Or.inl ⟨hforward.representativeTime,
          hforward.quotient, hforward.remainder, hforward.certificate⟩),
        hforward.semantic, hforward.progress⟩)
  | debt_child value firstTime child hchild hdebt hsemantic hprogress =>
      exact Or.inr (Or.inl ⟨child,
        Or.inl (Or.inr (Or.inr ⟨value, firstTime, hdebt⟩)),
        hsemantic, hprogress⟩)
  | residual hresidual =>
      cases hresidual with
      | legal_downcross representativeTime quotient remainder hcert hlegal
          hbelow hbudget hgap =>
          rcases EarlyRepresentativeResidual.legalDowncross_phaseSemanticStep
              hcert hlegal hbelow
              hbudget hgap with hoccurs |
              ⟨child, hcrossing, hsemantic, hprogress⟩
          · exact Or.inl hoccurs
          · exact Or.inr (Or.inl ⟨child, Or.inr hcrossing,
              hsemantic, hprogress⟩)
      | forced_below_candidate representativeTime quotient remainder
          candidate hcert hcandidate hpositive hbelow hseen hforced hnext =>
          exact Or.inr (Or.inr (.forced_below_candidate
            representativeTime quotient remainder candidate hcert
            hcandidate hpositive hbelow hseen hforced hnext))

/-- The concrete target-five early representative closes through the actual
weak crossing `a 4=2 → a 5=7`.  The recovery history horizon is six, the
pre-crossing anchor two is strictly below the old anchor six, and the target
is still missing before the crossing. -/
theorem earlyRepresentative_five_three_crossingClosure :
    let parent : PhaseSearchNode := ⟨4, a 3, .normal, a 3⟩
    let child : PhaseSearchNode := ⟨6, a 4, .normal, a 4⟩
    CrossingSearchInvariant 5 child ∧
      PhaseSemanticInvariant 5 child ∧
      PhaseSearchProgress 5 child parent := by
  let parent : PhaseSearchNode := ⟨4, a 3, .normal, a 3⟩
  let child : PhaseSearchNode := ⟨6, a 4, .normal, a 4⟩
  have hrecovery : CrossingRecoveryInvariant 5 6 (a 3) 4 1 2 := {
    target_missing := by decide
    forced_addition := by decide
    crossing := by
      unfold DebtCrossing
      exact ⟨by decide, by decide, by decide⟩
    coordinates := by constructor <;> decide
    crossing_before_horizon := by decide
    predecessor_lt_anchor := by decide
  }
  have hcrossing : CrossingSearchInvariant 5 child :=
    ⟨a 3, 4, 1, 2, {
      target_positive := by decide
      node_eq := rfl
      recovery := hrecovery
    }⟩
  have hsemantic : PhaseSemanticInvariant 5 child :=
    .crossing_recovery hcrossing
  have hprogress : PhaseSearchProgress 5 child parent := by
    exact phaseSearchProgress_of_horizonAndAnchor (by decide) (by decide)
  exact ⟨hcrossing, hsemantic, hprogress⟩

end Recaman
