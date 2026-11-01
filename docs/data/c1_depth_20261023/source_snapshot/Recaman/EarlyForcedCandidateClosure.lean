import Recaman.EarlyRepresentative
import Recaman.DowncrossBudgetGap

namespace Recaman

/-! # Closing the early forced-candidate residual

In the `forced_below_candidate` branch, the blocked subtraction candidate is
already present before the above-target representative state.  Starting from
an occurrence of that below-target candidate and ending at the representative
there is a forced-addition upcrossing.  Its pre-crossing value is below the
target, hence strictly below the old representative anchor.

The crossing is stored at `max node.horizon (time+2)`.  This keeps all old
history, makes the crossing strictly earlier than the new horizon, and leaves
the existing four-component phase rank decreasing through its anchor field.
-/

/-- Total semantic closure of the forced below-target candidate branch. -/
theorem earlyForcedBelowCandidate_phaseSemanticStep
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
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node := by
  rcases mem_valuesThrough_iff.mp candidate_seen with
    ⟨start, hstartTime, hstartValue⟩
  have hstartBelow : a start < target := by
    rw [hstartValue]
    exact candidate_below_target
  rcases exists_weakUpcrossingStep_between hstartTime hstartBelow
      certificate.extended.target_le_value with
    ⟨time, hcross, _htimeRepresentative⟩
  by_cases hseen : target ∈ valuesThrough time
  · rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact Or.inl ⟨witness, hvalue⟩
  by_cases hequal : a (time + 1) = target
  · exact Or.inl ⟨time + 1, hequal⟩
  have hstrict : target < a (time + 1) :=
    Nat.lt_of_le_of_ne hcross.endpoint_ge (Ne.symm hequal)
  have hstep := a_succ_of_not_canSubtract hcross.forced_addition
  have hdebtCrossing : DebtCrossing target (a (time + 1)) time :=
    ⟨hcross.below, hstrict, hstep⟩
  rcases exists_coordinatesAt (n := time + 1) (by omega) with
    ⟨crossingQuotient, crossingRemainder, hcoordinates⟩
  let recoveryHorizon := max node.horizon (time + 2)
  let child : PhaseSearchNode :=
    ⟨recoveryHorizon, a time, .normal, a time⟩
  have hrecovery : CrossingRecoveryInvariant target recoveryHorizon
      (a representativeTime) time crossingQuotient crossingRemainder := {
    target_missing := hseen
    forced_addition := hcross.forced_addition
    crossing := hdebtCrossing
    coordinates := hcoordinates
    crossing_before_horizon := by
      dsimp only [recoveryHorizon]
      have := Nat.le_max_right node.horizon (time + 2)
      omega
    predecessor_lt_anchor :=
      Nat.lt_of_lt_of_le hcross.below
        certificate.extended.target_le_value
  }
  have hsemantic : PhaseSemanticInvariant target child := by
    apply PhaseSemanticInvariant.crossing_recovery
    exact ⟨a representativeTime, time, crossingQuotient,
      crossingRemainder, {
        target_positive := certificate.extended.target_positive
        node_eq := rfl
        recovery := hrecovery
      }⟩
  have hprogress : PhaseSearchProgress target child node := by
    rw [certificate.extended.node_eq]
    dsimp only [child, recoveryHorizon]
    apply phaseSearchProgress_of_horizonAndAnchor
    · exact Nat.le_max_left _ _
    · exact Nat.lt_of_lt_of_le hcross.below
        certificate.extended.target_le_value
  exact Or.inr ⟨child, hsemantic, hprogress⟩

/-- Constructor-shaped adapter: an inhabitant produced specifically by
`EarlyRepresentativeResidual.forced_below_candidate` closes semantically. -/
theorem EarlyRepresentativeResidual.forcedBelowCandidate_phaseSemanticStep
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder candidate : Nat}
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
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node :=
  earlyForcedBelowCandidate_phaseSemanticStep certificate candidate_eq
    candidate_positive candidate_below_target candidate_seen forced next_value

/-- Proof-relevant remainder after removing the forced-candidate branch. -/
inductive EarlyLegalDowncrossResidual
    (target : Nat) (node : PhaseSearchNode) : Prop
  | legal_downcross
      (representativeTime quotient remainder : Nat)
      (certificate : EarlyRepresentativeCertificate target node
        representativeTime quotient remainder)
      (legal : CanSubtract (representativeTime + 1)
        (stateAt representativeTime))
      (next_below_target : a (representativeTime + 1) < target)
      (representative_to_next_budget_drop :
        missingBelowCount target (representativeTime + 1) <
          missingBelowCount target representativeTime)
      (history_budget_gap :
        missingBelowCount target node.horizon <
          missingBelowCount target representativeTime) :
      EarlyLegalDowncrossResidual target node

/-- Exhaustive residual adapter: after this module, the only early
representative residual is the legal-subtraction downcross branch. -/
theorem EarlyRepresentativeResidual.phaseSemanticStep_or_legalDowncross
    {target : Nat} {node : PhaseSearchNode}
    (h : EarlyRepresentativeResidual target node) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      EarlyLegalDowncrossResidual target node := by
  cases h with
  | legal_downcross representativeTime quotient remainder certificate legal
      hbelow hnextDrop hhistoryGap =>
      exact Or.inr (Or.inr (.legal_downcross representativeTime quotient
        remainder certificate legal hbelow hnextDrop hhistoryGap))
  | forced_below_candidate representativeTime quotient remainder candidate
      certificate candidateEq candidatePositive candidateBelow candidateSeen
      forced nextValue =>
      rcases earlyForcedBelowCandidate_phaseSemanticStep certificate
          candidateEq candidatePositive candidateBelow candidateSeen forced
          nextValue with hoccurs | hchild
      · exact Or.inl hoccurs
      · exact Or.inr (Or.inl hchild)

/-- Adapter for the complete one-step early-representative classification.
All successful constructors and the forced-candidate residual now have a
semantic rank step; only legal downcross remains. -/
theorem EarlyRepresentativeOutcome.toPhaseSemanticStep_or_legalDowncross
    {target : Nat} {node : PhaseSearchNode}
    (h : EarlyRepresentativeOutcome target node) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      EarlyLegalDowncrossResidual target node := by
  cases h with
  | target_occurs witness hvalue => exact Or.inl ⟨witness, hvalue⟩
  | forward_child child hforward =>
      exact Or.inr (Or.inl
        ⟨child, hforward.semantic, hforward.progress⟩)
  | debt_child value firstTime child childEq hdebt hsemantic hprogress =>
      exact Or.inr (Or.inl ⟨child, hsemantic, hprogress⟩)
  | residual hresidual =>
      exact hresidual.phaseSemanticStep_or_legalDowncross

/-- Certificate-level classification with the forced-candidate branch
removed. -/
theorem EarlyRepresentativeCertificate.phaseSemanticStep_or_legalDowncross
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      EarlyLegalDowncrossResidual target node :=
  h.classify.toPhaseSemanticStep_or_legalDowncross

/-- Actual forced-candidate example.  At representative time six, target
eight is not clock-ready, `a 6 = 13`, and the blocked subtraction candidate
six was seen at time three.  The segment recovers across `7 → 13` at step
six, yielding a crossing-recovery child anchored at seven. -/
theorem earlyForcedCandidate_eight_six_actual :
    let node : PhaseSearchNode := ⟨7, a 6, .normal, a 6⟩
    let child : PhaseSearchNode := ⟨7, a 5, .normal, a 5⟩
    EarlyRepresentativeResidual 8 node ∧
      CrossingSearchInvariant 8 child ∧
      PhaseSearchProgress 8 child node := by
  let node : PhaseSearchNode := ⟨7, a 6, .normal, a 6⟩
  let child : PhaseSearchNode := ⟨7, a 5, .normal, a 5⟩
  have hextended : ExtendedHistoryNormalCertificate 8 node 6 2 1 := {
    target_positive := by decide
    node_eq := rfl
    representative_le_horizon := by decide
    horizon_time_ready := by decide
    target_le_value := by decide
    coordinates := by constructor <;> decide
  }
  have hearly : EarlyRepresentativeCertificate 8 node 6 2 1 := {
    extended := hextended
    not_ready := by decide
  }
  have hresidual : EarlyRepresentativeResidual 8 node :=
    .forced_below_candidate 6 2 1 6 hearly rfl (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hrecovery : CrossingRecoveryInvariant 8 7 13 5 2 1 := {
    target_missing := by decide
    forced_addition := by decide
    crossing := by
      unfold DebtCrossing
      exact ⟨by decide, by decide, by decide⟩
    coordinates := by constructor <;> decide
    crossing_before_horizon := by decide
    predecessor_lt_anchor := by decide
  }
  have hcrossing : CrossingSearchInvariant 8 child :=
    ⟨13, 5, 2, 1, {
      target_positive := by decide
      node_eq := rfl
      recovery := hrecovery
    }⟩
  have hprogress : PhaseSearchProgress 8 child node :=
    phaseSearchProgress_of_horizonAndAnchor (by decide) (by decide)
  exact ⟨hresidual, hcrossing, hprogress⟩

end Recaman
