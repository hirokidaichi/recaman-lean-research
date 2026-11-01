import Recaman.PermanentAboveCorridorOuterHistory
import Recaman.DebtSubtraction
import Recaman.NormalPhase

namespace Recaman

noncomputable section

/-! # Generation transition of a terminal historical blocker

The first occurrence of a positive below-target blocker cannot be the initial
state.  Its actual generating transition is therefore either a legal
subtraction or a forced addition.  The subtraction branch exposes an earlier,
larger predecessor with first-occurrence provenance.  The addition branch is
entirely target bounded.

The landing value itself cannot inhabit the ordinary normal or debt semantic
domains, because both require a value at or above the target.  This records
the exact semantic boundary: a dedicated below-target historical/crossing
adapter is needed before the numerical backtrack edge can become a full
search step.
-/

/-- Exact generating transition of the blocker's first occurrence. -/
inductive TerminalHistoricalBlockerGeneration
    {target returnTime candidate firstTime : Nat}
    (blocker : TerminalHistoricalBlockerCertificate target returnTime
      candidate firstTime) : Prop
  | legal_subtraction
      (predecessor predecessorFirstTime : Nat)
      (legal : CanSubtract firstTime (stateAt (firstTime - 1)))
      (predecessor_eq : a (firstTime - 1) = predecessor)
      (predecessor_first : FirstAt a predecessor predecessorFirstTime)
      (predecessorFirstTime_lt : predecessorFirstTime < firstTime)
      (candidate_add_clock_eq : candidate + firstTime = predecessor)
      (candidate_fresh_before : candidate ∉ valuesThrough (firstTime - 1))
      (candidate_lt_predecessor : candidate < predecessor)
      (predecessor_target_position :
        predecessor < target ∨ target ≤ predecessor) :
      TerminalHistoricalBlockerGeneration blocker
  | forced_addition
      (predecessorFirstTime : Nat)
      (forced : ¬ CanSubtract firstTime (stateAt (firstTime - 1)))
      (candidate_eq_add : candidate =
        a (firstTime - 1) + firstTime)
      (predecessor_first : FirstAt a (a (firstTime - 1))
        predecessorFirstTime)
      (predecessorFirstTime_lt : predecessorFirstTime < firstTime)
      (predecessor_lt_candidate : a (firstTime - 1) < candidate)
      (predecessor_below_target : a (firstTime - 1) < target)
      (clock_below_target : firstTime < target)
      (forced_reason :
        a (firstTime - 1) ≤ firstTime ∨
          a (firstTime - 1) - firstTime ∈
            valuesThrough (firstTime - 1)) :
      TerminalHistoricalBlockerGeneration blocker

/-- The time-zero branch is impossible; the two actual transition branches
retain their strongest readily available provenance. -/
theorem TerminalHistoricalBlockerCertificate.generation
    {target returnTime candidate firstTime : Nat}
    (h : TerminalHistoricalBlockerCertificate target returnTime candidate
      firstTime) :
    TerminalHistoricalBlockerGeneration h := by
  rcases firstAt_final_transition h.candidate_first with
    hinitial | hlegal | hforced
  · rcases hinitial with ⟨htime, hvalue⟩
    have hpositive := h.candidate_positive
    omega
  · rcases hlegal with ⟨n, htime, hcan, hvalue⟩
    have htimePositive : 0 < firstTime := by omega
    have hcan' : CanSubtract firstTime (stateAt (firstTime - 1)) := by
      subst firstTime
      simpa using hcan
    rcases legalSubtraction_firstAt_predecessor h.candidate_first
        htimePositive hcan' with
      ⟨predecessor, predecessorFirstTime, hpredecessorEq,
        hpredecessorFirst, hpredecessorTime, hsum, hfresh, hlt⟩
    exact .legal_subtraction predecessor predecessorFirstTime hcan'
      hpredecessorEq hpredecessorFirst hpredecessorTime hsum hfresh hlt
      (Nat.lt_or_ge predecessor target)
  · rcases hforced with ⟨n, htime, hnot, hvalue, hreason⟩
    have htimePositive : 0 < firstTime := by omega
    have hforced' : ¬ CanSubtract firstTime
        (stateAt (firstTime - 1)) := by
      subst firstTime
      simpa using hnot
    have hcandidateEq : candidate =
        a (firstTime - 1) + firstTime := by
      subst firstTime
      simpa using hvalue
    rcases history_member_has_firstAt
        (current_mem_valuesThrough (firstTime - 1)) with
      ⟨predecessorFirstTime, hpredecessorTimeLe, hpredecessorFirst⟩
    have hpredecessorTime : predecessorFirstTime < firstTime := by omega
    have hpredecessorLt : a (firstTime - 1) < candidate := by
      rw [hcandidateEq]
      omega
    have hpredecessorBelow : a (firstTime - 1) < target :=
      Nat.lt_trans hpredecessorLt h.candidate_below_target
    have hcandidateBelow := h.candidate_below_target
    have hclockBelow : firstTime < target := by omega
    have hreason' :
        a (firstTime - 1) ≤ firstTime ∨
          a (firstTime - 1) - firstTime ∈
            valuesThrough (firstTime - 1) := by
      subst firstTime
      simpa using hreason
    exact .forced_addition predecessorFirstTime hforced' hcandidateEq
      hpredecessorFirst hpredecessorTime hpredecessorLt
      hpredecessorBelow hclockBelow hreason'

/-- A below-target blocker landing cannot itself be an ordinary normal
semantic state at its first-occurrence clock. -/
theorem TerminalHistoricalBlockerCertificate.not_normalPhaseInvariantAt
    {target returnTime candidate firstTime : Nat}
    (h : TerminalHistoricalBlockerCertificate target returnTime candidate
      firstTime)
    (node : PhaseSearchNode) (quotient remainder : Nat) :
    ¬ NormalPhaseInvariantAt target node firstTime quotient remainder := by
  intro hinvariant
  have hvalue := h.candidate_first.1
  have htargetLe := hinvariant.target_le_value
  have hcandidateBelow := h.candidate_below_target
  omega

/-- For the same reason, the blocker landing cannot be used directly as a
debt value, independently of the proposed horizon and anchor. -/
theorem TerminalHistoricalBlockerCertificate.not_debtInvariant
    {target returnTime candidate firstTime horizon anchor : Nat}
    (h : TerminalHistoricalBlockerCertificate target returnTime candidate
      firstTime) :
    ¬ DebtInvariant target ⟨horizon, anchor, .debt, firstTime⟩ candidate
      firstTime := by
  intro hinvariant
  exact Nat.not_le_of_gt h.candidate_below_target hinvariant.target_le

/-- Typed semantic boundary retained together with the complete generating
transition. -/
structure TerminalHistoricalBlockerSemanticBoundary
    (target returnTime candidate firstTime : Nat) : Prop where
  blocker : TerminalHistoricalBlockerCertificate target returnTime candidate
    firstTime
  generation : TerminalHistoricalBlockerGeneration blocker
  not_normal : ∀ node quotient remainder,
    ¬ NormalPhaseInvariantAt target node firstTime quotient remainder
  not_debt : ∀ horizon anchor,
    ¬ DebtInvariant target ⟨horizon, anchor, .debt, firstTime⟩ candidate
      firstTime

/-- Every terminal historical blocker reaches the explicit semantic boundary
above. -/
theorem TerminalHistoricalBlockerCertificate.semanticBoundary
    {target returnTime candidate firstTime : Nat}
    (h : TerminalHistoricalBlockerCertificate target returnTime candidate
      firstTime) :
    TerminalHistoricalBlockerSemanticBoundary target returnTime candidate
      firstTime := {
  blocker := h
  generation := h.generation
  not_normal := h.not_normalPhaseInvariantAt
  not_debt := fun _ _ => h.not_debtInvariant
}

/-- Both outer historical branches inherit the same generation and semantic
boundary through their common blocker certificate. -/
theorem TerminalOuterHistoricalBlockerCertificate.semanticBoundary
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (h : TerminalOuterHistoricalBlockerCertificate source freshEndpoint
      candidate firstTime) :
    TerminalHistoricalBlockerSemanticBoundary target source.returnTime
      candidate firstTime :=
  h.blocker.semanticBoundary

end

end Recaman
