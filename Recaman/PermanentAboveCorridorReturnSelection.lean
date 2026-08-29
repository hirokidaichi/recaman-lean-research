import Recaman.PermanentAboveCorridorImmediateClosure

namespace Recaman

noncomputable section

/-! # Finite selection state for terminal return candidates

The explicit return-candidate list already supplies a decreasing
`target - return` rank when a later candidate is selected.  What it does not
supply is a semantic rule preventing repeated selection of the same clock.

This module separates that concern.  A selection state stores the candidates
not yet consumed.  Selecting a remaining candidate erases it and strictly
decreases list length.  The only residual is literal revisit of a candidate
which is globally valid but no longer remains.  Thus fresh selections are
finite independently of whether a later-clock rule is eventually proved.
-/

structure TerminalReturnSelectionState (target : Nat) : Type where
  remaining : List Nat
  remaining_candidates :
    ∀ returnTime, returnTime ∈ remaining →
      returnTime ∈ terminalReturnCandidates target

def initialTerminalReturnSelectionState
    (target : Nat) : TerminalReturnSelectionState target := {
  remaining := terminalReturnCandidates target
  remaining_candidates := fun _ h => h
}

theorem initialTerminalReturnSelectionState_length_le (target : Nat) :
    (initialTerminalReturnSelectionState target).remaining.length ≤ target :=
  terminalReturnCandidates_length_le target

def TerminalReturnSelectionProgress {target : Nat}
    (child parent : TerminalReturnSelectionState target) : Prop :=
  child.remaining.length < parent.remaining.length

theorem terminalReturnSelectionProgress_wellFounded (target : Nat) :
    WellFounded (@TerminalReturnSelectionProgress target) := by
  apply WellFounded.intro
  intro state
  generalize hrank : state.remaining.length = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing state with
  | intro rank _ ih =>
      apply Acc.intro state
      intro child hchild
      have hrelation : child.remaining.length < rank := by
        simpa [TerminalReturnSelectionProgress, hrank] using hchild
      exact ih child.remaining.length hrelation child rfl

/-- Remove one selected clock while preserving membership in the global
candidate list. -/
def TerminalReturnSelectionState.erase
    {target : Nat} (state : TerminalReturnSelectionState target)
    (returnTime : Nat) : TerminalReturnSelectionState target := {
  remaining := state.remaining.erase returnTime
  remaining_candidates := by
    intro candidate hmem
    exact state.remaining_candidates candidate (List.mem_of_mem_erase hmem)
}

/-- Proof-carrying fresh selection and its strict visited-list edge. -/
structure TerminalReturnFreshSelectionCertificate
    (target returnTime : Nat)
    (state : TerminalReturnSelectionState target) : Type where
  candidate_membership : returnTime ∈ terminalReturnCandidates target
  remaining_membership : returnTime ∈ state.remaining
  next_state : TerminalReturnSelectionState target
  next_state_eq : next_state = state.erase returnTime
  progress : TerminalReturnSelectionProgress next_state state

/-- Exact selection result: consume a fresh candidate or expose literal
revisit. -/
inductive TerminalReturnCandidateSelectionOutcome
    (target returnTime : Nat)
    (state : TerminalReturnSelectionState target) : Type
  | fresh
      (certificate : TerminalReturnFreshSelectionCertificate target
        returnTime state) :
      TerminalReturnCandidateSelectionOutcome target returnTime state
  | revisited
      (candidate_membership : returnTime ∈ terminalReturnCandidates target)
      (not_remaining : returnTime ∉ state.remaining) :
      TerminalReturnCandidateSelectionOutcome target returnTime state

noncomputable def TerminalReturnSelectionState.select
    {target returnTime : Nat}
    (state : TerminalReturnSelectionState target)
    (hcandidate : returnTime ∈ terminalReturnCandidates target) :
    TerminalReturnCandidateSelectionOutcome target returnTime state := by
  by_cases hremaining : returnTime ∈ state.remaining
  · have hlength :
        (state.remaining.erase returnTime).length <
          state.remaining.length := by
      rw [List.length_erase_of_mem hremaining]
      have hpositive := List.length_pos_of_mem hremaining
      omega
    exact .fresh {
      candidate_membership := hcandidate
      remaining_membership := hremaining
      next_state := state.erase returnTime
      next_state_eq := rfl
      progress := hlength
    }
  · exact .revisited hcandidate hremaining

/-- If a later candidate is selected, the existing remaining-clock rank also
decreases; this condition is independent of freshness-list progress. -/
theorem TerminalReturnFreshSelectionCertificate.laterProgress
    {target parentReturn childReturn : Nat}
    {state : TerminalReturnSelectionState target}
    (h : TerminalReturnFreshSelectionCertificate target childReturn state)
    (hparent : parentReturn ∈ terminalReturnCandidates target)
    (hlater : parentReturn < childReturn) :
    TerminalReturnCandidateProgress target childReturn parentReturn :=
  terminalReturnCandidateProgress_of_later hparent h.candidate_membership
    hlater

/-- Terminal outcome with the sole numeric branch passed through the finite
selection state. -/
inductive PermanentTailTerminalReturnSelectedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalReturnSelectionState target) : Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalReturnSelectedOutcome source state
  | finite_selection
      (terminalEndpoint : Nat)
      (finite : TerminalFiniteReturnWindowCertificate source
        terminalEndpoint)
      (selection : TerminalReturnCandidateSelectionOutcome target
        source.returnTime state) :
      PermanentTailTerminalReturnSelectedOutcome source state
  | immediate_semantic
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (outcome : ImmediateTerminalSemanticOutcome target source.downTime
        source.returnTime) :
      PermanentTailTerminalReturnSelectedOutcome source state
  | historical_complete
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalCompleteStepOutcome historical) :
      PermanentTailTerminalReturnSelectedOutcome source state

theorem PermanentTailDischargeReturnCertificate.terminalReturnSelectedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalReturnSelectionState target) :
    PermanentTailTerminalReturnSelectedOutcome h state := by
  cases h.terminalSemanticallyClosedOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | finite_return_candidate terminalEndpoint finite =>
      exact .finite_selection terminalEndpoint finite
        (state.select finite.candidate_membership)
  | immediate_semantic valley insufficient outcome =>
      exact .immediate_semantic valley insufficient outcome
  | historical_complete freshEndpoint candidate firstTime historical
      outcome =>
      exact .historical_complete freshEndpoint candidate firstTime historical
        outcome

end

end Recaman
