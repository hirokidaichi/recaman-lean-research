import Recaman.PermanentAboveCorridorReturnSelection

namespace Recaman

noncomputable section

/-! # Finite selection state for terminal crossing windows

Selecting only the return clock identifies distinct terminal suffixes which
end at the same clock.  The finite terminal certificate also bounds its
endpoint strictly below that clock.  We therefore refine the candidate key
to `(returnTime, terminalEndpoint)`.

Both coordinates range over explicit finite lists.  Erasing a fresh key
strictly decreases the remaining-list length.  A revisit now means literal
identity of the crossing-window interval; it no longer conflates different
endpoints at the same return clock.  The semantic identity of the installed
parent (anchor and old crossing cursor) is deliberately left as the next
provenance boundary.
-/

/-- Finite identity of a terminal all-forced crossing interval. -/
structure TerminalReturnWindowKey : Type where
  returnTime : Nat
  terminalEndpoint : Nat
deriving DecidableEq, Repr

/-- All interval keys allowed by the elementary terminal clock bounds. -/
def terminalReturnWindowKeys (target : Nat) : List TerminalReturnWindowKey :=
  (List.range target).flatMap fun returnTime =>
    (List.range returnTime).map fun terminalEndpoint =>
      ⟨returnTime, terminalEndpoint⟩

theorem mem_terminalReturnWindowKeys_iff
    {target : Nat} {key : TerminalReturnWindowKey} :
    key ∈ terminalReturnWindowKeys target ↔
      key.terminalEndpoint < key.returnTime ∧ key.returnTime < target := by
  rcases key with ⟨returnTime, terminalEndpoint⟩
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with
      ⟨candidateReturn, hreturnMem, hkeyMem⟩
    rcases List.mem_map.mp hkeyMem with
      ⟨candidateEndpoint, hendpointMem, hkey⟩
    have hreturnEq : candidateReturn = returnTime :=
      congrArg TerminalReturnWindowKey.returnTime hkey
    have hendpointEq : candidateEndpoint = terminalEndpoint :=
      congrArg TerminalReturnWindowKey.terminalEndpoint hkey
    subst candidateReturn
    subst candidateEndpoint
    exact ⟨List.mem_range.mp hendpointMem,
      List.mem_range.mp hreturnMem⟩
  · rintro ⟨hendpoint, hreturn⟩
    apply List.mem_flatMap.mpr
    exact ⟨returnTime, List.mem_range.mpr hreturn,
      List.mem_map.mpr
        ⟨terminalEndpoint, List.mem_range.mpr hendpoint, rfl⟩⟩

/-- A full finite-window certificate supplies its exact interval key. -/
theorem TerminalFiniteReturnWindowCertificate.key_mem
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (h : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    (⟨source.returnTime, terminalEndpoint⟩ : TerminalReturnWindowKey) ∈
      terminalReturnWindowKeys target := by
  apply mem_terminalReturnWindowKeys_iff.mpr
  exact ⟨h.window.certificate.endpoint_before_return,
    h.window.return_before_target⟩

/-- Candidate intervals not yet selected. -/
structure TerminalReturnWindowSelectionState (target : Nat) : Type where
  remaining : List TerminalReturnWindowKey
  remaining_candidates :
    ∀ key, key ∈ remaining → key ∈ terminalReturnWindowKeys target

def initialTerminalReturnWindowSelectionState
    (target : Nat) : TerminalReturnWindowSelectionState target := {
  remaining := terminalReturnWindowKeys target
  remaining_candidates := fun _ h => h
}

def TerminalReturnWindowSelectionProgress {target : Nat}
    (child parent : TerminalReturnWindowSelectionState target) : Prop :=
  child.remaining.length < parent.remaining.length

theorem terminalReturnWindowSelectionProgress_wellFounded (target : Nat) :
    WellFounded (@TerminalReturnWindowSelectionProgress target) := by
  apply WellFounded.intro
  intro state
  generalize hrank : state.remaining.length = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing state with
  | intro rank _ ih =>
      apply Acc.intro state
      intro child hchild
      have hrelation : child.remaining.length < rank := by
        simpa [TerminalReturnWindowSelectionProgress, hrank] using hchild
      exact ih child.remaining.length hrelation child rfl

def TerminalReturnWindowSelectionState.erase
    {target : Nat} (state : TerminalReturnWindowSelectionState target)
    (key : TerminalReturnWindowKey) :
    TerminalReturnWindowSelectionState target := {
  remaining := state.remaining.erase key
  remaining_candidates := by
    intro candidate hmem
    exact state.remaining_candidates candidate (List.mem_of_mem_erase hmem)
}

/-- Proof-carrying consumption of one previously unselected interval. -/
structure TerminalReturnWindowFreshSelectionCertificate
    (target : Nat) (key : TerminalReturnWindowKey)
    (state : TerminalReturnWindowSelectionState target) : Type where
  candidate_membership : key ∈ terminalReturnWindowKeys target
  remaining_membership : key ∈ state.remaining
  next_state : TerminalReturnWindowSelectionState target
  next_state_eq : next_state = state.erase key
  progress : TerminalReturnWindowSelectionProgress next_state state

/-- Exact interval selection: strict finite-state progress or literal window
revisit. -/
inductive TerminalReturnWindowSelectionOutcome
    (target : Nat) (key : TerminalReturnWindowKey)
    (state : TerminalReturnWindowSelectionState target) : Type
  | fresh
      (certificate : TerminalReturnWindowFreshSelectionCertificate target key
        state) :
      TerminalReturnWindowSelectionOutcome target key state
  | revisited
      (candidate_membership : key ∈ terminalReturnWindowKeys target)
      (not_remaining : key ∉ state.remaining) :
      TerminalReturnWindowSelectionOutcome target key state

noncomputable def TerminalReturnWindowSelectionState.select
    {target : Nat} {key : TerminalReturnWindowKey}
    (state : TerminalReturnWindowSelectionState target)
    (hcandidate : key ∈ terminalReturnWindowKeys target) :
    TerminalReturnWindowSelectionOutcome target key state := by
  by_cases hremaining : key ∈ state.remaining
  · have hlength :
        (state.remaining.erase key).length < state.remaining.length := by
      rw [List.length_erase_of_mem hremaining]
      have hpositive := List.length_pos_of_mem hremaining
      omega
    exact .fresh {
      candidate_membership := hcandidate
      remaining_membership := hremaining
      next_state := state.erase key
      next_state_eq := rfl
      progress := hlength
    }
  · exact .revisited hcandidate hremaining

/-- The finite return branch routed through exact crossing-window selection.
All other terminal branches remain semantically closed. -/
inductive PermanentTailTerminalWindowSelectedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalReturnWindowSelectionState target) : Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalWindowSelectedOutcome source state
  | finite_window_selection
      (terminalEndpoint : Nat)
      (finite : TerminalFiniteReturnWindowCertificate source
        terminalEndpoint)
      (selection : TerminalReturnWindowSelectionOutcome target
        ⟨source.returnTime, terminalEndpoint⟩ state) :
      PermanentTailTerminalWindowSelectedOutcome source state
  | immediate_semantic
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (outcome : ImmediateTerminalSemanticOutcome target source.downTime
        source.returnTime) :
      PermanentTailTerminalWindowSelectedOutcome source state
  | historical_complete
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalCompleteStepOutcome historical) :
      PermanentTailTerminalWindowSelectedOutcome source state

theorem PermanentTailDischargeReturnCertificate.terminalWindowSelectedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalReturnWindowSelectionState target) :
    PermanentTailTerminalWindowSelectedOutcome h state := by
  cases h.terminalSemanticallyClosedOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | finite_return_candidate terminalEndpoint finite =>
      exact .finite_window_selection terminalEndpoint finite
        (state.select finite.key_mem)
  | immediate_semantic valley insufficient outcome =>
      exact .immediate_semantic valley insufficient outcome
  | historical_complete freshEndpoint candidate firstTime historical
      outcome =>
      exact .historical_complete freshEndpoint candidate firstTime historical
        outcome

/-- What remains after an exact finite-window revisit: the interval is
identified, while its installed parent/cursor identity is not part of the
finite key. -/
structure TerminalReturnWindowRevisitResidual
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (state : TerminalReturnWindowSelectionState target) : Type where
  interval_revisited :
    (⟨source.returnTime, terminalEndpoint⟩ : TerminalReturnWindowKey) ∉
      state.remaining
  interval_candidate :
    (⟨source.returnTime, terminalEndpoint⟩ : TerminalReturnWindowKey) ∈
      terminalReturnWindowKeys target

/-- Information-preserving decomposition of exact interval selection. -/
inductive TerminalReturnWindowRefinedSelectionOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (state : TerminalReturnWindowSelectionState target) : Type
  | fresh
      (certificate : TerminalReturnWindowFreshSelectionCertificate target
        ⟨source.returnTime, terminalEndpoint⟩ state) :
      TerminalReturnWindowRefinedSelectionOutcome finite state
  | revisited
      (residual : TerminalReturnWindowRevisitResidual finite state) :
      TerminalReturnWindowRefinedSelectionOutcome finite state

noncomputable def TerminalReturnWindowSelectionOutcome.revisitResidual
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    {finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint}
    {state : TerminalReturnWindowSelectionState target}
    (h : TerminalReturnWindowSelectionOutcome target
      ⟨source.returnTime, terminalEndpoint⟩ state) :
    TerminalReturnWindowRefinedSelectionOutcome finite state := by
  cases h with
  | fresh certificate => exact .fresh certificate
  | revisited candidate_membership not_remaining =>
      exact .revisited {
        interval_revisited := not_remaining
        interval_candidate := candidate_membership
      }

end

end Recaman
