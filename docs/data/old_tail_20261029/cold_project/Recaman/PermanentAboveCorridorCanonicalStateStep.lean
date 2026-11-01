import Recaman.PermanentAboveCorridorCanonicalMinimum

namespace Recaman

noncomputable section

/-! # Terminal total step with canonical finite-state provenance

All refinements of the finite return branch are now threaded through the
constructor-complete terminal outcome.  Since the semantic terminal outcome
is a proposition, the next selection state is exposed propositionally as an
existential strict edge.  This is exactly the interface needed by a later
well-founded induction: the child state and its decreasing relation remain
available without attempting to eliminate a proof into computational data.
-/

/-- Propositional, recursion-ready form of a fresh canonical-key selection. -/
def TerminalCanonicalTailHistoryFreshProgress
    (target horizon : Nat) (key : TerminalCanonicalTailHistoryKey)
    (state : TerminalCanonicalTailHistorySelectionState target horizon) :
    Prop :=
  ∃ nextState : TerminalCanonicalTailHistorySelectionState target horizon,
    nextState = state.erase key ∧
      TerminalCanonicalTailHistorySelectionProgress nextState state

theorem TerminalCanonicalTailHistoryFreshSelectionCertificate.toProgress
    {target horizon : Nat} {key : TerminalCanonicalTailHistoryKey}
    {state : TerminalCanonicalTailHistorySelectionState target horizon}
    (fresh : TerminalCanonicalTailHistoryFreshSelectionCertificate
      target horizon key state) :
    TerminalCanonicalTailHistoryFreshProgress target horizon key state :=
  ⟨fresh.next_state, fresh.next_state_eq, fresh.progress⟩

/-- Literal final residual after consuming every distinct numeric provenance
key at the fixed horizon. -/
structure TerminalCanonicalTailHistoryExactRevisitResidual
    (target horizon : Nat) (key : TerminalCanonicalTailHistoryKey)
    (state : TerminalCanonicalTailHistorySelectionState target horizon) :
    Prop where
  candidate_membership : key ∈ terminalCanonicalTailHistoryKeys target horizon
  not_remaining : key ∉ state.remaining

/-- Constructor-complete terminal step after installing the final finite
selection state. -/
inductive PermanentTailTerminalCanonicalStateStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalCanonicalTailHistorySelectionState target
      parent.horizon) : Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalCanonicalStateStepOutcome source state
  | finite_state_progress
      (terminalEndpoint : Nat)
      (finite : TerminalFiniteReturnWindowCertificate source
        terminalEndpoint)
      (progress : TerminalCanonicalTailHistoryFreshProgress target
        parent.horizon finite.canonicalTailHistoryKey state) :
      PermanentTailTerminalCanonicalStateStepOutcome source state
  | exact_canonical_revisit
      (terminalEndpoint : Nat)
      (finite : TerminalFiniteReturnWindowCertificate source
        terminalEndpoint)
      (residual : TerminalCanonicalTailHistoryExactRevisitResidual target
        parent.horizon finite.canonicalTailHistoryKey state) :
      PermanentTailTerminalCanonicalStateStepOutcome source state
  | immediate_semantic
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (outcome : ImmediateTerminalSemanticOutcome target source.downTime
        source.returnTime) :
      PermanentTailTerminalCanonicalStateStepOutcome source state
  | historical_complete
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalCompleteStepOutcome historical) :
      PermanentTailTerminalCanonicalStateStepOutcome source state

/-- Every terminal discharge either closes semantically, takes an existing
history/master edge, consumes a fresh canonical finite key, or exposes the
single exact canonical revisit residual. -/
theorem PermanentTailDischargeReturnCertificate.terminalCanonicalStateStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalCanonicalTailHistorySelectionState target
      parent.horizon) :
    PermanentTailTerminalCanonicalStateStepOutcome source state := by
  cases source.terminalSemanticallyClosedOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | finite_return_candidate terminalEndpoint finite =>
      cases finite.canonicalTailHistorySelection rfl state with
      | fresh fresh =>
          exact .finite_state_progress terminalEndpoint finite
            fresh.toProgress
      | exact_revisit candidate_membership not_remaining =>
          exact .exact_canonical_revisit terminalEndpoint finite {
            candidate_membership := candidate_membership
            not_remaining := not_remaining
          }
  | immediate_semantic valley insufficient outcome =>
      exact .immediate_semantic valley insufficient outcome
  | historical_complete freshEndpoint candidate firstTime historical
      outcome =>
      exact .historical_complete freshEndpoint candidate firstTime historical
        outcome

/-- Fresh terminal-state progress is always a strict edge of the already
proved well-founded canonical selection relation. -/
theorem TerminalCanonicalTailHistoryFreshProgress.strict
    {target horizon : Nat} {key : TerminalCanonicalTailHistoryKey}
    {state : TerminalCanonicalTailHistorySelectionState target horizon}
    (h : TerminalCanonicalTailHistoryFreshProgress target horizon key state) :
    ∃ nextState, TerminalCanonicalTailHistorySelectionProgress nextState
      state := by
  rcases h with ⟨nextState, _, hprogress⟩
  exact ⟨nextState, hprogress⟩

end

end Recaman
