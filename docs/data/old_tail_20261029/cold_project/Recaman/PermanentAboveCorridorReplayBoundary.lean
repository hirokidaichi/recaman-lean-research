import Recaman.PermanentAboveCorridorCanonicalStateStep

namespace Recaman

noncomputable section

/-! # Exact canonical replay: no-go and resolver boundary

A visited list is a termination device, not a semantic no-replay theorem.
Removing a valid key from a state and presenting the same finite certificate
again constructs the exact revisit residual directly.  Thus no contradiction
can be obtained from list membership alone.

This module records that no-go in the kernel and defines the remaining local
mathematical interface.  A replay resolver must turn an exact revisit into a
target occurrence, strict history progress, semantic phase progress, or an
installed-cycle master edge.  Under precisely that assumption the terminal
step has no unresolved constructor.
-/

/-- Remove every occurrence of one key while preserving global candidate
validity. -/
def TerminalCanonicalTailHistorySelectionState.removeAll
    {target horizon : Nat}
    (state : TerminalCanonicalTailHistorySelectionState target horizon)
    (key : TerminalCanonicalTailHistoryKey) :
    TerminalCanonicalTailHistorySelectionState target horizon := {
  remaining := state.remaining.filter fun candidate => decide (candidate ≠ key)
  remaining_candidates := by
    intro candidate hmem
    have hbase : candidate ∈ state.remaining := by
      have hfiltered : candidate ∈ state.remaining ∧
          decide (candidate ≠ key) = true := by
        simpa only [List.mem_filter] using hmem
      exact hfiltered.1
    exact state.remaining_candidates candidate hbase
}

theorem TerminalCanonicalTailHistorySelectionState.not_mem_removeAll
    {target horizon : Nat}
    (state : TerminalCanonicalTailHistorySelectionState target horizon)
    (key : TerminalCanonicalTailHistoryKey) :
    key ∉ (state.removeAll key).remaining := by
  simp [TerminalCanonicalTailHistorySelectionState.removeAll]

/-- The same finite certificate is an exact replay after its key is removed.
This is the formal no-go for a list-only contradiction. -/
theorem TerminalFiniteReturnWindowCertificate.exactReplayResidual_after_removeAll
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (state : TerminalCanonicalTailHistorySelectionState target
      parent.horizon) :
    TerminalCanonicalTailHistoryExactRevisitResidual target parent.horizon
      finite.canonicalTailHistoryKey
      (state.removeAll finite.canonicalTailHistoryKey) := {
  candidate_membership := finite.canonicalTailHistoryKey_mem rfl
  not_remaining := state.not_mem_removeAll finite.canonicalTailHistoryKey
}

/-- The no-go also inhabits the exact-revisit constructor of the integrated
terminal outcome. -/
theorem TerminalFiniteReturnWindowCertificate.exactReplayTerminalOutcome_after_removeAll
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (state : TerminalCanonicalTailHistorySelectionState target
      parent.horizon) :
    PermanentTailTerminalCanonicalStateStepOutcome source
      (state.removeAll finite.canonicalTailHistoryKey) :=
  .exact_canonical_revisit terminalEndpoint finite
    (finite.exactReplayResidual_after_removeAll state)

/-- Progress forms strong enough to resolve a literal replay.  The final
constructor is deliberately the already well-founded installed-cycle master
relation, rather than a new unverified rank. -/
inductive TerminalExactCanonicalReplayResolution
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      TerminalExactCanonicalReplayResolution source
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      TerminalExactCanonicalReplayResolution source
  | semantic_progress
      (child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child parent) :
      TerminalExactCanonicalReplayResolution source
  | installed_master_progress
      (child parentNode : TailInstalledCycleSearchNode)
      (progress : TailInstalledCycleProgress target child parentNode) :
      TerminalExactCanonicalReplayResolution source

/-- Minimal open mathematical obligation after the finite-state no-go. -/
def TerminalExactCanonicalReplayResolver (target : Nat) : Prop :=
  ∀ {start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalCanonicalTailHistorySelectionState target parent.horizon)
    (terminalEndpoint : Nat)
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint),
    TerminalCanonicalTailHistoryExactRevisitResidual target parent.horizon
      finite.canonicalTailHistoryKey state →
      TerminalExactCanonicalReplayResolution source

/-- Terminal outcome with the raw replay residual replaced by the resolver's
proved semantic/rank result. -/
inductive PermanentTailTerminalReplayResolvedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalCanonicalTailHistorySelectionState target
      parent.horizon) : Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalReplayResolvedOutcome source state
  | finite_state_progress
      (terminalEndpoint : Nat)
      (finite : TerminalFiniteReturnWindowCertificate source
        terminalEndpoint)
      (progress : TerminalCanonicalTailHistoryFreshProgress target
        parent.horizon finite.canonicalTailHistoryKey state) :
      PermanentTailTerminalReplayResolvedOutcome source state
  | replay_resolved
      (resolution : TerminalExactCanonicalReplayResolution source) :
      PermanentTailTerminalReplayResolvedOutcome source state
  | immediate_semantic
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (outcome : ImmediateTerminalSemanticOutcome target source.downTime
        source.returnTime) :
      PermanentTailTerminalReplayResolvedOutcome source state
  | historical_complete
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalCompleteStepOutcome historical) :
      PermanentTailTerminalReplayResolvedOutcome source state

/-- Conditional closure theorem: the resolver is exactly sufficient to
remove the final raw finite residual from the terminal total step. -/
theorem PermanentTailDischargeReturnCertificate.terminalReplayResolvedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (state : TerminalCanonicalTailHistorySelectionState target
      parent.horizon)
    (resolver : TerminalExactCanonicalReplayResolver target) :
    PermanentTailTerminalReplayResolvedOutcome source state := by
  cases source.terminalCanonicalStateStepOutcome state with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | finite_state_progress terminalEndpoint finite progress =>
      exact .finite_state_progress terminalEndpoint finite progress
  | exact_canonical_revisit terminalEndpoint finite residual =>
      exact .replay_resolved
        (resolver source state terminalEndpoint finite residual)
  | immediate_semantic valley insufficient outcome =>
      exact .immediate_semantic valley insufficient outcome
  | historical_complete freshEndpoint candidate firstTime historical
      outcome =>
      exact .historical_complete freshEndpoint candidate firstTime historical
        outcome

end

end Recaman
