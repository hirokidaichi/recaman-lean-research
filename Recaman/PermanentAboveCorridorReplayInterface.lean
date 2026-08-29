import Recaman.PermanentAboveCorridorReplayFloor

namespace Recaman

noncomputable section

/-! # Missing-target interface of the closed terminal analysis

Inside a virtual counterexample the target-occurrence branch of the
iteration-free outcome is contradictory, so a combined permanent-tail
certificate hands exactly three kinds of information to the outer search:
a strict chronology history edge, a semantic phase child, or an exact
replay fixed point.  This is the complete interface of the permanent-tail
terminal analysis.

The replay branch is moreover rigid: its crossing cursor and anchor are
determined by the discharge itself, since both equal the stored old
crossing data.  Distinct replay certificates of one discharge can differ
only in their blocker provenance, never in the cycle they close.
-/

/-- Terminal information available from a missing-target permanent tail:
no target branch remains. -/
inductive PermanentTailTerminalMissingOutcome
    (target start : Nat) : Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalMissingOutcome target start
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalMissingOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      PermanentTailTerminalMissingOutcome target start

/-- The target-occurrence branch contradicts the missing-target field, so
the closed terminal analysis returns exactly three interface forms. -/
theorem PermanentTailCombinedCertificate.terminalMissingOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    PermanentTailTerminalMissingOutcome target start := by
  cases h.terminalReplayReducedOutcome with
  | target_occurs witness value_eq =>
      exact False.elim (h.tail.target_missing ⟨witness, value_eq⟩)
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | semantic_progress stepParent child semantic progress =>
      exact .semantic_progress stepParent child semantic progress
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The replay crossing cursor is determined by the discharge alone. -/
theorem crossingTime_unique
    (r₁ r₂ : TerminalExactDischargeReplayCertificate source) :
    r₁.crossingTime = r₂.crossingTime := by
  have h₁ := r₁.time_eq
  have h₂ := r₂.time_eq
  omega

/-- So is the replay anchor value: both replay equalities read back the
stored old crossing. -/
theorem anchor_value_unique
    (r₁ r₂ : TerminalExactDischargeReplayCertificate source) :
    a r₁.crossingTime = a r₂.crossingTime := by
  rw [r₁.crossingTime_unique r₂]

end TerminalExactDischargeReplayCertificate

end

end Recaman
