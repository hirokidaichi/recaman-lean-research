import Recaman.RefinedIterationClosure
import Recaman.PermanentAboveCorridorReplayInterface

namespace Recaman

noncomputable section

/-! # Missing-target interface with the pinned semantic branch

`PermanentTailTerminalMissingOutcome` removes the target-occurrence branch of
the iteration-free outcome and keeps three interface forms for the outer
search.  Its semantic form is still the broad one, whose step parent is
existentially quantified and whose child is only a `PhaseSemanticInvariant`.

This stage repeats the same elimination with the certificate-tied
`RefinedSemanticEdge` payload.  Nothing else changes: the history edge keeps
its strengthened `TerminalChronologyHistoryProgress` (budget drop together
with the parent history cursor) verbatim, and the replay branch keeps its
full construction chain.
-/

/-- Refinement of `PermanentTailTerminalMissingOutcome`. -/
inductive RefinedTerminalMissingOutcome (target start : Nat) : Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      RefinedTerminalMissingOutcome target start
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      RefinedTerminalMissingOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      RefinedTerminalMissingOutcome target start

/-- Refined form of `terminalMissingOutcome`: inside a virtual
counterexample the occurrence branch is contradictory, so the closed terminal
analysis returns a history edge, a certificate-tied refined semantic edge, or
an exact replay fixed point. -/
theorem PermanentTailCombinedCertificate.refinedTerminalMissingOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    RefinedTerminalMissingOutcome target start := by
  cases h.refinedTerminalReplayReducedOutcome with
  | target_occurs witness value_eq =>
      exact False.elim (h.tail.target_missing ⟨witness, value_eq⟩)
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | refined_semantic edge =>
      exact .refined_semantic edge
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

end

end Recaman
