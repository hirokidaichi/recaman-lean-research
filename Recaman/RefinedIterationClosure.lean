import Recaman.RefinedSuccessorRank
import Recaman.PermanentAboveCorridorIterationClosure

namespace Recaman

noncomputable section

/-! # Eliminating the installed iteration while keeping the pinned branch

`PermanentTailTerminalReplayReducedOutcome` consumes the installed successor
iteration by well-founded recursion on the discharge-level rank and, in doing
so, forgets which discharge produced its semantic branch.  This module repeats
the same recursion with the certificate-tied `RefinedSemanticEdge` payload of
the previous stage.

Only the semantic constructor changes.  The recursion itself is the original
one: strict iteration edges descend the transportable triple, whose
lexicographic order is well founded, and the exact replay fixed point keeps
its full construction chain.
-/

/-- Refinement of `PermanentTailTerminalReplayReducedOutcome`.  The semantic
constructor now carries the generating certificate through
`RefinedSemanticEdge`, so it can no longer be produced from positivity of the
target alone. -/
inductive RefinedTerminalReplayReducedOutcome (target start : Nat) : Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      RefinedTerminalReplayReducedOutcome target start
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      RefinedTerminalReplayReducedOutcome target start
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      RefinedTerminalReplayReducedOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      RefinedTerminalReplayReducedOutcome target start

/-- Refined form of `terminalReplayReducedOutcome`: recursing along strict
iteration edges consumes every installed successor branch, and each semantic
exit is recorded together with the discharge which produced it. -/
theorem PermanentTailDischargeReturnCertificate.refinedTerminalReplayReducedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    RefinedTerminalReplayReducedOutcome target start := by
  have main : ∀ rank : Nat × (Nat × Nat),
      ∀ (parentNode : PhaseSearchNode)
        (node : PermanentTailDischargeReturnCertificate target start
          parentNode),
        terminalDischargeIterationRank target node = rank →
        RefinedTerminalReplayReducedOutcome target start := by
    intro rank
    induction natTripleLex_wellFounded.apply rank with
    | intro rank _ ih =>
        intro parentNode node hrank
        cases node.refinedTerminalIterationOutcome with
        | target_occurs witness value_eq =>
            exact .target_occurs witness value_eq
        | history_progress childTime parentTime progress =>
            exact .history_progress childTime parentTime progress
        | refined_semantic step =>
            exact .refined_semantic (.discharge_step parentNode node step)
        | iteration_progress _crossingTime next _next_old_eq iteration =>
            have hrelation : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
                (terminalDischargeIterationRank target next) rank := by
              rw [← hrank]
              exact iteration
            exact ih (terminalDischargeIterationRank target next) hrelation
              _ next rfl
        | exact_replay replay =>
            exact .exact_replay parentNode node replay
  exact main (terminalDischargeIterationRank target source) parent source rfl

/-- Combined-certificate form: any permanent-tail obstruction has an initial
discharge, so its whole successor iteration reduces to the same four outcomes
with the pinned semantic branch. -/
theorem PermanentTailCombinedCertificate.refinedTerminalReplayReducedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    RefinedTerminalReplayReducedOutcome target start := by
  obtain ⟨source⟩ := h.exists_dischargeReturnCertificate
  exact source.refinedTerminalReplayReducedOutcome

end

end Recaman
