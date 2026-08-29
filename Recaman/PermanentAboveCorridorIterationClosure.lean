import Recaman.PermanentAboveCorridorSuccessorRank

namespace Recaman

noncomputable section

/-! # Well-founded closure of the installed successor iteration

The discharge-level iteration rank is a triple of naturals under the
lexicographic order, which is well founded.  Iterating the terminal analysis
along strict successor edges therefore terminates, and the iteration
constructor can be eliminated by recursion: after finitely many installed
successors, the analysis reaches the target, one of the established global
strict edges, or an exact replay fixed point at some descendant discharge.

The replay branch keeps the descendant discharge itself together with its
full replay certificate, so the remaining mathematics is concentrated on one
typed object rather than on an unbounded iteration.
-/

/-- Iteration-free terminal outcome.  The exact replay branch names the
descendant discharge at which the iteration rank stopped moving. -/
inductive PermanentTailTerminalReplayReducedOutcome
    (target start : Nat) : Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      PermanentTailTerminalReplayReducedOutcome target start
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalReplayReducedOutcome target start
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalReplayReducedOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      PermanentTailTerminalReplayReducedOutcome target start

/-- Recursing along strict iteration edges consumes every installed successor
branch: only the target, an established strict edge, or an exact replay fixed
point survives. -/
theorem PermanentTailDischargeReturnCertificate.terminalReplayReducedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalReplayReducedOutcome target start := by
  have main : ∀ rank : Nat × (Nat × Nat),
      ∀ (parentNode : PhaseSearchNode)
        (node : PermanentTailDischargeReturnCertificate target start
          parentNode),
        terminalDischargeIterationRank target node = rank →
        PermanentTailTerminalReplayReducedOutcome target start := by
    intro rank
    induction natTripleLex_wellFounded.apply rank with
    | intro rank _ ih =>
        intro parentNode node hrank
        cases node.terminalIterationOutcome with
        | target_occurs witness value_eq =>
            exact .target_occurs witness value_eq
        | history_progress childTime parentTime progress =>
            exact .history_progress childTime parentTime progress
        | semantic_progress stepParent child semantic progress =>
            exact .semantic_progress stepParent child semantic progress
        | iteration_progress crossingTime next next_old_eq iteration =>
            have hrelation : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
                (terminalDischargeIterationRank target next) rank := by
              rw [← hrank]
              exact iteration
            exact ih (terminalDischargeIterationRank target next) hrelation
              _ next rfl
        | exact_replay replay =>
            exact .exact_replay parentNode node replay
  exact main (terminalDischargeIterationRank target source) parent source rfl

/-- Any combined permanent-tail obstruction admits an initial discharge, so
its whole successor iteration reduces to the same four outcomes. -/
theorem PermanentTailCombinedCertificate.terminalReplayReducedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    PermanentTailTerminalReplayReducedOutcome target start := by
  obtain ⟨source⟩ := h.exists_dischargeReturnCertificate
  exact source.terminalReplayReducedOutcome

end

end Recaman
