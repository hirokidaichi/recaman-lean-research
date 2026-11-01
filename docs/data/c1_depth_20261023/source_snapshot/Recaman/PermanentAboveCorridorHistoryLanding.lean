import Recaman.PermanentAboveCorridorReplayInterface

namespace Recaman

noncomputable section

/-! # Fresh landings behind every history edge

A strict missing-budget drop is not an abstract inequality: it always comes
from an explicit below-target value whose first occurrence lies strictly
inside the intervening window.  This module recovers that landing from the
inequality alone, so no upstream theorem has to be rewritten to thread the
witness.

Since the landing is below the target, the canonical upcrossing machinery
restarts from it.  The missing-target interface therefore strengthens to an
anchored form: every history edge carries a concrete fresh landing together
with the first crossing that returns from it, exactly the data the outer
recursion needs to continue past a history edge.
-/

/-- A strict missing-count drop exposes a below-target value seen by the
child cursor but not by the parent cursor. -/
theorem exists_new_below_of_missingDrop
    {m childTime parentTime : Nat}
    (h : missingBelowCount m childTime <
      missingBelowCount m parentTime) :
    ∃ v, v < m ∧ v ∉ valuesThrough parentTime ∧
      v ∈ valuesThrough childTime := by
  induction m with
  | zero => simp at h
  | succ m ih =>
      by_cases hc : m ∈ valuesThrough childTime
      · by_cases hp : m ∈ valuesThrough parentTime
        · have hstep : missingBelowCount m childTime <
              missingBelowCount m parentTime := by
            simp [missingBelowCount_succ, hc, hp] at h
            omega
          rcases ih hstep with ⟨v, hv, hnp, hcv⟩
          exact ⟨v, by omega, hnp, hcv⟩
        · exact ⟨m, by omega, hp, hc⟩
      · by_cases hp : m ∈ valuesThrough parentTime
        · have hstep : missingBelowCount m childTime <
              missingBelowCount m parentTime := by
            simp [missingBelowCount_succ, hc, hp] at h
            omega
          rcases ih hstep with ⟨v, hv, hnp, hcv⟩
          exact ⟨v, by omega, hnp, hcv⟩
        · have hstep : missingBelowCount m childTime <
              missingBelowCount m parentTime := by
            simp [missingBelowCount_succ, hc, hp] at h
            omega
          rcases ih hstep with ⟨v, hv, hnp, hcv⟩
          exact ⟨v, by omega, hnp, hcv⟩

/-- Every terminal history edge carries a fresh below-target landing whose
first occurrence lies strictly after the parent cursor. -/
theorem TerminalChronologyHistoryProgress.exists_freshLanding
    {target childTime parentTime : Nat}
    (h : TerminalHistoryBudgetDrop target childTime parentTime) :
    ∃ value landingTime, value < target ∧ parentTime < landingTime ∧
      landingTime ≤ childTime ∧ FirstAt a value landingTime := by
  rcases exists_new_below_of_missingDrop h with ⟨v, hv, hnp, hcv⟩
  rcases history_member_has_firstAt hcv with ⟨u, hu, hfirst⟩
  have hafter : parentTime < u := by
    by_cases hle : u ≤ parentTime
    · exact False.elim
        (hnp (mem_valuesThrough_iff.mpr ⟨u, hle, hfirst.1⟩))
    · omega
  exact ⟨v, u, hv, hafter, hu, hfirst⟩

/-- The same landing, together with the history cursor transported from the
parent cursor to the landing time. -/
theorem TerminalChronologyHistoryProgress.exists_freshLandingCursor
    {target childTime parentTime : Nat}
    (h : TerminalChronologyHistoryProgress target childTime parentTime) :
    ∃ value landingTime, value < target ∧ parentTime < landingTime ∧
      landingTime ≤ childTime ∧ FirstAt a value landingTime ∧
      TerminalHistoryCursor target landingTime := by
  rcases TerminalChronologyHistoryProgress.exists_freshLanding h.1 with
    ⟨value, landingTime, hvalue, hafter, hbefore, hfirst⟩
  exact ⟨value, landingTime, hvalue, hafter, hbefore, hfirst,
    h.2.mono (by omega)⟩

/-- Anchored interface: history edges are upgraded to a fresh landing plus
its canonical restart crossing. -/
inductive PermanentTailTerminalAnchoredOutcome
    (target start : Nat) : Prop
  | fresh_landing
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime)
      (value landingTime nextCrossingTime : Nat)
      (value_below : value < target)
      (after_parent : parentTime < landingTime)
      (before_child : landingTime ≤ childTime)
      (landing_first : FirstAt a value landingTime)
      (next_crossing : FirstWeakUpcrossingStep target landingTime
        nextCrossingTime)
      (landing_cursor : TerminalHistoryCursor target landingTime) :
      PermanentTailTerminalAnchoredOutcome target start
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalAnchoredOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      PermanentTailTerminalAnchoredOutcome target start

/-- The missing-target interface anchors: every branch now hands the outer
recursion either a semantic child, a replay fixed point, or a concrete fresh
landing with its restart crossing. -/
theorem PermanentTailCombinedCertificate.terminalAnchoredOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    PermanentTailTerminalAnchoredOutcome target start := by
  cases h.terminalMissingOutcome with
  | history_progress childTime parentTime progress =>
      rcases progress.exists_freshLandingCursor with
        ⟨value, landingTime, hvalue, hafter, hbefore, hfirst, hcursor⟩
      have hbelow : a landingTime < target := by
        rw [hfirst.1]
        exact hvalue
      rcases exists_firstWeakUpcrossingStep_from_below
          h.tail.target_positive hbelow with ⟨nextCrossingTime, hnext⟩
      exact .fresh_landing childTime parentTime progress value landingTime
        nextCrossingTime hvalue hafter hbefore hfirst hnext hcursor
  | semantic_progress stepParent child semantic progress =>
      exact .semantic_progress stepParent child semantic progress
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

end

end Recaman
