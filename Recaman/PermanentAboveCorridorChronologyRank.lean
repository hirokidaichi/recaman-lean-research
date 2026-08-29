import Recaman.PermanentAboveCorridorSelectedInstall

namespace Recaman

noncomputable section

/-! # History progress of an installed-cycle chronology mismatch

If the next historical downcross endpoint lies after the selected old
crossing, that endpoint is a new below-target value at its first occurrence.
The apparent chronology mismatch therefore strictly consumes the missing
below-target history budget between the selected crossing time and the
endpoint.

This is an independent well-founded relation, obtained by pulling natural
less-than back along `missingBelowCount`.  Hence every installed next
discharge is either eligible for the restart/cursor theorem or already makes
strict history progress; no chronology kernel remains.
-/

/-- Plain history-budget drop between two cursor times. -/
def TerminalHistoryBudgetDrop (target : Nat)
    (childTime parentTime : Nat) : Prop :=
  missingBelowCount target childTime <
    missingBelowCount target parentTime

/-- Orbit content of a history-edge parent cursor: an above-target
predecessor cursor strictly inside the bound, pinned as the numeric
predecessor of a tail minimum whose tail begins after every low orbit
value.  Every generation site of a terminal history edge can supply this,
because the parent cursor of such an edge always dominates the discharge
downcross, which in turn dominates the stored historical predecessor. -/
def TerminalHistoryCursor (target bound : Nat) : Prop :=
  ∃ cursorTime minimumTime tailStart,
    cursorTime < bound ∧ target < a cursorTime ∧
      a cursorTime + 1 = a minimumTime ∧ tailStart ≤ minimumTime ∧
      ∀ witness, a witness ≤ target → witness < tailStart

/-- The cursor is monotone in its bound. -/
theorem TerminalHistoryCursor.mono {target bound newBound : Nat}
    (h : TerminalHistoryCursor target bound) (hle : bound ≤ newBound) :
    TerminalHistoryCursor target newBound := by
  rcases h with ⟨cursorTime, minimumTime, tailStart, hlt, habove, hsucc,
    htail, hlow⟩
  exact ⟨cursorTime, minimumTime, tailStart, by omega, habove, hsucc, htail,
    hlow⟩

def TerminalChronologyHistoryProgress (target : Nat)
    (childTime parentTime : Nat) : Prop :=
  TerminalHistoryBudgetDrop target childTime parentTime ∧
    TerminalHistoryCursor target (parentTime + 1)

/-- The bare budget drop is already a well-founded relation. -/
theorem terminalHistoryBudgetDrop_wellFounded (target : Nat) :
    WellFounded (TerminalHistoryBudgetDrop target) := by
  apply WellFounded.intro
  intro time
  generalize hrank : missingBelowCount target time = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing time with
  | intro rank _ ih =>
      apply Acc.intro time
      intro childTime hchild
      have hrelation : missingBelowCount target childTime < rank := by
        simpa [TerminalHistoryBudgetDrop, hrank] using hchild
      exact ih (missingBelowCount target childTime) hrelation childTime rfl

theorem terminalChronologyHistoryProgress_wellFounded (target : Nat) :
    WellFounded (TerminalChronologyHistoryProgress target) := by
  apply WellFounded.intro
  intro time
  generalize hrank : missingBelowCount target time = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing time with
  | intro rank _ ih =>
      apply Acc.intro time
      intro childTime hchild
      have hrelation : missingBelowCount target childTime < rank := by
        simpa [TerminalChronologyHistoryProgress, TerminalHistoryBudgetDrop,
          hrank] using hchild.1
      exact ih (missingBelowCount target childTime) hrelation childTime rfl

/-- Every discharge return certificate supplies the history cursor at any
bound beyond its own downcross time.  The stored historical predecessor sits
at or before the downcross, strictly exceeds the target, and is the numeric
predecessor of the historical tail minimum, whose tail begins after every
low orbit value. -/
theorem PermanentTailDischargeReturnCertificate.terminalHistoryCursor
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    {bound : Nat} (hbound : source.downTime < bound) :
    TerminalHistoryCursor target bound := by
  have hhorizon := source.downcross.horizon_le_time
  have hpredecessor := source.historical_minimum.predecessor_first.1
  have htarget := source.historical_minimum.target_lt_predecessor
  have hpositive := source.historical_tail.target_positive
  refine ⟨source.historicalFirstTime, source.historicalMinimumTime,
    source.tailStart, by omega, by omega, by omega,
    source.historical_minimum.minimum.start_le_time, ?_⟩
  intro witness hlow
  by_cases hbefore : witness < source.tailStart
  · exact hbefore
  · have habove := source.historical_tail.strictly_above witness
      (Nat.le_of_not_gt hbefore)
    omega

/-- Complete strict history edge exposed by the chronology mismatch. -/
structure TerminalSelectedCrossingChronologyProgressCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    {install : TerminalSelectedCrossingInstallCertificate crossing}
    (next : TerminalSelectedCrossingDischargeCertificate install) : Prop where
  selected_before_endpoint :
    crossingTime < next.discharge.downTime + 1
  endpoint_below :
    a (next.discharge.downTime + 1) < target
  endpoint_first :
    FirstAt a (a (next.discharge.downTime + 1))
      (next.discharge.downTime + 1)
  missing_drop :
    missingBelowCount target (next.discharge.downTime + 1) <
      missingBelowCount target crossingTime
  seen_gain :
    seenBelowCount target crossingTime <
      seenBelowCount target (next.discharge.downTime + 1)
  progress : TerminalHistoryBudgetDrop target
    (next.discharge.downTime + 1) crossingTime

/-- The literal mismatch constructor yields a strict first-occurrence history
edge. -/
theorem TerminalSelectedCrossingDischargeCertificate.chronologyProgress
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    {install : TerminalSelectedCrossingInstallCertificate crossing}
    (h : TerminalSelectedCrossingDischargeCertificate install)
    (hmismatch : crossingTime < h.discharge.downTime + 1) :
    TerminalSelectedCrossingChronologyProgressCertificate h := by
  have hbelow := h.discharge.downcross.endpoint_below
  have hfirst := h.discharge.endpoint_first
  have hmissing := missingBelowCount_strict_of_firstAt hbelow hmismatch hfirst
  have hseen :=
    seenBelowCount_strict_of_missingBelowCount_strict hmissing
  exact {
    selected_before_endpoint := hmismatch
    endpoint_below := hbelow
    endpoint_first := hfirst
    missing_drop := hmissing
    seen_gain := hseen
    progress := hmissing
  }

/-- Total chronology result for an installed next discharge. -/
inductive TerminalSelectedCrossingIterationProgress
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    {install : TerminalSelectedCrossingInstallCertificate crossing}
    (next : TerminalSelectedCrossingDischargeCertificate install) : Prop
  | eligible
      (endpoint_le_selected :
        next.discharge.downTime + 1 ≤ crossingTime) :
      TerminalSelectedCrossingIterationProgress next
  | history_progress
      (certificate :
        TerminalSelectedCrossingChronologyProgressCertificate next) :
      TerminalSelectedCrossingIterationProgress next

/-- Chronology is either exactly eligible or itself a strict well-founded
history edge. -/
theorem TerminalSelectedCrossingDischargeCertificate.iterationProgress
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    {install : TerminalSelectedCrossingInstallCertificate crossing}
    (h : TerminalSelectedCrossingDischargeCertificate install) :
    TerminalSelectedCrossingIterationProgress h := by
  cases h.chronology with
  | eligible endpoint_le_selected =>
      exact .eligible endpoint_le_selected
  | mismatch selected_before_endpoint =>
      exact .history_progress
        (h.chronologyProgress selected_before_endpoint)

end

end Recaman
