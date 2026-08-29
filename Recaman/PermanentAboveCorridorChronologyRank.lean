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

def TerminalChronologyHistoryProgress (target : Nat)
    (childTime parentTime : Nat) : Prop :=
  missingBelowCount target childTime <
    missingBelowCount target parentTime

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
        simpa [TerminalChronologyHistoryProgress, hrank] using hchild
      exact ih (missingBelowCount target childTime) hrelation childTime rfl

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
  progress : TerminalChronologyHistoryProgress target
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
