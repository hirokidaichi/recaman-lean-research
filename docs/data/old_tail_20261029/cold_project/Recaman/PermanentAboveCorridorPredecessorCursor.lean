import Recaman.PermanentAboveCorridorPredecessorCrossing

namespace Recaman

noncomputable section

/-! # Cursor refinement of a blocker-predecessor crossing

The ordinary phase rank sees only the crossing predecessor anchor when the
history horizon is fixed.  The permanent-tail cursor rank additionally sees
the crossing time.  Consequently, an equal-anchor predecessor crossing still
makes progress when it is earlier than the old crossing.

Without a chronology hypothesis the remaining kernel is strict anchor growth
or an equal anchor whose time is not earlier.  If the old crossing is eligible
from the original downcross endpoint, canonicality bounds the newly selected
crossing by the old crossing and the latter kernel becomes literal
stationarity.
-/

/-- Combined outcome after consulting both the phase rank and the crossing
cursor rank. -/
inductive TerminalBelowPredecessorCombinedRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) : Prop
  | phase_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      TerminalBelowPredecessorCombinedRankOutcome below
  | cursor_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : TailCrossingCursorProgress
        ⟨a crossingTime, crossingTime⟩
        ⟨parent.anchorParent, source.oldCrossingTime⟩) :
      TerminalBelowPredecessorCombinedRankOutcome below
  | anchor_growth
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (growth : parent.anchorParent < a crossingTime) :
      TerminalBelowPredecessorCombinedRankOutcome below
  | same_anchor_not_earlier
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (same_anchor : a crossingTime = parent.anchorParent)
      (not_earlier : source.oldCrossingTime ≤ crossingTime) :
      TerminalBelowPredecessorCombinedRankOutcome below

/-- The selected blocker crossing either descends one of the two existing
ranks or reaches the exact growth/chronology kernel. -/
theorem BelowTargetHistoricalPredecessorCertificate.combinedRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) :
    TerminalBelowPredecessorCombinedRankOutcome h := by
  cases h.crossingRankOutcome with
  | refined_progress crossingTime quotient remainder certificate progress =>
      exact .phase_progress crossingTime quotient remainder certificate
        progress
  | anchor_growth crossingTime quotient remainder certificate
      anchor_nondecreasing =>
      by_cases hstrict : parent.anchorParent < a crossingTime
      · exact .anchor_growth crossingTime quotient remainder certificate
          hstrict
      · have hsame : a crossingTime = parent.anchorParent := by omega
        by_cases hearlier : crossingTime < source.oldCrossingTime
        · have hcursor : TailCrossingCursorProgress
              ⟨a crossingTime, crossingTime⟩
              ⟨parent.anchorParent, source.oldCrossingTime⟩ := by
            rw [tailCrossingCursorProgress_iff]
            exact Or.inr ⟨hsame, hearlier⟩
          exact .cursor_progress crossingTime quotient remainder certificate
            hcursor
        · exact .same_anchor_not_earlier crossingTime quotient remainder
            certificate hsame (Nat.le_of_not_gt hearlier)

/-- Cursor progress from the blocker-predecessor crossing closes the upward
discharge-to-crossing edge of the existing five-coordinate cycle rank. -/
theorem TerminalBelowPredecessorCrossingCertificate.cursorCycleProgress
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder childHistoryTime parentHistoryTime
      childMinimum parentMinimum : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    (_h : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder)
    (hcursor : TailCrossingCursorProgress
      ⟨a crossingTime, crossingTime⟩
      ⟨parent.anchorParent, source.oldCrossingTime⟩) :
    TailCursorCycleProgress target
      ⟨a crossingTime, crossingTime, .crossing, childHistoryTime,
        childMinimum⟩
      ⟨parent.anchorParent, source.oldCrossingTime, .discharge,
        parentHistoryTime, parentMinimum⟩ :=
  tailCursorCycle_exit_of_cursorProgress hcursor

/-- With chronological eligibility of the old crossing, the last equal-anchor
kernel is literal stationarity. -/
inductive TerminalBelowPredecessorEligibleRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) : Prop
  | phase_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      TerminalBelowPredecessorEligibleRankOutcome below
  | cursor_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : TailCrossingCursorProgress
        ⟨a crossingTime, crossingTime⟩
        ⟨parent.anchorParent, source.oldCrossingTime⟩) :
      TerminalBelowPredecessorEligibleRankOutcome below
  | anchor_growth
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (growth : parent.anchorParent < a crossingTime) :
      TerminalBelowPredecessorEligibleRankOutcome below
  | stationary
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (same_anchor : a crossingTime = parent.anchorParent)
      (same_time : crossingTime = source.oldCrossingTime) :
      TerminalBelowPredecessorEligibleRankOutcome below

/-- Eligibility turns the chronology residual into exact equality, because
the selected first crossing is bounded by the canonical discharge return. -/
theorem BelowTargetHistoricalPredecessorCertificate.eligibleRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical)
    (holdEligible : source.downTime + 1 ≤ source.oldCrossingTime) :
    TerminalBelowPredecessorEligibleRankOutcome h := by
  cases h.combinedRankOutcome with
  | phase_progress crossingTime quotient remainder certificate progress =>
      exact .phase_progress crossingTime quotient remainder certificate
        progress
  | cursor_progress crossingTime quotient remainder certificate progress =>
      exact .cursor_progress crossingTime quotient remainder certificate
        progress
  | anchor_growth crossingTime quotient remainder certificate growth =>
      exact .anchor_growth crossingTime quotient remainder certificate growth
  | same_anchor_not_earlier crossingTime quotient remainder certificate
      same_anchor not_earlier =>
      have hreturnLe := source.returnTime_le_oldCrossingTime holdEligible
      have hcrossingLe := certificate.crossingTime_le_return
      exact .stationary crossingTime quotient remainder certificate
        same_anchor (by omega)

end

end Recaman
