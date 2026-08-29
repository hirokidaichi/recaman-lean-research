import Recaman.PermanentAboveCorridorCandidates

namespace Recaman

noncomputable section

/-! # Outer-history rank data of terminal blockers

Every positive terminal historical blocker is born at a positive time.  Its
first occurrence therefore gives a strict seen-below gain from the preceding
clock, equivalently a valid backtrack edge in the existing tail-cycle rank.

Comparing the blocker time with the original downcross endpoint gives a
second classification: a later blocker is also strict forward history-budget
progress, while an earlier blocker remains outer historical provenance.  A
semantic rule selecting the predecessor as the next historical node is still
needed to turn the available numerical rank edge into a complete cycle step.
-/

/-- Common provenance of the immediate and finite outer-blocker branches. -/
structure TerminalOuterHistoricalBlockerCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    (freshEndpoint candidate firstTime : Nat) : Prop where
  fresh : TerminalFreshEndpointCertificate source freshEndpoint
  blocker : TerminalHistoricalBlockerCertificate target source.returnTime
    candidate firstTime
  firstTime_le_fresh : firstTime ≤ freshEndpoint

/-- Local budget and seen-count descent exposed by every positive historical
blocker at the clock immediately before its first occurrence. -/
structure TerminalHistoricalBacktrackCertificate
    (target returnTime candidate firstTime : Nat) : Prop where
  blocker : TerminalHistoricalBlockerCertificate target returnTime candidate
    firstTime
  firstTime_positive : 0 < firstTime
  predecessor_before : firstTime - 1 < firstTime
  missing_drop : missingBelowCount target firstTime <
    missingBelowCount target (firstTime - 1)
  seen_gain : seenBelowCount target (firstTime - 1) <
    seenBelowCount target firstTime

/-- A positive blocker has a nonzero first time and supplies the local dual
history-budget edge. -/
theorem TerminalHistoricalBlockerCertificate.backtrackCertificate
    {target returnTime candidate firstTime : Nat}
    (h : TerminalHistoricalBlockerCertificate target returnTime candidate
      firstTime) :
    TerminalHistoricalBacktrackCertificate target returnTime candidate
      firstTime := by
  have htimePositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · have hvalue := h.candidate_first.1
      rw [hzero] at hvalue
      have haZero : a 0 = 0 := rfl
      rw [haZero] at hvalue
      have hcandidatePositive := h.candidate_positive
      omega
    · omega
  have hpredecessor : firstTime - 1 < firstTime := by omega
  have hmissing := missingBelowCount_strict_of_firstAt
    h.candidate_below_target hpredecessor h.candidate_first
  have hseen := seenBelowCount_strict_of_missingBelowCount_strict hmissing
  exact {
    blocker := h
    firstTime_positive := htimePositive
    predecessor_before := hpredecessor
    missing_drop := hmissing
    seen_gain := hseen
  }

/-- The local blocker certificate is exactly a backtrack edge of the
existing permanent-tail cycle rank, for any fixed anchor and minimum. -/
theorem TerminalHistoricalBacktrackCertificate.tailCycleProgress
    {target returnTime candidate firstTime anchor minimumValue : Nat}
    (h : TerminalHistoricalBacktrackCertificate target returnTime candidate
      firstTime) :
    TailCycleProgress target
      ⟨anchor, .backtrack, firstTime - 1, minimumValue⟩
      ⟨anchor, .backtrack, firstTime, minimumValue⟩ :=
  tailCycleProgress_backtrack_of_seenDrop h.seen_gain

/-- Explicit selection boundary: if the next historical clock is chosen as
the predecessor of the blocker's first occurrence, the existing cycle rank
strictly descends.  Constructing the corresponding semantic search node is
the remaining outer-selection obligation. -/
theorem TerminalHistoricalBacktrackCertificate.tailCycleProgress_of_selected
    {target returnTime candidate firstTime anchor minimumValue
      nextHistoryTime : Nat}
    (h : TerminalHistoricalBacktrackCertificate target returnTime candidate
      firstTime)
    (hselected : nextHistoryTime = firstTime - 1) :
    TailCycleProgress target
      ⟨anchor, .backtrack, nextHistoryTime, minimumValue⟩
      ⟨anchor, .backtrack, firstTime, minimumValue⟩ := by
  subst nextHistoryTime
  exact h.tailCycleProgress

/-- Position-sensitive rank outcome of the three non-clock residuals. -/
inductive PermanentTailTerminalNonClockRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | immediate_insufficient
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime) :
      PermanentTailTerminalNonClockRankOutcome source
  | original_history_blocker
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (firstTime_le_original : firstTime ≤ source.downTime + 1)
      (backtrack : TerminalHistoricalBacktrackCertificate target
        source.returnTime candidate firstTime) :
      PermanentTailTerminalNonClockRankOutcome source
  | forward_budget_progress
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (original_lt_firstTime : source.downTime + 1 < firstTime)
      (budget_drop : missingBelowCount target firstTime <
        missingBelowCount target (source.downTime + 1))
      (backtrack : TerminalHistoricalBacktrackCertificate target
        source.returnTime candidate firstTime) :
      PermanentTailTerminalNonClockRankOutcome source

/-- Non-clock residuals are an immediate numeric obstruction, an original
outer-history blocker, or strict forward history-budget progress.  Both
historical branches also expose the local tail-cycle backtrack edge. -/
theorem PermanentTailTerminalNonClockResidual.rankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : PermanentTailTerminalNonClockResidual source) :
    PermanentTailTerminalNonClockRankOutcome source := by
  cases h with
  | immediate_insufficient valley insufficient =>
      exact .immediate_insufficient valley insufficient
  | immediate_historical candidate firstTime valley blocker hfirst =>
      let fresh : TerminalFreshEndpointCertificate source
          (source.downTime + 1) := {
        origin_le := Nat.le_refl _
        fresh_le_return := Nat.le_of_eq (Eq.symm valley.return_eq)
        fresh_first := source.endpoint_first
        fresh_below := valley.endpoint_below
        canonical_return := source.return_crossing
      }
      let historical : TerminalOuterHistoricalBlockerCertificate source
          (source.downTime + 1) candidate firstTime := {
        fresh := fresh
        blocker := blocker
        firstTime_le_fresh := Nat.le_of_lt hfirst
      }
      exact .original_history_blocker (source.downTime + 1) candidate
        firstTime historical (Nat.le_of_lt hfirst)
        blocker.backtrackCertificate
  | finite_outer_blocker terminalEndpoint candidate firstTime origin_le
      window blocker hfirst =>
      let fresh : TerminalFreshEndpointCertificate source terminalEndpoint := {
        origin_le := origin_le
        fresh_le_return := Nat.le_of_lt
          window.certificate.endpoint_before_return
        fresh_first := window.certificate.suffix.endpoint_first
        fresh_below := window.certificate.suffix.endpoint_below
        canonical_return := window.certificate.suffix.first_return
      }
      let historical : TerminalOuterHistoricalBlockerCertificate source
          terminalEndpoint candidate firstTime := {
        fresh := fresh
        blocker := blocker
        firstTime_le_fresh := hfirst
      }
      by_cases hposition : firstTime ≤ source.downTime + 1
      · exact .original_history_blocker terminalEndpoint candidate firstTime
          historical hposition blocker.backtrackCertificate
      · have horiginalLt : source.downTime + 1 < firstTime := by omega
        have hbudget := missingBelowCount_strict_of_firstAt
          blocker.candidate_below_target horiginalLt
          blocker.candidate_first
        exact .forward_budget_progress terminalEndpoint candidate firstTime
          historical horiginalLt hbudget blocker.backtrackCertificate

end

end Recaman
