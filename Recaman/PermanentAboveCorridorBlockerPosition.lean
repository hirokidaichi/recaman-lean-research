import Recaman.PermanentAboveCorridorBlocker

namespace Recaman

noncomputable section

/-! # Position of the terminal historical blocker

The final positive subtraction blocker either belongs to history at or
before the normalized fresh endpoint, or first appears strictly inside the
final canonical corridor.  The latter alternative consumes below-target
history budget.  The immediate valley cannot take this latter branch because
its fresh endpoint is the return predecessor itself.
-/

/-- Total position-sensitive outcome of the final forced subtraction. -/
inductive NormalizedTerminalBlockerOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | insufficient_value
      (freshEndpoint : Nat)
      (fresh : TerminalFreshEndpointCertificate source freshEndpoint)
      (certificate : TerminalInsufficientValueCertificate target
        source.returnTime) :
      NormalizedTerminalBlockerOutcome source
  | blocker_at_or_before_fresh
      (freshEndpoint candidate firstTime : Nat)
      (fresh : TerminalFreshEndpointCertificate source freshEndpoint)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (firstTime_le_fresh : firstTime ≤ freshEndpoint) :
      NormalizedTerminalBlockerOutcome source
  | blocker_after_fresh
      (freshEndpoint candidate firstTime : Nat)
      (fresh : TerminalFreshEndpointCertificate source freshEndpoint)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (fresh_lt_firstTime : freshEndpoint < firstTime)
      (budget_drop : missingBelowCount target firstTime <
        missingBelowCount target freshEndpoint) :
      NormalizedTerminalBlockerOutcome source

/-- The normalized terminal interface classifies a historical blocker by its
position; a blocker first seen after the fresh endpoint strictly lowers the
below-target history budget. -/
theorem NormalizedTerminalCrossingData.blockerOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : NormalizedTerminalCrossingData source) :
    NormalizedTerminalBlockerOutcome source := by
  rcases h.fresh_endpoint with ⟨freshEndpoint, hfresh⟩
  cases h.balance.forcedReason with
  | insufficient_value certificate =>
      exact .insufficient_value freshEndpoint hfresh certificate
  | historical_blocker candidate firstTime blocker =>
      by_cases hposition : firstTime ≤ freshEndpoint
      · exact .blocker_at_or_before_fresh freshEndpoint candidate firstTime
          hfresh blocker hposition
      · have hfreshLt : freshEndpoint < firstTime := by omega
        have hbudget := missingBelowCount_strict_of_firstAt
          blocker.candidate_below_target hfreshLt blocker.candidate_first
        exact .blocker_after_fresh freshEndpoint candidate firstTime
          hfresh blocker hfreshLt hbudget

/-- In an immediate historical valley, every positive final blocker occurs
strictly before the fresh endpoint, since that endpoint equals the return
predecessor. -/
theorem TerminalHistoricalBlockerCertificate.firstTime_lt_immediateEndpoint
    {target downTime returnTime candidate firstTime : Nat}
    (h : TerminalHistoricalBlockerCertificate target returnTime candidate
      firstTime)
    (hvalley : ImmediateHistoricalValleyCertificate target downTime
      returnTime) :
    firstTime < downTime + 1 := by
  rw [← hvalley.return_eq]
  exact h.firstTime_lt_return

/-- Direct discharge-level adapter for the position-sensitive blocker
classification. -/
theorem PermanentTailDischargeReturnCertificate.terminalBlockerOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    NormalizedTerminalBlockerOutcome h :=
  h.normalizedTerminalCrossingData.blockerOutcome

end

end Recaman
