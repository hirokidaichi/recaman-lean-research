import Recaman.PermanentAboveCorridorBlockerPosition

namespace Recaman

noncomputable section

/-! # Master residual of the normalized terminal corridor

This module combines terminal shape, crossing balance, forced reason, and
blocker position into one exhaustive classification.  One constructor is a
strict history-budget step; removing it leaves four explicit outer residuals.
-/

/-- The finite return-clock band in the all-forced insufficient-value branch. -/
structure TerminalFiniteClockBandCertificate
    (target returnTime : Nat) : Prop where
  return_before_target : returnTime < target
  target_lt_twice_clock : target < 2 * (returnTime + 1)

/-- Exhaustive terminal classification retaining all branch provenance. -/
inductive PermanentTailTerminalResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | immediate_insufficient
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime) :
      PermanentTailTerminalResidual source
  | immediate_historical
      (candidate firstTime : Nat)
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (firstTime_lt_endpoint : firstTime < source.downTime + 1) :
      PermanentTailTerminalResidual source
  | finite_insufficient
      (terminalEndpoint : Nat)
      (origin_le : source.downTime + 1 ≤ terminalEndpoint)
      (window : TerminalAllForcedCrossingWindow target terminalEndpoint
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (clock_band : TerminalFiniteClockBandCertificate target
        source.returnTime) :
      PermanentTailTerminalResidual source
  | finite_outer_blocker
      (terminalEndpoint candidate firstTime : Nat)
      (origin_le : source.downTime + 1 ≤ terminalEndpoint)
      (window : TerminalAllForcedCrossingWindow target terminalEndpoint
        source.returnTime)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (firstTime_le_endpoint : firstTime ≤ terminalEndpoint) :
      PermanentTailTerminalResidual source
  | finite_budget_progress
      (terminalEndpoint candidate firstTime : Nat)
      (origin_le : source.downTime + 1 ≤ terminalEndpoint)
      (window : TerminalAllForcedCrossingWindow target terminalEndpoint
        source.returnTime)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (endpoint_lt_firstTime : terminalEndpoint < firstTime)
      (budget_drop : missingBelowCount target firstTime <
        missingBelowCount target terminalEndpoint) :
      PermanentTailTerminalResidual source

/-- Every typed discharge has exactly the exhaustive master terminal
classification above. -/
theorem PermanentTailDischargeReturnCertificate.terminalResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalResidual h := by
  cases h.terminalShape with
  | immediate_valley valley =>
      cases h.strictTerminalCrossingBalance.forcedReason with
      | insufficient_value insufficient =>
          exact .immediate_insufficient valley insufficient
      | historical_blocker candidate firstTime blocker =>
          exact .immediate_historical candidate firstTime valley blocker
            (blocker.firstTime_lt_immediateEndpoint valley)
  | finite_crossing_window terminalEndpoint origin_le window =>
      cases h.strictTerminalCrossingBalance.forcedReason with
      | insufficient_value insufficient =>
          exact .finite_insufficient terminalEndpoint origin_le window
            insufficient {
              return_before_target := window.return_before_target
              target_lt_twice_clock := insufficient.target_lt_twice_clock
            }
      | historical_blocker candidate firstTime blocker =>
          by_cases hposition : firstTime ≤ terminalEndpoint
          · exact .finite_outer_blocker terminalEndpoint candidate firstTime
              origin_le window blocker hposition
          · have hendpointLt : terminalEndpoint < firstTime := by omega
            have hbudget := missingBelowCount_strict_of_firstAt
              blocker.candidate_below_target hendpointLt
              blocker.candidate_first
            exact .finite_budget_progress terminalEndpoint candidate firstTime
              origin_le window blocker hendpointLt hbudget

/-- The four terminal constructors which remain after strict corridor-budget
progress is removed. -/
inductive PermanentTailTerminalOuterResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | immediate_insufficient
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime) :
      PermanentTailTerminalOuterResidual source
  | immediate_historical
      (candidate firstTime : Nat)
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (firstTime_lt_endpoint : firstTime < source.downTime + 1) :
      PermanentTailTerminalOuterResidual source
  | finite_insufficient
      (terminalEndpoint : Nat)
      (origin_le : source.downTime + 1 ≤ terminalEndpoint)
      (window : TerminalAllForcedCrossingWindow target terminalEndpoint
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (clock_band : TerminalFiniteClockBandCertificate target
        source.returnTime) :
      PermanentTailTerminalOuterResidual source
  | finite_outer_blocker
      (terminalEndpoint candidate firstTime : Nat)
      (origin_le : source.downTime + 1 ≤ terminalEndpoint)
      (window : TerminalAllForcedCrossingWindow target terminalEndpoint
        source.returnTime)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (firstTime_le_endpoint : firstTime ≤ terminalEndpoint) :
      PermanentTailTerminalOuterResidual source

/-- Master terminal analysis is either a strict below-history budget step or
one of the four genuine outer residuals. -/
theorem PermanentTailDischargeReturnCertificate.terminalBudgetProgress_or_outerResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    (∃ terminalEndpoint firstTime,
      h.downTime + 1 ≤ terminalEndpoint ∧
      terminalEndpoint < firstTime ∧
      missingBelowCount target firstTime <
        missingBelowCount target terminalEndpoint) ∨
      PermanentTailTerminalOuterResidual h := by
  cases h.terminalResidual with
  | immediate_insufficient valley insufficient =>
      exact Or.inr (.immediate_insufficient valley insufficient)
  | immediate_historical candidate firstTime valley blocker hfirst =>
      exact Or.inr (.immediate_historical candidate firstTime valley
        blocker hfirst)
  | finite_insufficient terminalEndpoint origin_le window insufficient band =>
      exact Or.inr (.finite_insufficient terminalEndpoint origin_le window
        insufficient band)
  | finite_outer_blocker terminalEndpoint candidate firstTime origin_le
      window blocker hfirst =>
      exact Or.inr (.finite_outer_blocker terminalEndpoint candidate
        firstTime origin_le window blocker hfirst)
  | finite_budget_progress terminalEndpoint candidate firstTime origin_le
      window blocker hendpoint hbudget =>
      exact Or.inl ⟨terminalEndpoint, firstTime, origin_le, hendpoint,
        hbudget⟩

end

end Recaman
