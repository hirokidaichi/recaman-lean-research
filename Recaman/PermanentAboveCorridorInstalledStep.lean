import Recaman.PermanentAboveCorridorMasterRank

namespace Recaman

noncomputable section

/-! # Total installed step of a terminal discharge

This module composes the complete terminal residual tree with the
blocker-predecessor semantic and master-rank pipeline.  A discharge now
returns one of four top-level results:

* strict missing-history progress;
* membership in the finite return-clock candidate list;
* the immediate insufficient-value arithmetic residual;
* an eligible historical predecessor step.

In the historical branch, a chronologically ineligible old crossing is itself
strict history progress.  An eligible branch is normal-ready, an explicit
above-target clock/sign residual, or a below-target installed master-rank
step.  Every below-target master result retains enough crossing data to
reconstruct its semantic installed parent.
-/

/-- Semantic/master outcome of one eligible terminal outer blocker. -/
inductive TerminalOuterHistoricalInstalledStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime) : Prop
  | normal_ready
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (predecessor_certificate : TerminalBlockerPredecessorCertificate
        historical predecessor predecessorFirstTime)
      (invariant : NormalPhaseInvariantAt target
        ⟨firstTime - 1, predecessor, .normal, a (firstTime - 1)⟩
        (firstTime - 1) quotient remainder)
      (backtrack : TerminalHistoricalBacktrackCertificate target
        source.returnTime candidate firstTime) :
      TerminalOuterHistoricalInstalledStepOutcome historical
  | above_residual
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (residual : AboveTargetPredecessorResidual
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical quotient
        remainder)
      (backtrack : TerminalHistoricalBacktrackCertificate target
        source.returnTime candidate firstTime) :
      TerminalOuterHistoricalInstalledStepOutcome historical
  | below_master
      (predecessor predecessorFirstTime : Nat)
      (below : BelowTargetHistoricalPredecessorCertificate
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical)
      (master : TerminalBelowPredecessorMasterRankOutcome below) :
      TerminalOuterHistoricalInstalledStepOutcome historical

/-- Eligible outer blockers enter the full semantic/master pipeline. -/
theorem TerminalOuterHistoricalBlockerCertificate.installedStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (h : TerminalOuterHistoricalBlockerCertificate source freshEndpoint
      candidate firstTime)
    (holdEligible : source.downTime + 1 ≤ source.oldCrossingTime) :
    TerminalOuterHistoricalInstalledStepOutcome h := by
  cases h.predecessorSemanticOutcome with
  | normal_ready predecessor predecessorFirstTime quotient remainder
      predecessor_certificate invariant =>
      exact .normal_ready predecessor predecessorFirstTime quotient remainder
        predecessor_certificate invariant h.blocker.backtrackCertificate
  | above_residual predecessor predecessorFirstTime quotient remainder
      residual =>
      exact .above_residual predecessor predecessorFirstTime quotient remainder
        residual h.blocker.backtrackCertificate
  | below_historical predecessor predecessorFirstTime certificate =>
      exact .below_master predecessor predecessorFirstTime certificate
        (certificate.masterRankOutcome holdEligible)

/-- Every below-target master outcome exposes a selected crossing and its
installed permanent-tail parent. -/
theorem TerminalBelowPredecessorMasterRankOutcome.exists_install
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    (h : TerminalBelowPredecessorMasterRankOutcome below) :
    ∃ crossingTime quotient remainder,
      ∃ crossing : TerminalBelowPredecessorCrossingCertificate below
          crossingTime quotient remainder,
        TerminalSelectedCrossingInstallCertificate crossing := by
  cases h with
  | phase_exit crossingTime quotient remainder certificate progress =>
      exact ⟨crossingTime, quotient, remainder, certificate,
        certificate.install⟩
  | master_progress crossingTime quotient remainder certificate progress =>
      exact ⟨crossingTime, quotient, remainder, certificate,
        certificate.install⟩

/-- Constructor-complete terminal step at discharge level. -/
inductive PermanentTailTerminalInstalledStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalInstalledStepOutcome source
  | finite_return_candidate
      (membership : source.returnTime ∈ terminalReturnCandidates target) :
      PermanentTailTerminalInstalledStepOutcome source
  | immediate_insufficient
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime) :
      PermanentTailTerminalInstalledStepOutcome source
  | historical_step
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalInstalledStepOutcome historical) :
      PermanentTailTerminalInstalledStepOutcome source

/-- Every terminal discharge reaches a proved strict edge, a finite candidate,
the immediate numeric residual, or a typed installed historical step. -/
theorem PermanentTailDischargeReturnCertificate.terminalInstalledStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalInstalledStepOutcome h := by
  rcases h.terminalBudgetProgress_or_outerResidual with
    ⟨terminalEndpoint, firstTime, endpoint_lt_firstTime, budget_drop⟩ |
      outer
  · exact .history_progress firstTime terminalEndpoint budget_drop
  · rcases outer.finiteCandidate_or_nonClockResidual with
      finiteCandidate | nonClock
    · exact .finite_return_candidate finiteCandidate
    · cases nonClock.rankOutcome with
      | immediate_insufficient valley insufficient =>
          exact .immediate_insufficient valley insufficient
      | forward_budget_progress freshEndpoint candidate firstTime historical
          original_lt_firstTime budget_drop backtrack =>
          exact .history_progress firstTime (h.downTime + 1) budget_drop
      | original_history_blocker freshEndpoint candidate firstTime historical
          firstTime_le_original backtrack =>
          by_cases holdEligible :
              h.downTime + 1 ≤ h.oldCrossingTime
          · exact .historical_step freshEndpoint candidate firstTime historical
              (historical.installedStepOutcome holdEligible)
          · have holdBefore : h.oldCrossingTime < h.downTime + 1 :=
              Nat.lt_of_not_ge holdEligible
            have hbudget := missingBelowCount_strict_of_firstAt
              h.downcross.endpoint_below holdBefore h.endpoint_first
            exact .history_progress (h.downTime + 1) h.oldCrossingTime
              hbudget

end

end Recaman
