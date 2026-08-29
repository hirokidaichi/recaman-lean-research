import Recaman.PermanentAboveCorridorInstalledStep
import Recaman.EarlyRepresentativeComplete
import Recaman.OrbitReadyComplete

namespace Recaman

noncomputable section

/-! # Complete closure of an above-target blocker predecessor

The earlier predecessor of a terminal blocker may already be at or above the
target.  Its clock has exactly two cases:

* if `target ≤ firstTime`, the actual predecessor state at
  `firstTime - 1` is an orbit-ready normal node;
* otherwise, the same actual state can be stored at the old ready history
  horizon as a complete early representative.

Both existing APIs are locally total: they return the target or a semantic
phase-rank child.  No potential-sign residual is needed.  Combining this with
the below-target master branch removes the former above clock/sign residual
from the discharge-level terminal outcome.
-/

def terminalCurrentPredecessorNode (time : Nat) : PhaseSearchNode :=
  ⟨time, a time, .normal, a time⟩

def terminalHistoricalPredecessorNode
    (parent : PhaseSearchNode) (time : Nat) : PhaseSearchNode :=
  ⟨parent.horizon, a time, .normal, a time⟩

/-- Complete eligible historical blocker result after closing both above
clock cases. -/
inductive TerminalOuterHistoricalCompleteStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime) : Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      TerminalOuterHistoricalCompleteStepOutcome historical
  | early_step
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (predecessor_certificate : TerminalBlockerPredecessorCertificate
        historical predecessor predecessorFirstTime)
      (early : EarlyRepresentativeCertificate target
        (terminalHistoricalPredecessorNode parent (firstTime - 1))
        (firstTime - 1) quotient remainder)
      (child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalHistoricalPredecessorNode parent (firstTime - 1)))
      (backtrack : TerminalHistoricalBacktrackCertificate target
        source.returnTime candidate firstTime) :
      TerminalOuterHistoricalCompleteStepOutcome historical
  | ready_step
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (predecessor_certificate : TerminalBlockerPredecessorCertificate
        historical predecessor predecessorFirstTime)
      (ready : OrbitReadyNormalCertificate target
        (terminalCurrentPredecessorNode (firstTime - 1))
        (firstTime - 1) quotient remainder)
      (child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalCurrentPredecessorNode (firstTime - 1)))
      (backtrack : TerminalHistoricalBacktrackCertificate target
        source.returnTime candidate firstTime) :
      TerminalOuterHistoricalCompleteStepOutcome historical
  | below_master
      (predecessor predecessorFirstTime : Nat)
      (below : BelowTargetHistoricalPredecessorCertificate
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical)
      (master : TerminalBelowPredecessorMasterRankOutcome below) :
      TerminalOuterHistoricalCompleteStepOutcome historical

/-- Above predecessors close through the early or orbit-ready total local
theorem; below predecessors retain the installed master-rank outcome. -/
theorem TerminalOuterHistoricalBlockerCertificate.completeStepOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (h : TerminalOuterHistoricalBlockerCertificate source freshEndpoint
      candidate firstTime)
    (holdEligible : source.downTime + 1 ≤ source.oldCrossingTime) :
    TerminalOuterHistoricalCompleteStepOutcome h := by
  rcases h.exists_predecessorCertificate with
    ⟨predecessor, predecessorFirstTime, hpredecessor⟩
  rcases hpredecessor.target_position with hbelow | habove
  · let below := hpredecessor.toBelowTargetHistorical hbelow
    exact .below_master predecessor predecessorFirstTime below
      (below.masterRankOutcome holdEligible)
  · have hfirstPositive := h.blocker.backtrackCertificate.firstTime_positive
    have htimePositive : 0 < firstTime - 1 := by
      by_cases hzero : firstTime - 1 = 0
      · have heq := hpredecessor.predecessor_eq
        have haZero : a 0 = 0 := rfl
        rw [hzero, haZero] at heq
        have htargetPositive := source.combined.tail.target_positive
        omega
      · exact Nat.zero_lt_of_ne_zero hzero
    rcases exists_coordinatesAt htimePositive with
      ⟨quotient, remainder, hcoordinates⟩
    have htargetValue : target ≤ a (firstTime - 1) := by
      rw [hpredecessor.predecessor_eq]
      exact habove
    have hbacktrack := h.blocker.backtrackCertificate
    by_cases hreadyClock : target ≤ firstTime
    · have hready : OrbitReadyNormalCertificate target
          (terminalCurrentPredecessorNode (firstTime - 1))
          (firstTime - 1) quotient remainder := {
        target_positive := source.combined.tail.target_positive
        node_eq := rfl
        time_ready := by omega
        target_le_value := htargetValue
        coordinates := hcoordinates
      }
      rcases hready.phaseSemanticStep with hoccurs | hchild
      · rcases hoccurs with ⟨witness, hvalue⟩
        exact .target_occurs witness hvalue
      · rcases hchild with ⟨child, hsemantic, hprogress⟩
        exact .ready_step predecessor predecessorFirstTime quotient remainder
          hpredecessor hready child hsemantic hprogress hbacktrack
    · have hrepresentativeLe :
          firstTime - 1 ≤ parent.horizon := by
        have hfirstReturn := h.blocker.firstTime_lt_return
        have hreturnHorizon := source.return_before_parentHorizon
        omega
      have hextended : ExtendedHistoryNormalCertificate target
          (terminalHistoricalPredecessorNode parent (firstTime - 1))
          (firstTime - 1) quotient remainder := {
        target_positive := source.combined.tail.target_positive
        node_eq := rfl
        representative_le_horizon := hrepresentativeLe
        horizon_time_ready := by
          simpa [terminalHistoricalPredecessorNode] using
            source.combined.crossing.ready_crossing.horizon_ready
        target_le_value := htargetValue
        coordinates := hcoordinates
      }
      have hearly : EarlyRepresentativeCertificate target
          (terminalHistoricalPredecessorNode parent (firstTime - 1))
          (firstTime - 1) quotient remainder := {
        extended := hextended
        not_ready := by omega
      }
      rcases hearly.phaseSemanticStep with hoccurs | hchild
      · rcases hoccurs with ⟨witness, hvalue⟩
        exact .target_occurs witness hvalue
      · rcases hchild with ⟨child, hsemantic, hprogress⟩
        exact .early_step predecessor predecessorFirstTime quotient remainder
          hpredecessor hearly child hsemantic hprogress hbacktrack

/-- Terminal total outcome after removing the above clock/sign residual. -/
inductive PermanentTailTerminalCompleteInstalledOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalCompleteInstalledOutcome source
  | finite_return_candidate
      (membership : source.returnTime ∈ terminalReturnCandidates target) :
      PermanentTailTerminalCompleteInstalledOutcome source
  | immediate_insufficient
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime) :
      PermanentTailTerminalCompleteInstalledOutcome source
  | historical_complete
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalCompleteStepOutcome historical) :
      PermanentTailTerminalCompleteInstalledOutcome source

/-- Complete refinement of the previous total installed step. -/
theorem PermanentTailDischargeReturnCertificate.terminalCompleteInstalledOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalCompleteInstalledOutcome h := by
  cases h.terminalInstalledStepOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | finite_return_candidate membership =>
      exact .finite_return_candidate membership
  | immediate_insufficient valley insufficient =>
      exact .immediate_insufficient valley insufficient
  | historical_step freshEndpoint candidate firstTime historical installed =>
      exact .historical_complete freshEndpoint candidate firstTime historical
        (historical.completeStepOutcome installed.eligible)

end

end Recaman
