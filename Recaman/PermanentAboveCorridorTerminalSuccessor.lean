import Recaman.PermanentAboveCorridorTerminalProgress

namespace Recaman

noncomputable section

/-! # Successor-carrying installed terminal progress

The generic installed-master edge proves termination but hides the semantic
object to analyze next.  In the historical below-target branch, the selected
crossing can be installed as a permanent-tail parent and the next discharge
can already be reconstructed.  This module retains that entire chain in the
terminal outcome.
-/

inductive PermanentTailTerminalSuccessorOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      PermanentTailTerminalSuccessorOutcome source
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalSuccessorOutcome source
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalSuccessorOutcome source
  | installed_successor
      (freshEndpoint candidate firstTime predecessor predecessorFirstTime
        crossingTime quotient remainder : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (below : BelowTargetHistoricalPredecessorCertificate
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical)
      (crossing : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (install : TerminalSelectedCrossingInstallCertificate crossing)
      (next : Nonempty (TerminalSelectedCrossingDischargeCertificate install))
      (progress : TailInstalledCycleProgress target
        ⟨parent.horizon, a crossingTime, crossingTime, firstTime - 1,
          .crossing, firstTime - 1, 0⟩
        ⟨parent.horizon, parent.anchorParent, source.oldCrossingTime,
          firstTime, .discharge, firstTime, 0⟩) :
      PermanentTailTerminalSuccessorOutcome source

/-- Every installed recurrent edge now carries the selected semantic parent
and an actual next-discharge existence proof. -/
theorem PermanentTailDischargeReturnCertificate.terminalSuccessorOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalSuccessorOutcome source := by
  cases source.terminalFiniteClosedOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | immediate_semantic valley insufficient immediate =>
      cases immediate with
      | target_occurs witness value_eq =>
          exact .target_occurs witness value_eq
      | semantic_step child semantic progress =>
          exact .semantic_progress (targetStartNode (source.downTime + 2))
            child semantic progress
  | historical_complete freshEndpoint candidate firstTime historical
      complete =>
      cases complete with
      | target_occurs witness value_eq =>
          exact .target_occurs witness value_eq
      | early_step predecessor predecessorFirstTime quotient remainder
          predecessor_certificate early child semantic progress backtrack =>
          exact .semantic_progress
            (terminalHistoricalPredecessorNode parent (firstTime - 1))
            child semantic progress
      | ready_step predecessor predecessorFirstTime quotient remainder
          predecessor_certificate ready child semantic progress backtrack =>
          exact .semantic_progress
            (terminalCurrentPredecessorNode (firstTime - 1))
            child semantic progress
      | below_master predecessor predecessorFirstTime below master =>
          cases master with
          | phase_exit crossingTime quotient remainder certificate progress =>
              exact .semantic_progress parent
                (terminalPredecessorCrossingNode parent crossingTime)
                certificate.refined.toPhaseSemanticInvariant progress
          | master_progress crossingTime quotient remainder certificate
              progress =>
              let install := certificate.install
              exact .installed_successor freshEndpoint candidate firstTime
                predecessor predecessorFirstTime crossingTime quotient
                remainder historical below certificate install
                install.exists_nextDischarge progress

/-- The successor package exposes a discharge whose parent is definitionally
the installed selected crossing node. -/
def TerminalSelectedCrossingDischargeCertificate.parent_is_installed
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
    (next : TerminalSelectedCrossingDischargeCertificate install) :
    PermanentTailDischargeReturnCertificate target start
      (terminalPredecessorCrossingNode parent crossingTime) :=
  next.discharge

end

end Recaman
