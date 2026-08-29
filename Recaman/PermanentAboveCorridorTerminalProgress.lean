import Recaman.PermanentAboveCorridorFiniteClosure

namespace Recaman

noncomputable section

/-! # Progress-only terminal classification

After eliminating the finite numeric branch, every remaining constructor can
be flattened into one of four established outcomes: the target occurs,
missing history strictly decreases, a semantic phase node strictly decreases,
or the installed-cycle master rank strictly decreases.  The semantic edge
stores its actual local parent; early, ready, immediate, and selected-crossing
steps therefore retain their precise provenance rather than being forced to
compare against the original discharge parent.
-/

inductive PermanentTailTerminalProgressOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      PermanentTailTerminalProgressOutcome source
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalProgressOutcome source
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalProgressOutcome source
  | installed_master_progress
      (child parentNode : TailInstalledCycleSearchNode)
      (progress : TailInstalledCycleProgress target child parentNode) :
      PermanentTailTerminalProgressOutcome source

/-- Every terminal discharge now yields the target or a strict edge of an
already proved well-founded relation; no numeric or typed residual remains. -/
theorem PermanentTailDischargeReturnCertificate.terminalProgressOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalProgressOutcome source := by
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
              exact .installed_master_progress
                ⟨parent.horizon, a crossingTime, crossingTime,
                  firstTime - 1, .crossing, firstTime - 1, 0⟩
                ⟨parent.horizon, parent.anchorParent,
                  source.oldCrossingTime, firstTime, .discharge,
                  firstTime, 0⟩
                progress

end

end Recaman
