import Recaman.PermanentAboveCorridorAboveClosure
import Recaman.CanonicalOracle

namespace Recaman

noncomputable section

/-! # Semantic closure of the immediate terminal valley

The immediate terminal branch need not be forced into the finite return-clock
band.  Its exact two-step equation is stronger:

`a (downTime + 2) = a downTime + 1`.

The source value is strictly above the target.  Taking its first occurrence
therefore gives a target-valid value strictly below the post-valley value,
which is precisely a `CoverageStep`.  The existing canonical coverage
adapter returns the target or a strict semantic phase-rank child.  Thus the
immediate insufficient-value residual disappears entirely; only the finite
return candidate remains as a numeric terminal branch.
-/

/-- The exact immediate rebound supplies a coverage step from its post-valley
value back to the source value. -/
theorem ImmediateHistoricalValleyCertificate.coverageStep
    {target downTime returnTime : Nat}
    (h : ImmediateHistoricalValleyCertificate target downTime returnTime) :
    CoverageStep target (a (downTime + 2)) (downTime + 2) := by
  rcases history_member_has_firstAt
      (current_mem_valuesThrough downTime) with
    ⟨firstTime, _, hfirst⟩
  exact Or.inr ⟨a downTime, firstTime, Nat.le_of_lt h.source_above, hfirst,
    by rw [h.valley_equation]; omega⟩

/-- Semantic result of closing an immediate insufficient terminal branch. -/
inductive ImmediateTerminalSemanticOutcome
    (target downTime returnTime : Nat) : Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      ImmediateTerminalSemanticOutcome target downTime returnTime
  | semantic_step
      (child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child
        (targetStartNode (downTime + 2))) :
      ImmediateTerminalSemanticOutcome target downTime returnTime

/-- The immediate valley closes through the ordinary canonical coverage
adapter, independently of the insufficient-value subcertificate. -/
theorem ImmediateHistoricalValleyCertificate.semanticOutcome
    {target downTime returnTime : Nat}
    (h : ImmediateHistoricalValleyCertificate target downTime returnTime)
    (htarget : 0 < target) :
    ImmediateTerminalSemanticOutcome target downTime returnTime := by
  rcases canonicalCoverage_phaseSemantic htarget h.coverageStep with
    hoccurs | hchild
  · rcases hoccurs with ⟨witness, hvalue⟩
    exact .target_occurs witness hvalue
  · rcases hchild with ⟨child, hsemantic, hprogress⟩
    exact .semantic_step child hsemantic hprogress

/-- Terminal outcome after eliminating the immediate numeric residual. -/
inductive PermanentTailTerminalSemanticallyClosedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalSemanticallyClosedOutcome source
  | finite_return_candidate
      (membership : source.returnTime ∈ terminalReturnCandidates target) :
      PermanentTailTerminalSemanticallyClosedOutcome source
  | immediate_semantic
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (outcome : ImmediateTerminalSemanticOutcome target source.downTime
        source.returnTime) :
      PermanentTailTerminalSemanticallyClosedOutcome source
  | historical_complete
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalCompleteStepOutcome historical) :
      PermanentTailTerminalSemanticallyClosedOutcome source

/-- Complete terminal refinement: the sole numeric branch is now the explicit
finite return candidate list. -/
theorem PermanentTailDischargeReturnCertificate.terminalSemanticallyClosedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalSemanticallyClosedOutcome h := by
  cases h.terminalCompleteInstalledOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | finite_return_candidate membership =>
      exact .finite_return_candidate membership
  | immediate_insufficient valley insufficient =>
      exact .immediate_semantic valley insufficient
        (valley.semanticOutcome h.combined.tail.target_positive)
  | historical_complete freshEndpoint candidate firstTime historical
      outcome =>
      exact .historical_complete freshEndpoint candidate firstTime historical
        outcome

end

end Recaman
