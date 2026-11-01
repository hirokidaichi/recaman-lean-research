import Recaman.RefinedSemanticOutcome
import Recaman.PermanentAboveCorridorSuccessorRank

namespace Recaman

noncomputable section

/-! # Carrying the pinned semantic branch into the discharge iteration

`PermanentTailTerminalIterationOutcome` is the first stage of the chain which
actually reaches the summit theorem, and it still stores the broad
`semantic_progress` payload: a `PhaseSemanticInvariant` child under an
existentially quantified step parent.  Both halves of that payload can be
manufactured, so the branch survives to the top carrying nothing.

This module keeps every existing declaration untouched and adds the same
stage with the four pinned branches of `RefinedSemanticOutcome` in place of
the broad one.  The remaining constructors — history progress, installed
iteration progress, and the exact replay fixed point — keep their payload
verbatim.

## Why the forgetful edge may not be propagated

`RefinedDomainEdge` forgets which certificate produced the edge and keeps only
"both endpoints are refined".  That statement is *already* a consequence of
positivity, as `occurs_or_refinedDomainEdge_of_pos` below shows: the canonical
start is itself a refined node and `OrbitReadyNormalInvariant.refinedStep` is
locally total on it.  Collapsing to the forgetful shape while climbing the
chain would therefore restore exactly the defect being removed.  The payload
transported here keeps the generating certificate in every constructor.
-/

/-! ## The forgetful edge is free -/

/-- The canonical start of any positive target is a refined node with a
locally total refined step, so a refined edge exists without any part of the
permanent-tail analysis. -/
theorem occurs_or_refinedDomainEdge_of_pos
    {target : Nat} (htarget : 0 < target) :
    (∃ witness, a witness = target) ∨ RefinedDomainEdge target := by
  rcases exists_targetStartNode htarget with ⟨node, hstart⟩
  have hready : OrbitReadyNormalInvariant target node :=
    hstart.toOrbitReadyNormalInvariant htarget
  rcases hready.refinedStep with hoccurs | ⟨child, hchild, hprogress⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨node, child, Or.inl (Or.inl hready), hchild, hprogress⟩

/-- Consequently a least missing target owns a refined edge outright.  The
forgetful shape is thus useless as a summit disjunct. -/
theorem LeastMissingTarget.refinedDomainEdge
    {target : Nat} (h : LeastMissingTarget target) :
    RefinedDomainEdge target := by
  rcases occurs_or_refinedDomainEdge_of_pos h.target_pos with
    hoccurs | hedge
  · exact False.elim (h.target_missing hoccurs)
  · exact hedge

/-! ## The transported payload -/

/-- The four pinned refined semantic branches of one terminal discharge.
Each branch names its step parent as a function of the certificate's own
clocks and proves that the child lies in the refined recursion domain. -/
inductive RefinedTerminalSemanticStep
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | immediate
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (representative : ExtendedHistoryNormalInvariant target
        (terminalHistoricalPredecessorNode parent (source.downTime + 2)))
      (child : PhaseSearchNode)
      (refined : OrbitReadyRefinedInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalHistoricalPredecessorNode parent (source.downTime + 2))) :
      RefinedTerminalSemanticStep source
  | early
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (representative : ExtendedHistoryNormalInvariant target
        (terminalHistoricalPredecessorNode parent (firstTime - 1)))
      (child : PhaseSearchNode)
      (refined : OrbitReadyRefinedInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalHistoricalPredecessorNode parent (firstTime - 1))) :
      RefinedTerminalSemanticStep source
  | ready
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (representative : OrbitReadyNormalInvariant target
        (terminalCurrentPredecessorNode (firstTime - 1)))
      (child : PhaseSearchNode)
      (refined : OrbitReadyRefinedInvariant target child)
      (progress : PhaseSearchProgress target child
        (terminalCurrentPredecessorNode (firstTime - 1))) :
      RefinedTerminalSemanticStep source
  | crossing
      (crossingTime : Nat)
      (refined : OrbitReadyRefinedInvariant target
        (terminalPredecessorCrossingNode parent crossingTime))
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      RefinedTerminalSemanticStep source

/-- Certificate-tied refined semantic edge, indexed only by the target and the
tail start.  This is the payload which travels up the chain: the discharge or
combined certificate that produced the edge is retained, so the shape cannot
be produced from positivity alone. -/
inductive RefinedSemanticEdge (target start : Nat) : Prop
  | discharge_step
      (dischargeParent : PhaseSearchNode)
      (discharge : PermanentTailDischargeReturnCertificate target start
        dischargeParent)
      (step : RefinedTerminalSemanticStep discharge) :
      RefinedSemanticEdge target start
  | mounted_crossing
      (mountedParent : PhaseSearchNode)
      (minimumTime predecessorFirstTime crossingTime : Nat)
      (combined : PermanentTailCombinedCertificate target start mountedParent
        minimumTime predecessorFirstTime)
      (ready : ReadyCrossingSearchInvariant target
        (terminalPredecessorCrossingNode mountedParent crossingTime))
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode mountedParent crossingTime)
        mountedParent) :
      RefinedSemanticEdge target start

/-- Forgetting the certificate.  Use this only at the final connection to the
restricted oracle recursion, never while climbing the chain. -/
theorem RefinedTerminalSemanticStep.toRefinedDomainEdge
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : RefinedTerminalSemanticStep source) :
    RefinedDomainEdge target := by
  cases h with
  | immediate _valley representative child refined progress =>
      exact ⟨_, child, Or.inr (Or.inl representative), refined, progress⟩
  | early _freshEndpoint _candidate _firstTime _historical representative
      child refined progress =>
      exact ⟨_, child, Or.inr (Or.inl representative), refined, progress⟩
  | ready _freshEndpoint _candidate _firstTime _historical representative
      child refined progress =>
      exact ⟨_, child, Or.inl (Or.inl representative), refined, progress⟩
  | crossing _crossingTime refined progress =>
      exact ⟨parent, _, source.parent_orbitReadyRefined, refined, progress⟩

/-- Forgetting the certificate at edge level. -/
theorem RefinedSemanticEdge.toRefinedDomainEdge
    {target start : Nat} (h : RefinedSemanticEdge target start) :
    RefinedDomainEdge target := by
  cases h with
  | discharge_step _dischargeParent _discharge step =>
      exact step.toRefinedDomainEdge
  | mounted_crossing mountedParent _minimumTime _predecessorFirstTime
      _crossingTime combined ready progress =>
      exact ⟨mountedParent, _,
        Or.inr (Or.inr combined.crossing.ready_crossing.crossing),
        Or.inr (Or.inr ready.crossing), progress⟩

/-! ## Refined discharge-level iteration outcome -/

/-- Refinement of `PermanentTailTerminalIterationOutcome`: the broad
`semantic_progress` constructor is replaced by the pinned
`RefinedTerminalSemanticStep`.  Every other constructor is unchanged. -/
inductive RefinedTerminalIterationOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      RefinedTerminalIterationOutcome source
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      RefinedTerminalIterationOutcome source
  | refined_semantic
      (step : RefinedTerminalSemanticStep source) :
      RefinedTerminalIterationOutcome source
  | iteration_progress
      (crossingTime : Nat)
      (next : PermanentTailDischargeReturnCertificate target start
        (terminalPredecessorCrossingNode parent crossingTime))
      (next_old_eq : next.oldCrossingTime = crossingTime)
      (iteration : TerminalDischargeIterationProgress target next source) :
      RefinedTerminalIterationOutcome source
  | exact_replay
      (replay : TerminalExactDischargeReplayCertificate source) :
      RefinedTerminalIterationOutcome source

/-- Refined form of `terminalIterationOutcome`.  The three historical
semantic branches reuse the refined local steps which were already available
at the point where the broad step was taken; the immediate valley branch uses
the extended-history representative at the parent horizon.  The installed
anchor-growth analysis is unchanged. -/
theorem PermanentTailDischargeReturnCertificate.refinedTerminalIterationOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    RefinedTerminalIterationOutcome source := by
  cases source.terminalFiniteClosedOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | immediate_semantic valley _insufficient _immediate =>
      rcases exists_coordinatesAt (n := source.downTime + 2) (by omega) with
        ⟨quotient, remainder, hcoordinates⟩
      have hextended := source.immediateValley_extended valley quotient
        remainder hcoordinates
      rcases hextended.refinedStep with ⟨witness, hvalue⟩ |
        ⟨child, hchild, hprogress⟩
      · exact .target_occurs witness hvalue
      · exact .refined_semantic (.immediate valley
          ⟨source.downTime + 2, quotient, remainder, hextended⟩
          child hchild hprogress)
  | historical_complete freshEndpoint candidate firstTime historical
      complete =>
      cases complete with
      | target_occurs witness value_eq =>
          exact .target_occurs witness value_eq
      | early_step _predecessor _predecessorFirstTime quotient remainder
          _predecessorCertificate early _child _semantic _progress
          _backtrack =>
          rcases early.refinedStep with ⟨witness, hvalue⟩ |
            ⟨child, hchild, hprogress⟩
          · exact .target_occurs witness hvalue
          · exact .refined_semantic (.early freshEndpoint candidate firstTime
              historical
              ⟨firstTime - 1, quotient, remainder, early.extended⟩
              child hchild hprogress)
      | ready_step _predecessor _predecessorFirstTime quotient remainder
          _predecessorCertificate ready _child _semantic _progress
          _backtrack =>
          rcases ready.refinedStep with ⟨witness, hvalue⟩ |
            ⟨child, hchild, hprogress⟩
          · exact .target_occurs witness hvalue
          · exact .refined_semantic (.ready freshEndpoint candidate firstTime
              historical ⟨firstTime - 1, quotient, remainder, ready⟩
              child hchild hprogress)
      | below_master predecessor predecessorFirstTime below _master =>
          by_cases holdEligible :
              source.downTime + 1 ≤ source.oldCrossingTime
          · cases below.crossingRankOutcome with
            | refined_progress crossingTime quotient remainder certificate
                progress =>
                exact .refined_semantic
                  (.crossing crossingTime certificate.refined progress)
            | anchor_growth crossingTime quotient remainder certificate
                anchor_nondecreasing =>
                let install := certificate.install
                obtain ⟨next⟩ := install.exists_nextDischarge
                by_cases hstrict : parent.anchorParent < a crossingTime
                · have hiteration : TerminalDischargeIterationProgress target
                      next.discharge source :=
                    terminalDischargeIterationProgress_of_anchorGrowth rfl
                      certificate.first_crossing.crossing.below hstrict
                  exact .iteration_progress crossingTime next.discharge
                    next.old_crossing_time_eq hiteration
                · have hsame : a crossingTime = parent.anchorParent := by
                    omega
                  by_cases hearlier :
                      crossingTime < source.oldCrossingTime
                  · have hiteration : TerminalDischargeIterationProgress
                        target next.discharge source :=
                      terminalDischargeIterationProgress_of_earlierCrossing
                        rfl hsame
                        (by rw [next.old_crossing_time_eq]; exact hearlier)
                    exact .iteration_progress crossingTime next.discharge
                      next.old_crossing_time_eq hiteration
                  · have hreturnLe :=
                      source.returnTime_le_oldCrossingTime holdEligible
                    have hcrossingLe := certificate.crossingTime_le_return
                    have htime : crossingTime = source.oldCrossingTime := by
                      omega
                    have hrank : terminalDischargeIterationRank target
                        next.discharge =
                        terminalDischargeIterationRank target source :=
                      terminalDischargeIterationRank_eq rfl hsame
                        (by rw [next.old_crossing_time_eq]; exact htime)
                    exact .exact_replay {
                      freshEndpoint := freshEndpoint
                      candidate := candidate
                      firstTime := firstTime
                      predecessor := predecessor
                      predecessorFirstTime := predecessorFirstTime
                      crossingTime := crossingTime
                      quotient := quotient
                      remainder := remainder
                      historical := historical
                      below := below
                      crossing := certificate
                      install := install
                      next := next
                      anchor_eq := hsame
                      time_eq := htime
                      eligible := holdEligible
                      rank_eq := hrank
                    }
          · have hbudget : TerminalChronologyHistoryProgress target
                (source.downTime + 1) source.downTime :=
              ⟨missingBelowCount_strict_of_firstAt
                source.downcross.endpoint_below
                (show source.downTime < source.downTime + 1 by omega)
                source.endpoint_first,
                source.terminalHistoryCursor (by omega)⟩
            exact .history_progress (source.downTime + 1)
              source.downTime hbudget

end

end Recaman
