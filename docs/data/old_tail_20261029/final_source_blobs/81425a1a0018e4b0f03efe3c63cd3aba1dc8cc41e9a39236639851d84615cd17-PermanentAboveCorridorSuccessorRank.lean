import Recaman.PermanentAboveCorridorTerminalSuccessor

namespace Recaman

noncomputable section

/-! # Discharge-level iteration rank for installed successors

The installed master edge relates two seven-component nodes whose inner
cursors mention the blocker first time of one particular analysis.  Those
cursors do not transport to the successor discharge, so consecutive master
edges need not concatenate.  The coordinates that do transport are exactly
the ones fixed by the installation: the shared history horizon, the installed
crossing anchor, and the recorded old crossing time.

This module extracts that transportable triple as a discharge-level rank.
An installed successor either strictly descends this rank — through anchor
growth or an earlier equal-anchor crossing — or reproduces the parent anchor
at the same crossing time.  The latter case is an exact rank fixed point and
is kept as a typed replay certificate with its full construction chain.
-/

/-- Transportable outer measure of a discharge: shared horizon budget,
remaining crossing-anchor gap, and the old crossing cursor. -/
def terminalDischargeIterationRank (target : Nat) {start : Nat}
    {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Nat × (Nat × Nat) :=
  (missingBelowCount target parent.horizon,
    (terminalCrossingAnchorRank target parent.anchorParent,
      source.oldCrossingTime))

/-- Strict lexicographic progress between two discharges, possibly living on
different parent nodes. -/
def TerminalDischargeIterationProgress (target : Nat)
    {childStart sourceStart : Nat}
    {childParent sourceParent : PhaseSearchNode}
    (child : PermanentTailDischargeReturnCertificate target childStart
      childParent)
    (source : PermanentTailDischargeReturnCertificate target sourceStart
      sourceParent) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
    (terminalDischargeIterationRank target child)
    (terminalDischargeIterationRank target source)

/-- At a shared horizon, strict anchor growth below the target lowers the
remaining anchor gap. -/
theorem terminalDischargeIterationProgress_of_anchorGrowth
    {target childStart sourceStart : Nat}
    {childParent sourceParent : PhaseSearchNode}
    {child : PermanentTailDischargeReturnCertificate target childStart
      childParent}
    {source : PermanentTailDischargeReturnCertificate target sourceStart
      sourceParent}
    (hhorizon : childParent.horizon = sourceParent.horizon)
    (hchildBelow : childParent.anchorParent < target)
    (hgrowth : sourceParent.anchorParent < childParent.anchorParent) :
    TerminalDischargeIterationProgress target child source := by
  unfold TerminalDischargeIterationProgress terminalDischargeIterationRank
  rw [hhorizon]
  exact Prod.Lex.right _
    (Prod.Lex.left _ _
      (Nat.sub_lt_sub_left (Nat.lt_trans hgrowth hchildBelow) hgrowth))

/-- At a shared horizon and anchor, an earlier old crossing cursor is strict
progress in the third coordinate. -/
theorem terminalDischargeIterationProgress_of_earlierCrossing
    {target childStart sourceStart : Nat}
    {childParent sourceParent : PhaseSearchNode}
    {child : PermanentTailDischargeReturnCertificate target childStart
      childParent}
    {source : PermanentTailDischargeReturnCertificate target sourceStart
      sourceParent}
    (hhorizon : childParent.horizon = sourceParent.horizon)
    (hanchor : childParent.anchorParent = sourceParent.anchorParent)
    (hearlier : child.oldCrossingTime < source.oldCrossingTime) :
    TerminalDischargeIterationProgress target child source := by
  unfold TerminalDischargeIterationProgress terminalDischargeIterationRank
  rw [hhorizon, hanchor]
  exact Prod.Lex.right _ (Prod.Lex.right _ hearlier)

/-- Equal horizon, anchor, and old crossing cursor give an exact rank fixed
point. -/
theorem terminalDischargeIterationRank_eq
    {target childStart sourceStart : Nat}
    {childParent sourceParent : PhaseSearchNode}
    {child : PermanentTailDischargeReturnCertificate target childStart
      childParent}
    {source : PermanentTailDischargeReturnCertificate target sourceStart
      sourceParent}
    (hhorizon : childParent.horizon = sourceParent.horizon)
    (hanchor : childParent.anchorParent = sourceParent.anchorParent)
    (htime : child.oldCrossingTime = source.oldCrossingTime) :
    terminalDischargeIterationRank target child =
      terminalDischargeIterationRank target source := by
  unfold terminalDischargeIterationRank
  rw [hhorizon, hanchor, htime]

/-- Exact discharge-level replay: the installed successor reproduces the
parent anchor at the same crossing cursor, so its iteration rank does not
move.  The full construction chain is retained. -/
structure TerminalExactDischargeReplayCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent)
    where
  freshEndpoint : Nat
  candidate : Nat
  firstTime : Nat
  predecessor : Nat
  predecessorFirstTime : Nat
  crossingTime : Nat
  quotient : Nat
  remainder : Nat
  historical : TerminalOuterHistoricalBlockerCertificate source
    freshEndpoint candidate firstTime
  below : BelowTargetHistoricalPredecessorCertificate
    (predecessor := predecessor)
    (predecessorFirstTime := predecessorFirstTime) historical
  crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
    quotient remainder
  install : TerminalSelectedCrossingInstallCertificate crossing
  next : TerminalSelectedCrossingDischargeCertificate install
  anchor_eq : a crossingTime = parent.anchorParent
  time_eq : crossingTime = source.oldCrossingTime
  eligible : source.downTime + 1 ≤ source.oldCrossingTime
  rank_eq : terminalDischargeIterationRank target next.discharge =
    terminalDischargeIterationRank target source

/-- Terminal outcome measured at discharge level: the target occurs, an
established history or semantic edge fires, the successor discharge strictly
descends the iteration rank, or the successor is an exact replay. -/
inductive PermanentTailTerminalIterationOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      PermanentTailTerminalIterationOutcome source
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalIterationOutcome source
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalIterationOutcome source
  | iteration_progress
      (crossingTime : Nat)
      (next : PermanentTailDischargeReturnCertificate target start
        (terminalPredecessorCrossingNode parent crossingTime))
      (next_old_eq : next.oldCrossingTime = crossingTime)
      (iteration : TerminalDischargeIterationProgress target next source) :
      PermanentTailTerminalIterationOutcome source
  | exact_replay
      (replay : TerminalExactDischargeReplayCertificate source) :
      PermanentTailTerminalIterationOutcome source

/-- Every terminal discharge either fires an established global edge or
hands over a successor discharge which strictly descends the transportable
iteration rank; the only remaining case is an exact rank replay. -/
theorem PermanentTailDischargeReturnCertificate.terminalIterationOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalIterationOutcome source := by
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
      | below_master predecessor predecessorFirstTime below _master =>
          by_cases holdEligible :
              source.downTime + 1 ≤ source.oldCrossingTime
          · cases below.crossingRankOutcome with
            | refined_progress crossingTime quotient remainder certificate
                progress =>
                exact .semantic_progress parent
                  (terminalPredecessorCrossingNode parent crossingTime)
                  certificate.refined.toPhaseSemanticInvariant progress
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
