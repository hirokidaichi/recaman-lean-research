import Recaman.PermanentAboveCorridorChronologyRank

namespace Recaman

noncomputable section

/-! # Master rank for the installed-cycle recurrence kernel

Immediate crossing-anchor decrease is already a global
`PhaseSearchProgress` exit, whereas the recurrent growth branch moves the
anchor in the opposite numeric direction.  Those two directions cannot share
one plain anchor coordinate.  We therefore keep the phase exit separate and
combine exactly the recurrence kernel.

The seven coordinates are:

1. missing below-target history at the chronology cursor;
2. the remaining crossing-anchor gap `target - anchor`;
3. crossing time;
4. seen-below count at the stationary restart cursor;
5. one-way cycle phase;
6. local seen-below count;
7. tail-minimum value.

Chronology mismatch lowers coordinate one, strict anchor growth lowers
coordinate two, an equal-anchor earlier crossing lowers coordinate three, and
a literal stationary restart lowers coordinate four.  Thus all recurrent
branches use one well-founded relation.
-/

structure TailInstalledCycleSearchNode where
  budgetTime : Nat
  anchor : Nat
  crossingTime : Nat
  restartTime : Nat
  phase : TailCyclePhase
  historyTime : Nat
  minimumValue : Nat
deriving Repr, DecidableEq

def tailInstalledCycleRank (target : Nat)
    (node : TailInstalledCycleSearchNode) :
    Nat × (Nat × (Nat × (Nat × (Nat × (Nat × Nat))))) :=
  (missingBelowCount target node.budgetTime,
    (terminalCrossingAnchorRank target node.anchor,
      (node.crossingTime,
        (seenBelowCount target node.restartTime,
          (node.phase.rank,
            (seenBelowCount target node.historyTime, node.minimumValue))))))

def TailInstalledCycleProgress (target : Nat)
    (child parent : TailInstalledCycleSearchNode) : Prop :=
  Prod.Lex Nat.lt
      (Prod.Lex Nat.lt
        (Prod.Lex Nat.lt
          (Prod.Lex Nat.lt
            (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)))))
    (tailInstalledCycleRank target child)
    (tailInstalledCycleRank target parent)

theorem natSeptLex_wellFounded :
    WellFounded
      (Prod.Lex Nat.lt
        (Prod.Lex Nat.lt
          (Prod.Lex Nat.lt
            (Prod.Lex Nat.lt
              (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)))))) := by
  apply WellFounded.intro
  intro tuple
  exact Prod.lexAccessible
    (Nat.lt_wfRel.wf.apply tuple.1)
    (fun sextuple => natSextLex_wellFounded.apply sextuple)
    tuple.2

theorem tailInstalledCycleProgress_wellFounded (target : Nat) :
    WellFounded (TailInstalledCycleProgress target) := by
  apply WellFounded.intro
  intro node
  generalize hrank : tailInstalledCycleRank target node = rank
  have hacc := natSeptLex_wellFounded.apply rank
  induction hacc generalizing node with
  | intro rank _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrelation :
          Prod.Lex Nat.lt
              (Prod.Lex Nat.lt
                (Prod.Lex Nat.lt
                  (Prod.Lex Nat.lt
                    (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)))))
            (tailInstalledCycleRank target child) rank := by
        simpa [TailInstalledCycleProgress, hrank] using hchild
      exact ih (tailInstalledCycleRank target child) hrelation child rfl

/-- Strict missing-budget progress dominates every inner installed-cycle
coordinate. -/
theorem tailInstalledCycleProgress_of_historyDrop
    {target childBudgetTime parentBudgetTime childAnchor parentAnchor
      childCrossingTime parentCrossingTime childRestartTime parentRestartTime
      childHistoryTime parentHistoryTime childMinimum parentMinimum : Nat}
    {childPhase parentPhase : TailCyclePhase}
    (hdrop : missingBelowCount target childBudgetTime <
      missingBelowCount target parentBudgetTime) :
    TailInstalledCycleProgress target
      ⟨childBudgetTime, childAnchor, childCrossingTime, childRestartTime,
        childPhase, childHistoryTime, childMinimum⟩
      ⟨parentBudgetTime, parentAnchor, parentCrossingTime, parentRestartTime,
        parentPhase, parentHistoryTime, parentMinimum⟩ :=
  Prod.Lex.left _ _ hdrop

/-- At a fixed chronology cursor, strict anchor growth lowers the remaining
target-anchor gap. -/
theorem tailInstalledCycleProgress_of_anchorGrowth
    {target budgetTime childAnchor parentAnchor childCrossingTime
      parentCrossingTime childRestartTime parentRestartTime childHistoryTime
      parentHistoryTime childMinimum parentMinimum : Nat}
    {childPhase parentPhase : TailCyclePhase}
    (hchildBelow : childAnchor < target)
    (hgrowth : parentAnchor < childAnchor) :
    TailInstalledCycleProgress target
      ⟨budgetTime, childAnchor, childCrossingTime, childRestartTime,
        childPhase, childHistoryTime, childMinimum⟩
      ⟨budgetTime, parentAnchor, parentCrossingTime, parentRestartTime,
        parentPhase, parentHistoryTime, parentMinimum⟩ := by
  exact Prod.Lex.right _
    (Prod.Lex.left _ _
      (Nat.sub_lt_sub_left (Nat.lt_trans hgrowth hchildBelow) hgrowth))

/-- Equal anchor plus an earlier crossing time lowers the third coordinate. -/
theorem tailInstalledCycleProgress_of_earlierCrossing
    {target budgetTime anchor childCrossingTime parentCrossingTime
      childRestartTime parentRestartTime childHistoryTime parentHistoryTime
      childMinimum parentMinimum : Nat}
    {childPhase parentPhase : TailCyclePhase}
    (hearlier : childCrossingTime < parentCrossingTime) :
    TailInstalledCycleProgress target
      ⟨budgetTime, anchor, childCrossingTime, childRestartTime,
        childPhase, childHistoryTime, childMinimum⟩
      ⟨budgetTime, anchor, parentCrossingTime, parentRestartTime,
        parentPhase, parentHistoryTime, parentMinimum⟩ := by
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.left _ _ hearlier))

/-- At stationary outer cursors, the blocker restart seen-drop lowers the
fourth coordinate and hides the upward phase reset. -/
theorem tailInstalledCycleProgress_of_restartSeenDrop
    {target budgetTime anchor crossingTime childRestartTime parentRestartTime
      childHistoryTime parentHistoryTime childMinimum parentMinimum : Nat}
    {childPhase parentPhase : TailCyclePhase}
    (hseen : seenBelowCount target childRestartTime <
      seenBelowCount target parentRestartTime) :
    TailInstalledCycleProgress target
      ⟨budgetTime, anchor, crossingTime, childRestartTime,
        childPhase, childHistoryTime, childMinimum⟩
      ⟨budgetTime, anchor, crossingTime, parentRestartTime,
        parentPhase, parentHistoryTime, parentMinimum⟩ := by
  exact Prod.Lex.right _
    (Prod.Lex.right _
      (Prod.Lex.right _ (Prod.Lex.left _ _ hseen)))

/-- Installed-cycle outcome: an immediate exit to the global phase rank, or
one strict edge of the unified recurrent master rank. -/
inductive TerminalBelowPredecessorMasterRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) : Prop
  | phase_exit
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      TerminalBelowPredecessorMasterRankOutcome below
  | master_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : TailInstalledCycleProgress target
        ⟨parent.horizon, a crossingTime, crossingTime, firstTime - 1,
          .crossing, firstTime - 1, 0⟩
        ⟨parent.horizon, parent.anchorParent, source.oldCrossingTime,
          firstTime, .discharge, firstTime, 0⟩) :
      TerminalBelowPredecessorMasterRankOutcome below

/-- Every eligible below-target predecessor either exits through the existing
global phase rank or strictly descends the installed-cycle master rank. -/
theorem BelowTargetHistoricalPredecessorCertificate.masterRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical)
    (holdEligible : source.downTime + 1 ≤ source.oldCrossingTime) :
    TerminalBelowPredecessorMasterRankOutcome h := by
  cases h.crossingRankOutcome with
  | refined_progress crossingTime quotient remainder certificate progress =>
      exact .phase_exit crossingTime quotient remainder certificate progress
  | anchor_growth crossingTime quotient remainder certificate
      anchor_nondecreasing =>
      by_cases hstrict : parent.anchorParent < a crossingTime
      · have hmaster : TailInstalledCycleProgress target
            ⟨parent.horizon, a crossingTime, crossingTime, firstTime - 1,
              .crossing, firstTime - 1, 0⟩
            ⟨parent.horizon, parent.anchorParent, source.oldCrossingTime,
              firstTime, .discharge, firstTime, 0⟩ :=
          tailInstalledCycleProgress_of_anchorGrowth
            certificate.first_crossing.crossing.below hstrict
        exact .master_progress crossingTime quotient remainder certificate
          hmaster
      · have hsame : a crossingTime = parent.anchorParent := by omega
        by_cases hearlier : crossingTime < source.oldCrossingTime
        · have hmaster : TailInstalledCycleProgress target
              ⟨parent.horizon, a crossingTime, crossingTime, firstTime - 1,
                .crossing, firstTime - 1, 0⟩
              ⟨parent.horizon, parent.anchorParent, source.oldCrossingTime,
                firstTime, .discharge, firstTime, 0⟩ := by
            rw [← hsame]
            exact tailInstalledCycleProgress_of_earlierCrossing hearlier
          exact .master_progress crossingTime quotient remainder certificate
            hmaster
        · have hreturnLe :=
            source.returnTime_le_oldCrossingTime holdEligible
          have hcrossingLe := certificate.crossingTime_le_return
          have htime : crossingTime = source.oldCrossingTime := by omega
          have hseen := certificate.backtrack.seen_gain
          have hmaster : TailInstalledCycleProgress target
              ⟨parent.horizon, a crossingTime, crossingTime, firstTime - 1,
                .crossing, firstTime - 1, 0⟩
              ⟨parent.horizon, parent.anchorParent, source.oldCrossingTime,
                firstTime, .discharge, firstTime, 0⟩ := by
            rw [← hsame, ← htime]
            exact tailInstalledCycleProgress_of_restartSeenDrop hseen
          exact .master_progress crossingTime quotient remainder certificate
            hmaster

/-- A chronology mismatch of an installed next discharge is an edge of the
same master rank, through its outermost history coordinate. -/
theorem TerminalSelectedCrossingChronologyProgressCertificate.masterProgress
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
    {next : TerminalSelectedCrossingDischargeCertificate install}
    (h : TerminalSelectedCrossingChronologyProgressCertificate next) :
    TailInstalledCycleProgress target
      ⟨next.discharge.downTime + 1, a crossingTime, crossingTime,
        firstTime, .discharge, firstTime, 0⟩
      ⟨crossingTime, a crossingTime, crossingTime,
        firstTime, .discharge, firstTime, 0⟩ :=
  tailInstalledCycleProgress_of_historyDrop h.missing_drop

end

end Recaman
