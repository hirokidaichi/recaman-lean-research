import Recaman.PermanentAboveCorridorPredecessorCursor

namespace Recaman

noncomputable section

/-! # Restart cursor for a stationary blocker crossing

Moving the ordinary history coordinate ahead of the one-way cycle phase does
not work: it would validate a stationary reset, but a real downcross can move
history forward when entering discharge.  Instead we add a distinct restart
cursor.  It is held fixed during one crossing/backtrack/discharge pass and is
decreased only when a stationary crossing is restarted from a blocker's
first-occurrence predecessor.

The resulting six-coordinate rank preserves the existing crossing-time and
phase behavior.  The strict seen-below drop from `firstTime` to
`firstTime - 1` now dominates the otherwise upward discharge-to-crossing phase
reset.  Thus the eligible predecessor kernel has only strict anchor growth
left as a non-progress outcome.
-/

/-- Cycle node with a dedicated history cursor consumed only by a stationary
restart. -/
structure TailRestartCycleSearchNode where
  anchor : Nat
  crossingTime : Nat
  restartTime : Nat
  phase : TailCyclePhase
  historyTime : Nat
  minimumValue : Nat
deriving Repr, DecidableEq

def tailRestartCycleRank (target : Nat)
    (node : TailRestartCycleSearchNode) :
    Nat × (Nat × (Nat × (Nat × (Nat × Nat)))) :=
  (node.anchor,
    (node.crossingTime,
      (seenBelowCount target node.restartTime,
        (node.phase.rank,
          (seenBelowCount target node.historyTime, node.minimumValue)))))

def TailRestartCycleProgress (target : Nat)
    (child parent : TailRestartCycleSearchNode) : Prop :=
  Prod.Lex Nat.lt
      (Prod.Lex Nat.lt
        (Prod.Lex Nat.lt
          (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))))
    (tailRestartCycleRank target child)
    (tailRestartCycleRank target parent)

/-- Six right-nested natural coordinates carry a well-founded lexicographic
order. -/
theorem natSextLex_wellFounded :
    WellFounded
      (Prod.Lex Nat.lt
        (Prod.Lex Nat.lt
          (Prod.Lex Nat.lt
            (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))))) := by
  apply WellFounded.intro
  intro tuple
  exact Prod.lexAccessible
    (Nat.lt_wfRel.wf.apply tuple.1)
    (fun quintuple => natQuintLex_wellFounded.apply quintuple)
    tuple.2

/-- Pullback of the six-coordinate order along the restart-cycle rank. -/
theorem tailRestartCycleProgress_wellFounded (target : Nat) :
    WellFounded (TailRestartCycleProgress target) := by
  apply WellFounded.intro
  intro node
  generalize hrank : tailRestartCycleRank target node = rank
  have hacc := natSextLex_wellFounded.apply rank
  induction hacc generalizing node with
  | intro rank _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrelation :
          Prod.Lex Nat.lt
              (Prod.Lex Nat.lt
                (Prod.Lex Nat.lt
                  (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))))
            (tailRestartCycleRank target child) rank := by
        simpa [TailRestartCycleProgress, hrank] using hchild
      exact ih (tailRestartCycleRank target child) hrelation child rfl

/-- Any strict crossing cursor decrease remains an exit in the restart rank,
independently of the two restart/history coordinates. -/
theorem tailRestartCycle_exit_of_cursorProgress
    {target childAnchor childCrossingTime childRestartTime childHistoryTime
      childMinimum parentAnchor parentCrossingTime parentRestartTime
      parentHistoryTime parentMinimum : Nat}
    (hcursor : TailCrossingCursorProgress
      ⟨childAnchor, childCrossingTime⟩
      ⟨parentAnchor, parentCrossingTime⟩) :
    TailRestartCycleProgress target
      ⟨childAnchor, childCrossingTime, childRestartTime, .crossing,
        childHistoryTime, childMinimum⟩
      ⟨parentAnchor, parentCrossingTime, parentRestartTime, .discharge,
        parentHistoryTime, parentMinimum⟩ := by
  rw [tailCrossingCursorProgress_iff] at hcursor
  rcases hcursor with hanchor | ⟨hanchor, htime⟩
  · exact Prod.Lex.left _ _ hanchor
  · rw [hanchor]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ htime)

/-- A strict restart seen-budget drop hides the upward phase reset even when
the crossing anchor and crossing time are both stationary. -/
theorem tailRestartCycle_exit_of_restartSeenDrop
    {target anchor crossingTime childRestartTime childHistoryTime childMinimum
      parentRestartTime parentHistoryTime parentMinimum : Nat}
    (hseen : seenBelowCount target childRestartTime <
      seenBelowCount target parentRestartTime) :
    TailRestartCycleProgress target
      ⟨anchor, crossingTime, childRestartTime, .crossing,
        childHistoryTime, childMinimum⟩
      ⟨anchor, crossingTime, parentRestartTime, .discharge,
        parentHistoryTime, parentMinimum⟩ := by
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.left _ _ hseen))

/-- Final eligible outcome after adding the stationary restart cursor. -/
inductive TerminalBelowPredecessorRestartRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) : Prop
  | phase_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      TerminalBelowPredecessorRestartRankOutcome below
  | restart_cycle_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : TailRestartCycleProgress target
        ⟨a crossingTime, crossingTime, firstTime - 1, .crossing,
          firstTime - 1, 0⟩
        ⟨parent.anchorParent, source.oldCrossingTime, firstTime, .discharge,
          firstTime, 0⟩) :
      TerminalBelowPredecessorRestartRankOutcome below
  | anchor_growth
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (growth : parent.anchorParent < a crossingTime) :
      TerminalBelowPredecessorRestartRankOutcome below

/-- Under old-crossing eligibility, both equal-anchor earlier-time and literal
stationary returns strictly descend; only strict anchor growth remains. -/
theorem BelowTargetHistoricalPredecessorCertificate.restartRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical)
    (holdEligible : source.downTime + 1 ≤ source.oldCrossingTime) :
    TerminalBelowPredecessorRestartRankOutcome h := by
  cases h.eligibleRankOutcome holdEligible with
  | phase_progress crossingTime quotient remainder certificate progress =>
      exact .phase_progress crossingTime quotient remainder certificate
        progress
  | cursor_progress crossingTime quotient remainder certificate progress =>
      have hrestart : TailRestartCycleProgress target
          ⟨a crossingTime, crossingTime, firstTime - 1, .crossing,
            firstTime - 1, 0⟩
          ⟨parent.anchorParent, source.oldCrossingTime, firstTime, .discharge,
            firstTime, 0⟩ :=
        tailRestartCycle_exit_of_cursorProgress progress
      exact .restart_cycle_progress crossingTime quotient remainder
        certificate hrestart
  | anchor_growth crossingTime quotient remainder certificate growth =>
      exact .anchor_growth crossingTime quotient remainder certificate growth
  | stationary crossingTime quotient remainder certificate same_anchor
      same_time =>
      have hseen := certificate.backtrack.seen_gain
      have hrestart : TailRestartCycleProgress target
          ⟨a crossingTime, crossingTime, firstTime - 1, .crossing,
            firstTime - 1, 0⟩
          ⟨parent.anchorParent, source.oldCrossingTime, firstTime, .discharge,
            firstTime, 0⟩ := by
        rw [← same_anchor, ← same_time]
        exact tailRestartCycle_exit_of_restartSeenDrop hseen
      exact .restart_cycle_progress crossingTime quotient remainder
        certificate hrestart

end

end Recaman
