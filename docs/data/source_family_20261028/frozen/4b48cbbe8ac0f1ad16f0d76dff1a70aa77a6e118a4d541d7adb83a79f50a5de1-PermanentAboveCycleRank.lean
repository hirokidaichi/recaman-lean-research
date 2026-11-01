import Recaman.PermanentAboveCanonical

namespace Recaman

/-! # A one-way rank for permanent-tail historical cycles

Within a zero-budget permanent-tail obstruction, the old outer history rank
is saturated.  We instead keep the crossing anchor outermost and place a
one-way `crossing → backtrack → discharge` phase beneath it.  Backtracking
uses the dual seen-below budget and tail-minimum value.  Returning from
discharge to crossing is rank-valid exactly when the crossing anchor drops.
-/

inductive TailCyclePhase where
  | discharge
  | backtrack
  | crossing
deriving Repr, DecidableEq

def TailCyclePhase.rank : TailCyclePhase → Nat
  | .discharge => 0
  | .backtrack => 1
  | .crossing => 2

structure TailCycleSearchNode where
  anchor : Nat
  phase : TailCyclePhase
  historyTime : Nat
  minimumValue : Nat
deriving Repr, DecidableEq

def tailCycleRank (target : Nat) (node : TailCycleSearchNode) :
    Nat × (Nat × (Nat × Nat)) :=
  (node.anchor,
    (node.phase.rank,
      (seenBelowCount target node.historyTime, node.minimumValue)))

def TailCycleProgress (target : Nat)
    (child parent : TailCycleSearchNode) : Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (tailCycleRank target child) (tailCycleRank target parent)

/-- The permanent-tail cycle rank is well founded. -/
theorem tailCycleProgress_wellFounded (target : Nat) :
    WellFounded (TailCycleProgress target) := by
  apply WellFounded.intro
  intro node
  generalize hrank : tailCycleRank target node = rank
  have hacc := natQuadLex_wellFounded.apply rank
  induction hacc generalizing node with
  | intro rank _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrelation :
          Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
            (tailCycleRank target child) rank := by
        simpa [TailCycleProgress, hrank] using hchild
      exact ih (tailCycleRank target child) hrelation child rfl

/-- Enter historical backtracking without changing the crossing anchor. -/
theorem tailCycleProgress_enterBacktrack
    {target anchor childTime parentTime childMinimum parentMinimum : Nat} :
    TailCycleProgress target
      ⟨anchor, .backtrack, childTime, childMinimum⟩
      ⟨anchor, .crossing, parentTime, parentMinimum⟩ := by
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (anchor, (1, (seenBelowCount target childTime, childMinimum)))
    (anchor, (2, (seenBelowCount target parentTime, parentMinimum)))
  exact Prod.Lex.right _
    (Prod.Lex.left _ _ (Nat.lt_succ_self 1))

/-- A strict dual seen-budget drop progresses within backtracking. -/
theorem tailCycleProgress_backtrack_of_seenDrop
    {target anchor childTime parentTime childMinimum parentMinimum : Nat}
    (hseen : seenBelowCount target childTime <
      seenBelowCount target parentTime) :
    TailCycleProgress target
      ⟨anchor, .backtrack, childTime, childMinimum⟩
      ⟨anchor, .backtrack, parentTime, parentMinimum⟩ := by
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.left _ _ hseen))

/-- If seen history is unchanged, a strict tail-minimum drop progresses. -/
theorem tailCycleProgress_backtrack_of_seenLe_minimumDrop
    {target anchor childTime parentTime childMinimum parentMinimum : Nat}
    (hseen : seenBelowCount target childTime ≤
      seenBelowCount target parentTime)
    (hminimum : childMinimum < parentMinimum) :
    TailCycleProgress target
      ⟨anchor, .backtrack, childTime, childMinimum⟩
      ⟨anchor, .backtrack, parentTime, parentMinimum⟩ := by
  rcases Nat.eq_or_lt_of_le hseen with hequal | hstrict
  · change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (anchor, (1, (seenBelowCount target childTime, childMinimum)))
      (anchor, (1, (seenBelowCount target parentTime, parentMinimum)))
    rw [hequal]
    exact Prod.Lex.right _
      (Prod.Lex.right _ (Prod.Lex.right _ hminimum))
  · exact tailCycleProgress_backtrack_of_seenDrop hstrict

/-- A real historical downcross enters the terminal discharge phase. -/
theorem tailCycleProgress_enterDischarge
    {target anchor childTime parentTime childMinimum parentMinimum : Nat} :
    TailCycleProgress target
      ⟨anchor, .discharge, childTime, childMinimum⟩
      ⟨anchor, .backtrack, parentTime, parentMinimum⟩ := by
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (anchor, (0, (seenBelowCount target childTime, childMinimum)))
    (anchor, (1, (seenBelowCount target parentTime, parentMinimum)))
  exact Prod.Lex.right _
    (Prod.Lex.left _ _ (Nat.zero_lt_succ 0))

/-- Returning from discharge to crossing is valid in this rank if and only
if the crossing anchor strictly drops.  Neither time nor either history
coordinate can hide a stationary anchor. -/
theorem tailCycle_exitCrossing_iff_anchorDrop
    {target childAnchor parentAnchor childTime parentTime
      childMinimum parentMinimum : Nat} :
    TailCycleProgress target
        ⟨childAnchor, .crossing, childTime, childMinimum⟩
        ⟨parentAnchor, .discharge, parentTime, parentMinimum⟩ ↔
      childAnchor < parentAnchor := by
  constructor
  · intro hprogress
    unfold TailCycleProgress tailCycleRank at hprogress
    rcases Prod.lex_def.mp hprogress with hanchor | ⟨hanchorEq, hrest⟩
    · exact hanchor
    · rcases Prod.lex_def.mp hrest with hphase | ⟨hphaseEq, _⟩
      · simp [TailCyclePhase.rank] at hphase
      · simp [TailCyclePhase.rank] at hphaseEq
  · intro hanchor
    exact Prod.Lex.left _ _ hanchor

/-- The historical predecessor outcome is total and strictly descending in
the cycle rank while the crossing anchor is held fixed. -/
theorem HistoricalPredecessorOutcome.tailCycleProgress
    {target start minimumTime predecessorFirstTime anchor : Nat}
    (h : HistoricalPredecessorOutcome target start minimumTime
      predecessorFirstTime) :
    ∃ child,
      TailCycleProgress target child
        ⟨anchor, .backtrack, predecessorFirstTime, a minimumTime⟩ := by
  cases h with
  | downcross downTime hstep hfirst hbefore hbudget =>
      exact ⟨⟨anchor, .discharge, downTime + 1, a minimumTime⟩,
        tailCycleProgress_enterDischarge⟩
  | renewed_tail newMinimumTime newFirstTime htail hminimum hvalueDrop =>
      have htime : newFirstTime ≤ predecessorFirstTime :=
        Nat.le_of_lt hminimum.firstTime_before_tail
      have hseen := seenBelowCount_monotone (target := target) htime
      exact ⟨⟨anchor, .backtrack, newFirstTime, a newMinimumTime⟩,
        tailCycleProgress_backtrack_of_seenLe_minimumDrop
          hseen hvalueDrop⟩

/-- Every combined permanent-tail obstruction strictly enters the cycle rank
at fixed anchor.  The historical certificate is retained so its local
outcome can take the next strict step. -/
theorem PermanentTailCombinedCertificate.entersTailCycle
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    ∃ tailStart historicalMinimumTime historicalFirstTime downTime,
      MissingStrictAboveTail target tailStart ∧
      PermanentTailMinimumCertificate target tailStart
        historicalMinimumTime historicalFirstTime ∧
      FutureDowncrossStep target historicalFirstTime downTime ∧
      TailCycleProgress target
        ⟨parent.anchorParent, .backtrack, historicalFirstTime,
          a historicalMinimumTime⟩
        ⟨parent.anchorParent, .crossing, parent.horizon,
          a historicalMinimumTime⟩ := by
  rcases h.tail.exists_historicalDowncrossCertificate with
    ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
      htailStart, htail, hminimum, hdown, hfirst, hbefore, hbudget⟩
  exact ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
    htail, hminimum, hdown, tailCycleProgress_enterBacktrack⟩

/-- In particular, the stationary historical cycle cannot exit discharge
back to the same crossing anchor in the new rank. -/
theorem tailCycle_no_stationary_crossingExit
    {target anchor childTime parentTime childMinimum parentMinimum : Nat} :
    ¬ TailCycleProgress target
      ⟨anchor, .crossing, childTime, childMinimum⟩
      ⟨anchor, .discharge, parentTime, parentMinimum⟩ := by
  rw [tailCycle_exitCrossing_iff_anchorDrop]
  exact Nat.lt_irrefl _

/-- The old historical growth residual is exactly an exit obstruction for
the new one-way rank as well: its reconstructed ready crossing has a
nondecreasing anchor, so discharge cannot return to crossing. -/
theorem HistoricalCycleGrowthResidual.tailCycleExitObstruction
    {target : Nat} {parent : PhaseSearchNode}
    (h : HistoricalCycleGrowthResidual target parent) :
    ∃ child,
      ReadyCrossingSearchInvariant target child ∧
      parent.anchorParent ≤ child.anchorParent ∧
      ¬ TailCycleProgress target
        ⟨child.anchorParent, .crossing, child.horizon, 0⟩
        ⟨parent.anchorParent, .discharge, parent.horizon, 0⟩ := by
  cases h with
  | intro predecessorFirstTime downTime crossingTime child hdown hupcross
      hready hhorizon hanchor hnoProgress =>
      refine ⟨child, hready, hanchor, ?_⟩
      rw [tailCycle_exitCrossing_iff_anchorDrop]
      omega

end Recaman
