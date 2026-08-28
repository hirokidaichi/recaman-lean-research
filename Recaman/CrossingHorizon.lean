import Recaman.BoundaryAudit

namespace Recaman

/-! # Crossing horizon updates

This module isolates the exact rank boundary for moving from a debt node to
a normal node while advancing the stored history horizon.  Advancing the
horizon is semantically legitimate only through the actual orbit history; it
helps the phase rank precisely when that extra history consumes a missing
value below the target.
-/

/-- Exact rank boundary for an advancing-horizon debt-to-normal transition.

The phase component points in the wrong direction (`normal.rank = 1` while
`debt.rank = 0`), so after equal budgets only a strict anchor drop can make
progress.  The horizon-order assumption turns budget comparison into the
exhaustive strict-drop/equality dichotomy. -/
theorem exitDebt_advancingHorizon_iff_budgetDrop_or_anchorDrop
    {target parentHorizon childHorizon parentAnchor childAnchor
      parentTime childLocal : Nat}
    (htime : parentHorizon ≤ childHorizon) :
    PhaseSearchProgress target
        ⟨childHorizon, childAnchor, .normal, childLocal⟩
        ⟨parentHorizon, parentAnchor, .debt, parentTime⟩ ↔
      missingBelowCount target childHorizon <
          missingBelowCount target parentHorizon ∨
        (missingBelowCount target childHorizon =
            missingBelowCount target parentHorizon ∧
          childAnchor < parentAnchor) := by
  have hbudget := missingBelowCount_antitone (m := target) htime
  constructor
  · intro hprogress
    rcases Nat.eq_or_lt_of_le hbudget with heq | hdrop
    · right
      refine ⟨heq, ?_⟩
      change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
        (missingBelowCount target childHorizon,
          (childAnchor, (SearchPhase.normal.rank, childLocal)))
        (missingBelowCount target parentHorizon,
          (parentAnchor, (SearchPhase.debt.rank, parentTime))) at hprogress
      rw [heq] at hprogress
      cases hprogress with
      | left _ _ hfalse => exact False.elim (Nat.lt_irrefl _ hfalse)
      | right _ htail =>
          cases htail with
          | left _ _ hanchor => exact hanchor
          | right _ hphaseLocal =>
              cases hphaseLocal with
              | left _ _ hphase =>
                  change 1 < 0 at hphase
                  omega
    · exact Or.inl hdrop
  · rintro (hdrop | ⟨heq, hanchor⟩)
    · exact Prod.Lex.left _ _ hdrop
    · change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
        (missingBelowCount target childHorizon,
          (childAnchor, (SearchPhase.normal.rank, childLocal)))
        (missingBelowCount target parentHorizon,
          (parentAnchor, (SearchPhase.debt.rank, parentTime)))
      rw [heq]
      exact Prod.Lex.right _ (Prod.Lex.left _ _ hanchor)

/-- A strict history-budget drop is by itself sufficient for a phase step;
the new normal anchor and local coordinate are unrestricted. -/
theorem exitDebt_advancingHorizon_of_budgetDrop
    {target parentHorizon childHorizon parentAnchor childAnchor
      parentTime childLocal : Nat}
    (hdrop : missingBelowCount target childHorizon <
      missingBelowCount target parentHorizon) :
    PhaseSearchProgress target
      ⟨childHorizon, childAnchor, .normal, childLocal⟩
      ⟨parentHorizon, parentAnchor, .debt, parentTime⟩ := by
  exact Prod.Lex.left _ _ hdrop

/-- If the normal anchor does not drop, budget consumption is not merely
sufficient but necessary for an advancing-horizon phase step. -/
theorem exitDebt_anchorGrowth_iff_budgetDrop
    {target parentHorizon childHorizon parentAnchor childAnchor
      parentTime childLocal : Nat}
    (htime : parentHorizon ≤ childHorizon)
    (hanchor : parentAnchor ≤ childAnchor) :
    PhaseSearchProgress target
        ⟨childHorizon, childAnchor, .normal, childLocal⟩
        ⟨parentHorizon, parentAnchor, .debt, parentTime⟩ ↔
      missingBelowCount target childHorizon <
        missingBelowCount target parentHorizon := by
  rw [exitDebt_advancingHorizon_iff_budgetDrop_or_anchorDrop htime]
  constructor
  · rintro (hdrop | ⟨_, hanchorDrop⟩)
    · exact hdrop
    · omega
  · exact Or.inl

/-- Updating the diagonal crossing node's horizon to the finite catch-up time
does not unlock the budget branch.  Its phase progress boundary is still
exactly strict anchor decrease. -/
theorem diagonalCrossingCatchup_exitDebt_iff_anchorDrop
    {horizon parentAnchor childAnchor parentTime childLocal catchTime
      quotient remainder firstTime : Nat}
    (hcatch : CrossingCatchup (horizon + 1) horizon parentAnchor catchTime
      quotient remainder firstTime) :
    PhaseSearchProgress (horizon + 1)
        ⟨catchTime, childAnchor, .normal, childLocal⟩
        ⟨horizon, parentAnchor, .debt, parentTime⟩ ↔
      childAnchor < parentAnchor := by
  have htime : horizon ≤ catchTime := by
    rcases hcatch.time_eq with h | h <;> omega
  rw [exitDebt_advancingHorizon_iff_budgetDrop_or_anchorDrop htime]
  have heq := diagonalCrossingCatchup_budget_eq_horizon hcatch
  rw [heq]
  simp

/-- Consequently, the actual catch-up horizon cannot close the joint
value/anchor-growth obstruction. -/
theorem diagonalCrossingCatchup_anchorGrowth_no_progress
    {horizon parentAnchor childAnchor parentTime childLocal catchTime
      quotient remainder firstTime : Nat}
    (hcatch : CrossingCatchup (horizon + 1) horizon parentAnchor catchTime
      quotient remainder firstTime)
    (hanchor : parentAnchor ≤ childAnchor) :
    ¬ PhaseSearchProgress (horizon + 1)
      ⟨catchTime, childAnchor, .normal, childLocal⟩
      ⟨horizon, parentAnchor, .debt, parentTime⟩ := by
  rw [diagonalCrossingCatchup_exitDebt_iff_anchorDrop hcatch]
  omega

/-- A later epoch time does close the growth branch as soon as its newly
available history contains a first occurrence below the target that was not
available at the old horizon.  This is the canonical sufficient condition
for using budget as the first rank component. -/
theorem exitDebt_at_laterEpoch_of_newFirstBelowTarget
    {target parentHorizon epochTime parentAnchor childAnchor parentTime
      childLocal g firstTime : Nat}
    (hg : g < target)
    (hnew : parentHorizon < firstTime)
    (hseen : firstTime ≤ epochTime)
    (hfirst : FirstAt a g firstTime) :
    PhaseSearchProgress target
      ⟨epochTime, childAnchor, .normal, childLocal⟩
      ⟨parentHorizon, parentAnchor, .debt, parentTime⟩ := by
  have hdropAtFirst := missingBelowCount_strict_of_firstAt hg hnew hfirst
  have hmono := missingBelowCount_antitone
    (m := target) hseen
  apply exitDebt_advancingHorizon_of_budgetDrop
  exact Nat.lt_of_le_of_lt hmono hdropAtFirst

/-- Exact residual obligation at a later epoch in the anchor-growth branch:
the transition succeeds iff the extended real history strictly lowers the
missing-below-target budget. -/
theorem exitDebt_at_laterEpoch_anchorGrowth_iff
    {target parentHorizon epochTime parentAnchor childAnchor parentTime
      childLocal : Nat}
    (htime : parentHorizon ≤ epochTime)
    (hanchor : parentAnchor ≤ childAnchor) :
    PhaseSearchProgress target
        ⟨epochTime, childAnchor, .normal, childLocal⟩
        ⟨parentHorizon, parentAnchor, .debt, parentTime⟩ ↔
      missingBelowCount target epochTime <
        missingBelowCount target parentHorizon :=
  exitDebt_anchorGrowth_iff_budgetDrop htime hanchor

end Recaman
