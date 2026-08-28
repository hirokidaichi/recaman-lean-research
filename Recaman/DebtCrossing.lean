import Recaman.DebtInvariant
import Recaman.PrestateCoverage

namespace Recaman

/-- A forced addition crosses `target` strictly when the old value is below
the target and the newly first-occurring value is above it. -/
def DebtCrossing (target value n : Nat) : Prop :=
  a n < target ∧ target < value ∧ value = a n + (n + 1)

/-- A strict crossing cannot itself be a target equation based at the
post-addition state.  One planned subtraction removes `n+2`, already more
than the entire gap back to the pre-state; zero removes nothing. -/
theorem debtCrossing_not_targetEquation
    {target value n k : Nat}
    (hcross : DebtCrossing target value n) :
    ¬ TargetEquation (n + 1) value target k := by
  intro hequation
  rcases hcross with ⟨hpre, hpost, hvalue⟩
  cases k with
  | zero =>
      simp [TargetEquation, descentDrop, upperTri] at hequation
      omega
  | succ k =>
      have hdrop := descentDrop_mono (n + 1)
        (show 1 ≤ k + 1 by omega)
      have hone : descentDrop (n + 1) 1 = n + 2 := by
        simp [descentDrop, upperTri]
      unfold TargetEquation at hequation
      rw [hone] at hdrop
      omega

/-- Consequently no quotient/remainder presentation of the post-state can
place a strict crossing on the target surface `G=target`. -/
theorem debtCrossing_not_targetSurface
    {target value n q r : Nat}
    (hcross : DebtCrossing target value n)
    (hqr : QuotRem (n + 1) value q r) :
    potential q r ≠ Int.ofNat target := by
  intro hpotential
  exact debtCrossing_not_targetEquation hcross
    (targetEquation_of_quotRem_potential hqr hpotential)

/-- The exact two-step gate is also arithmetically impossible at the
post-addition endpoint of a strict crossing. -/
theorem debtCrossing_not_exactGate_post
    {target value n : Nat}
    (hcross : DebtCrossing target value n) :
    value ≠ 2 * (n + 1) + target + 3 := by
  intro hgate
  rcases hcross with ⟨hpre, _, hvalue⟩
  omega

/-- Nor can the below-target pre-state itself have the exact-gate value. -/
theorem debtCrossing_not_exactGate_pre
    {target value n : Nat}
    (hcross : DebtCrossing target value n) :
    a n ≠ 2 * n + target + 3 := by
  intro hgate
  exact (Nat.not_lt_of_ge (by omega : target ≤ a n)) hcross.1

/-- Adding a value at least `target` does not fill any missing slot strictly
below `target`; the history-budget component is therefore unchanged. -/
theorem missingBelowCount_succ_of_new_ge
    {target n : Nat} (hge : target ≤ a (n + 1)) :
    missingBelowCount target (n + 1) = missingBelowCount target n := by
  induction target with
  | zero => simp
  | succ target ih =>
      have hne : target ≠ a (n + 1) := by omega
      have hmem :
          target ∈ valuesThrough (n + 1) ↔
            target ∈ valuesThrough n := by
        rw [valuesThrough_succ]
        simp [hne]
      simp only [missingBelowCount_succ]
      simp only [hmem]
      rw [ih (by omega)]

/-- Thus a strict crossing cannot make progress through the history-budget
coordinate. -/
theorem debtCrossing_budget_unchanged
    {target value n : Nat}
    (hcross : DebtCrossing target value n)
    (hfirst : FirstAt a value (n + 1)) :
    missingBelowCount target (n + 1) = missingBelowCount target n := by
  apply missingBelowCount_succ_of_new_ge
  rw [hfirst.1]
  exact Nat.le_of_lt hcross.2.1

/-- A valid debt crossing still gives a formal `PhaseSearchProgress`: forced
addition makes the pre-state value smaller than the fixed anchor.  This is a
rank fact only; because the pre-state is below `target`, it does not preserve
the usual normal-search lower-bound invariant. -/
theorem debtCrossing_phaseProgress
    {target horizon anchor value n : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (_hbelow : a n < target) :
    PhaseSearchProgress target
      ⟨horizon, a n, .normal, a n⟩
      ⟨horizon, anchor, .debt, n + 1⟩ := by
  have hstep := a_succ_of_not_canSubtract hnot
  have hvalue : value = a n + (n + 1) :=
    hinv.first.1.symm.trans hstep
  have hanchor : a n < anchor := by
    exact Nat.lt_trans (by omega : a n < value) hinv.value_lt_anchor
  exact phaseSearch_exitDebt_of_anchorDrop hanchor

/-- Complete outcome for a forced addition that weakly crosses the target.
If the new endpoint equals the target, its stored first occurrence witnesses
success.  If the target lies strictly inside the jump, only the formal
anchor-decreasing phase progress is unconditional. -/
theorem debt_forcedAddition_crossing_outcome
    {target horizon anchor value n : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hpre : a n < target) :
    (∃ t, a t = target) ∨
      PhaseSearchProgress target
        ⟨horizon, a n, .normal, a n⟩
        ⟨horizon, anchor, .debt, n + 1⟩ := by
  rcases Nat.eq_or_lt_of_le hinv.target_le with heq | hstrict
  · left
    refine ⟨n + 1, ?_⟩
    rw [hinv.first.1, heq]
  · right
    exact debtCrossing_phaseProgress hinv hnot hpre

/-- The strongest unconditional local conclusion currently available in the
strict-crossing branch: either the target was already seen, or one can take
the formal anchor-decreasing rank step. -/
theorem debtCrossing_occursBefore_or_phaseProgress
    {target horizon anchor value n : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbelow : a n < target) :
    (∃ t, t ≤ n ∧ a t = target) ∨
      PhaseSearchProgress target
        ⟨horizon, a n, .normal, a n⟩
        ⟨horizon, anchor, .debt, n + 1⟩ := by
  by_cases hseen : target ∈ valuesThrough n
  · left
    exact mem_valuesThrough_iff.mp hseen
  · right
    exact debtCrossing_phaseProgress hinv hnot hbelow

/-- Concrete local counterexample to the stronger claim that crossing itself
forces the target to have occurred: step 3 jumps from 3 to 6 across 4, while
4 is absent from the complete history through that step. -/
theorem debtCrossing_four_local_counterexample :
    DebtInvariant 4 ⟨4, 7, .debt, 3⟩ 6 3 ∧
      ¬ CanSubtract 3 (stateAt 2) ∧
      DebtCrossing 4 6 2 ∧
      4 ∉ valuesThrough 3 := by
  refine ⟨?_, by decide, ?_, by decide⟩
  refine {
    phase_eq := rfl
    local_eq := rfl
    target_le := by omega
    first := ?_
    firstTime_lt_horizon := by decide
    value_lt_anchor := by decide
  }
  constructor
  · decide
  · intro u hu
    have hcases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hcases with h | h | h <;> subst u <;> decide
  unfold DebtCrossing
  exact ⟨by decide, by decide, by decide⟩

end Recaman
