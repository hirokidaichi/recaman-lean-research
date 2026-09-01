import Recaman.EventualHighCorridorStructure

namespace Recaman

/-! # Both step types recur unconditionally

The adversarial audit of the 2026-09-01 sprint found that two corridor
conclusions are free: they hold for the canonical orbit with no corridor
hypothesis at all.  This module records the free facts under honest names
and restates the corridor blocking law with its genuinely corridor-bound
half, the clock condition.

First, any forced addition exposes a historical candidate: if the clock
half of `CanSubtract` fails, the truncated candidate is `0 = a 0`, which
is always in the history.  Second, forced additions recur beyond every
bound: a perpetual subtraction ray is impossible because the clock half
keeps values positive while every subtraction drops the value.  Together
with `exists_canSubtract_of_ray`, both step types of the canonical orbit
are unconditionally recurrent.

What the corridor genuinely adds to a forced addition is the clock half
itself: strictly inside the corridor the clock condition always holds, so
the block is purely historical and the candidate is positive.
-/

/-- **Free fact.**  Any forced addition exposes a historical candidate:
when the clock half fails, the truncated candidate is `0 = a 0`. -/
theorem forcedAddition_candidate_historical
    {n : Nat}
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    nextSubtractionCandidate n ∈ valuesThrough n := by
  rcases not_canSubtract_cases hnot with hsmall | hseen
  · have hzero : nextSubtractionCandidate n = 0 := by
      simp only [nextSubtractionCandidate]
      omega
    rw [hzero]
    exact mem_valuesThrough_iff.mpr ⟨0, Nat.zero_le n, rfl⟩
  · exact hseen

/-- **Free fact.**  Forced additions recur beyond every bound: a perpetual
subtraction ray would drop the value by at least one per step while the
clock half keeps it positive. -/
theorem exists_forcedAddition_of_ray :
    ∀ M, ∃ n, M ≤ n ∧ ¬ CanSubtract (n + 1) (stateAt n) := by
  classical
  intro M
  by_cases hresult : ∃ n, M ≤ n ∧ ¬ CanSubtract (n + 1) (stateAt n)
  · exact hresult
  · exfalso
    have hall : ∀ n, M ≤ n → CanSubtract (n + 1) (stateAt n) := by
      intro n hn
      by_cases hcan : CanSubtract (n + 1) (stateAt n)
      · exact hcan
      · exact False.elim (hresult ⟨n, hn, hcan⟩)
    have hdrop : ∀ k, a (M + k) + k ≤ a M := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have hcan := hall (M + k) (by omega)
          have hclock : M + k + 1 < a (M + k) := hcan.1
          have hstep := a_succ_of_canSubtract hcan
          have hidx : M + k + 1 = M + (k + 1) := by omega
          rw [hidx] at hstep hclock
          omega
    have hfinal := hdrop (a M + 1)
    omega

/-- **Honest corridor blocking law.**  Strictly inside the corridor the
clock half of `CanSubtract` always holds and the candidate is positive, so
a forced addition is blocked purely by history.  The clock conjunct is the
corridor-bound content; the membership conjunct alone is free. -/
theorem corridor_forcedAddition_clock_and_seen
    {target cutoff n : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff + 1 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    n + 1 < a n ∧
      0 < nextSubtractionCandidate n ∧
      nextSubtractionCandidate n ∈ valuesThrough n := by
  have hhighPrev := hhigh (n - 1) (by omega)
  have hclockIdx : n - 1 + 1 = n := by omega
  rw [hclockIdx] at hhighPrev
  have hseen := forcedAddition_candidate_historical hnot
  simp only [nextSubtractionCandidate] at hhighPrev ⊢
  exact ⟨by omega, by omega, hseen⟩

end Recaman
