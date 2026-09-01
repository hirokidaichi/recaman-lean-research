import Recaman.History
import Recaman.ActualDescent
import Recaman.CoordinateDynamics

namespace Recaman

/-! # Forced-addition runs of length exactly two are impossible

After a legal subtraction, one forced addition followed by a legal
subtraction lands exactly one below the pre-run value: this is the known
immediate-repayment identity.  This module records the next case: after a
legal subtraction, two consecutive forced additions expose, as the next
subtraction candidate, exactly the value the original subtraction departed
from.  That value is already in the history, so a third addition is forced.

Consequently every maximal forced-addition run which begins right after a
legal subtraction has length one or at least three.  A one-billion-step
exact probe (`experiments/corridor_structure_probe.cpp`) observed maximal
run lengths `1, 3, 4, 5, 6` with length two occurring exactly zero times;
this theorem explains that gap unconditionally.
-/

/-- After a legal subtraction and two forced additions, the next
subtraction candidate has returned to the pre-subtraction value. -/
theorem double_forcedAddition_candidate_returns
    {n : Nat}
    (hsub : CanSubtract (n + 1) (stateAt n))
    (hadd₁ : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hadd₂ : ¬ CanSubtract (n + 3) (stateAt (n + 2))) :
    a (n + 3) - (n + 4) = a n := by
  have hclock : n + 1 < a n := hsub.1
  have hv₁ : a (n + 1) = a n - (n + 1) := a_succ_of_canSubtract hsub
  have hv₂ : a (n + 2) = a (n + 1) + (n + 2) :=
    a_succ_of_not_canSubtract hadd₁
  have hv₃ : a (n + 3) = a (n + 2) + (n + 3) :=
    a_succ_of_not_canSubtract hadd₂
  omega

/-- **No forced-addition run of length exactly two.**  A legal subtraction
followed by two forced additions forces a third addition: the exposed
candidate is the pre-subtraction value, which is already historical. -/
theorem double_forcedAddition_extends
    {n : Nat}
    (hsub : CanSubtract (n + 1) (stateAt n))
    (hadd₁ : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hadd₂ : ¬ CanSubtract (n + 3) (stateAt (n + 2))) :
    ¬ CanSubtract (n + 4) (stateAt (n + 3)) := by
  intro hcan
  have hfresh : a (n + 3) - (n + 4) ∉ valuesThrough (n + 3) := hcan.2
  have hvalue := double_forcedAddition_candidate_returns hsub hadd₁ hadd₂
  rw [hvalue] at hfresh
  exact hfresh (mem_valuesThrough_iff.mpr ⟨n, by omega, rfl⟩)

end Recaman
