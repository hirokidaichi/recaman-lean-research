import Recaman.History
import Recaman.ActualDescent
import Recaman.CoordinateDynamics

namespace Recaman

/-! # The loop-closing subtraction family

A step word whose signed clock weights cancel exposes, as its next
subtraction candidate, exactly the value the window departed from — a
historical value, so the closing subtraction is impossible.  For a sign
prefix `ε₁ … ε_{L-1}` the closing candidate equals the pre-window value
precisely when `Σ εᵢ = 1` and `Σ εᵢ·i = L`, which forces `L ≡ 0 (mod 4)`.
At `L = 4` the unique minimal instance is the proven `S A A + S`
prohibition; at `L = 8` the unique minimal instance not containing the
`L = 4` one is `S S A A A A S + S`, and a one-billion-step census indeed
lists it among the minimal absent factors.  This module records the
`L = 8` instance concretely: after two legal subtractions and four forced
additions, a legal subtraction exposes the pre-window value, so an eighth
step subtraction is impossible.

A seeded search confirms this law is local: every other forced-S census
candidate at length at most eight has an exact seeded realization, while
this pattern and the length-four one have none.
-/

/-- After two legal subtractions, four forced additions, and one more
legal subtraction, the next subtraction candidate has returned to the
pre-window value. -/
theorem double_descent_loop_candidate_returns
    {n : Nat}
    (hsub₁ : CanSubtract (n + 1) (stateAt n))
    (hsub₂ : CanSubtract (n + 2) (stateAt (n + 1)))
    (hadd₃ : ¬ CanSubtract (n + 3) (stateAt (n + 2)))
    (hadd₄ : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hadd₅ : ¬ CanSubtract (n + 5) (stateAt (n + 4)))
    (hadd₆ : ¬ CanSubtract (n + 6) (stateAt (n + 5)))
    (hsub₇ : CanSubtract (n + 7) (stateAt (n + 6))) :
    a (n + 7) - (n + 8) = a n := by
  have hclock₁ : n + 1 < a n := hsub₁.1
  have hclock₂ : n + 2 < a (n + 1) := hsub₂.1
  have hclock₇ : n + 7 < a (n + 6) := hsub₇.1
  have hv₁ : a (n + 1) = a n - (n + 1) := a_succ_of_canSubtract hsub₁
  have hv₂ : a (n + 2) = a (n + 1) - (n + 2) := a_succ_of_canSubtract hsub₂
  have hv₃ : a (n + 3) = a (n + 2) + (n + 3) := a_succ_of_not_canSubtract hadd₃
  have hv₄ : a (n + 4) = a (n + 3) + (n + 4) := a_succ_of_not_canSubtract hadd₄
  have hv₅ : a (n + 5) = a (n + 4) + (n + 5) := a_succ_of_not_canSubtract hadd₅
  have hv₆ : a (n + 6) = a (n + 5) + (n + 6) := a_succ_of_not_canSubtract hadd₆
  have hv₇ : a (n + 7) = a (n + 6) - (n + 7) := a_succ_of_canSubtract hsub₇
  omega

/-- **No loop-closing subtraction at length eight.**  The step pattern
`S S A A A A S` cannot be followed by another legal subtraction: the
exposed candidate is the pre-window value, which is already historical. -/
theorem double_descent_loop_extends
    {n : Nat}
    (hsub₁ : CanSubtract (n + 1) (stateAt n))
    (hsub₂ : CanSubtract (n + 2) (stateAt (n + 1)))
    (hadd₃ : ¬ CanSubtract (n + 3) (stateAt (n + 2)))
    (hadd₄ : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hadd₅ : ¬ CanSubtract (n + 5) (stateAt (n + 4)))
    (hadd₆ : ¬ CanSubtract (n + 6) (stateAt (n + 5)))
    (hsub₇ : CanSubtract (n + 7) (stateAt (n + 6))) :
    ¬ CanSubtract (n + 8) (stateAt (n + 7)) := by
  intro hcan
  have hfresh : a (n + 7) - (n + 8) ∉ valuesThrough (n + 7) := hcan.2
  have hvalue := double_descent_loop_candidate_returns
    hsub₁ hsub₂ hadd₃ hadd₄ hadd₅ hadd₆ hsub₇
  rw [hvalue] at hfresh
  exact hfresh (mem_valuesThrough_iff.mpr ⟨n, by omega, rfl⟩)

end Recaman
