import Recaman.OrbitComb
import Recaman.History

namespace Recaman

/-! # Witness construction of comb steps

Deciding a comb step re-evaluates the orbit state, which is exactly what
compressed verification must avoid.  This module builds a comb step from
three value-level facts instead: a reason why the addition is forced — the
subtraction defect is nonpositive or has already occurred —, positivity of
the entry value, and freshness of the decremented value at the repayment
clock.  The first two travel with local witnesses; only the freshness fact
is global, and it is precisely the ingredient a values-representation
theorem for comb segments will supply.
-/

/-- A comb step follows from a blocked-up reason, entry positivity, and
freshness of the decremented value. -/
theorem combStep_of_witness
    {s : Nat}
    (hblocked : a s ≤ s + 1 ∨ (a s - (s + 1)) ∈ valuesThrough s)
    (hpositive : 1 < a s)
    (hfresh : (a s - 1) ∉ valuesThrough (s + 1)) :
    CombStep s := by
  have hforced : ¬ CanSubtract (s + 1) (stateAt s) := by
    intro hcan
    rcases hcan with ⟨hlt, hnotin⟩
    rcases hblocked with hsmall | hseen
    · exact absurd hlt (by
        show ¬ s + 1 < (stateAt s).value
        have hvalue : (stateAt s).value = a s := rfl
        omega)
    · exact hnotin hseen
  have hup : a (s + 1) = a s + (s + 1) :=
    a_succ_of_not_canSubtract hforced
  refine ⟨hforced, ?_, ?_⟩
  · show s + 2 < (stateAt (s + 1)).value
    have hvalue : (stateAt (s + 1)).value = a (s + 1) := rfl
    omega
  · show (stateAt (s + 1)).value - (s + 2) ∉ (stateAt (s + 1)).seen
    have hvalue : (stateAt (s + 1)).value = a (s + 1) := rfl
    have hdefect : (stateAt (s + 1)).value - (s + 2) = a s - 1 := by
      omega
    rw [hdefect]
    exact hfresh

/-- Inside a comb run every low-rail landing is fresh, so consecutive comb
periods chain their freshness requirements downward: the run consumes the
descending values `a s - 1, a s - 2, …` one per period. -/
theorem CombRun.low_rail_fresh
    {s k : Nat} (h : CombRun s k) :
    ∀ i, i < k →
      (a (s + 2 * i + 2)) ∉ valuesThrough (s + 2 * i + 1) := by
  intro i hik
  have hstep := h i hik
  have hsub := hstep.legal_down
  rcases hsub with ⟨hlt, hnotin⟩
  have hvalue : a (s + 2 * i + 2) =
      a (s + 2 * i + 1) - (s + 2 * i + 2) := by
    have := a_succ_of_canSubtract (n := s + 2 * i + 1) hstep.legal_down
    simpa [Nat.add_assoc] using this
  rw [hvalue]
  exact hnotin

end Recaman
