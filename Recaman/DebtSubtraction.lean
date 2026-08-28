import Recaman.Mechanisms
import Recaman.PhaseSearch

namespace Recaman

/-- Data recovered by looking one step behind a first occurrence that was
created by a legal subtraction.  The predecessor is itself replaced by its
first occurrence; that first occurrence is strictly earlier than the landing
time even though its value is strictly larger than the landing value. -/
theorem legalSubtraction_firstAt_predecessor
    {y fy : Nat}
    (hfirst : FirstAt a y fy)
    (hfy : 0 < fy)
    (hcan : CanSubtract fy (stateAt (fy - 1))) :
    ∃ x fx,
      a (fy - 1) = x ∧
      FirstAt a x fx ∧
      fx < fy ∧
      y + fy = x ∧
      y ∉ valuesThrough (fy - 1) ∧
      y < x := by
  have htime : (fy - 1) + 1 = fy := by omega
  have hcan' : CanSubtract ((fy - 1) + 1) (stateAt (fy - 1)) := by
    simpa [htime] using hcan
  have hlanding : a fy = a (fy - 1) - fy := by
    simpa [htime] using
      (a_succ_of_canSubtract (n := fy - 1) hcan')
  have hy_eq : y = a (fy - 1) - fy := by
    rw [← hfirst.1]
    exact hlanding
  have hpositive : fy < a (fy - 1) := by
    simpa [a] using hcan.1
  have hsum : y + fy = a (fy - 1) := by omega
  have hfresh : y ∉ valuesThrough (fy - 1) := by
    rw [hy_eq]
    exact hcan.2
  rcases history_member_has_firstAt
      (current_mem_valuesThrough (fy - 1)) with ⟨fx, hfx, hfirstX⟩
  refine ⟨a (fy - 1), fx, rfl, hfirstX, ?_, hsum, hfresh, ?_⟩
  · omega
  · omega

/-- If the legal subtraction landing remains above the target, the recovered
predecessor is immediately a value-decreasing `CoverageStep`. -/
theorem legalSubtraction_firstAt_gives_coverageStep
    {m y fy : Nat}
    (hfirst : FirstAt a y fy)
    (hfy : 0 < fy)
    (hcan : CanSubtract fy (stateAt (fy - 1)))
    (hmy : m ≤ y) :
    CoverageStep m (a (fy - 1)) (fy - 1) := by
  have htime : (fy - 1) + 1 = fy := by omega
  have hcan' : CanSubtract ((fy - 1) + 1) (stateAt (fy - 1)) := by
    simpa [htime] using hcan
  have hcoverage := subtraction_gives_coverageStep
    (m := m) (n := fy - 1) hcan'
  rw [htime] at hcoverage
  exact hcoverage (by simpa [hfirst.1] using hmy)

/-- The same predecessor recovery directly closes the legal-subtraction case
of a debt node.  The horizon and anchor stay fixed, while the predecessor's
first-occurrence time strictly lowers the debt-local component. -/
theorem legalSubtraction_firstAt_gives_debtProgress
    {m horizon anchor y fy : Nat}
    (hfirst : FirstAt a y fy)
    (hfy : 0 < fy)
    (hcan : CanSubtract fy (stateAt (fy - 1)))
    (hmy : m ≤ y) :
    ∃ x fx,
      m ≤ x ∧
      FirstAt a x fx ∧
      y < x ∧
      PhaseSearchProgress m
        ⟨horizon, anchor, .debt, fx⟩
        ⟨horizon, anchor, .debt, fy⟩ := by
  rcases legalSubtraction_firstAt_predecessor hfirst hfy hcan with
    ⟨x, fx, _, hfirstX, hfx, _, _, hyx⟩
  exact ⟨x, fx, Nat.le_trans hmy (Nat.le_of_lt hyx), hfirstX, hyx,
    phaseSearch_debtTimeDrop hfx⟩

end Recaman
