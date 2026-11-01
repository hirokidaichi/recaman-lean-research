import Recaman.PermanentAboveCorridorNineteenUnique

namespace Recaman

noncomputable section

/-! # The nineteen tail minimum is twenty-one

The unique nineteen cycle also pins the historical minimum data.  The tail
minimum's predecessor value first occurs before the downcross time seven,
exceeds nineteen, and the only orbit value above nineteen in that range is
`a 7 = 20`.  Hence the predecessor first time is exactly seven and the tail
minimum value is exactly twenty-one.

A hypothetical counterexample at nineteen is thereby pinned in every stored
numeric component: it replays the `20 → 12` downcross with immediate return
at clock eight, its permanent tail hovers above nineteen with minimum value
twenty-one, and the minimum's predecessor is the value twenty first seen at
time seven.  All remaining freedom lives in the unbounded tail clocks.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- In the nineteen replay the minimum's predecessor first occurs exactly
at time seven, and the tail minimum value is exactly twenty-one. -/
theorem nineteen_minimum_pins
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    source.historicalFirstTime = 7 ∧
      a source.historicalMinimumTime = 21 := by
  have hdown := r.downTime_eq_seven_of_nineteen h19
  have hle := source.downcross.horizon_le_time
  have hle' : source.historicalFirstTime ≤ 7 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have hvalue : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have htarget := source.historical_minimum.target_lt_predecessor
  have htarget' : 19 < a source.historicalMinimumTime - 1 := by omega
  have hseven : source.historicalFirstTime = 7 := by
    by_cases hseven : source.historicalFirstTime = 7
    · exact hseven
    · have hcases : source.historicalFirstTime = 0 ∨
          source.historicalFirstTime = 1 ∨
          source.historicalFirstTime = 2 ∨
          source.historicalFirstTime = 3 ∨
          source.historicalFirstTime = 4 ∨
          source.historicalFirstTime = 5 ∨
          source.historicalFirstTime = 6 := by omega
      rcases hcases with heq | heq | heq | heq | heq | heq | heq
      · rw [heq] at hvalue
        have hbound : a 0 ≤ 13 := by decide
        omega
      · rw [heq] at hvalue
        have hbound : a 1 ≤ 13 := by decide
        omega
      · rw [heq] at hvalue
        have hbound : a 2 ≤ 13 := by decide
        omega
      · rw [heq] at hvalue
        have hbound : a 3 ≤ 13 := by decide
        omega
      · rw [heq] at hvalue
        have hbound : a 4 ≤ 13 := by decide
        omega
      · rw [heq] at hvalue
        have hbound : a 5 ≤ 13 := by decide
        omega
      · rw [heq] at hvalue
        have hbound : a 6 ≤ 13 := by decide
        omega
  refine ⟨hseven, ?_⟩
  rw [hseven] at hvalue
  have htwenty : a 7 = 20 := by decide
  omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
