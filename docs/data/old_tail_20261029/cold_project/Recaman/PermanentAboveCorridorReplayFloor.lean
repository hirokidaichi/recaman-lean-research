import Recaman.PermanentAboveCorridorReplayCorridor

namespace Recaman

noncomputable section

/-! # Kernel floor of the replay fixed point

The replay crossing is a genuine orbit event: its step really is a forced
addition, its value really exceeds its clock, and every target it straddles
really is missing.  All three facts are decidable on concrete clocks, so the
kernel can raise the floor of the fixed point.

Clock four fails the value bound (`a 4 = 2`).  Clock three passes the value
bound but its actual orbit step subtracts (`a 4 ≠ a 3 + 4`).  Clock five
straddles exactly the targets `8..13`, and each of them occurs in the orbit
by time sixteen, contradicting the missing-target field.  Hence a replay
fixed point needs crossing clock at least six and target at least eight.
The target is also bounded above by the triangular envelope at the crossing
endpoint, so both parameters of the fixed point are pinched from both
sides.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The replay lives inside a virtual counterexample: its target is missing
from the whole orbit. -/
theorem target_missing
    (_r : TerminalExactDischargeReplayCertificate source) :
    ¬ ∃ time, a time = target :=
  source.combined.tail.target_missing

/-- Triangular envelope: the straddled target is at most the maximal
possible value at the crossing endpoint. -/
theorem target_le_upperTri
    (r : TerminalExactDischargeReplayCertificate source) :
    target ≤ upperTri (r.crossingTime + 1) :=
  Nat.le_trans r.crossing_straddles_target.2 (a_le_upperTri _)

/-- Clocks three and four are excluded by the actual orbit step. -/
theorem five_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    5 ≤ r.crossingTime := by
  have hthree := r.three_le_crossingTime
  have hforced := r.forced_addition_at_crossing
  have hclock := r.clock_lt_crossingValue
  by_cases hfive : 5 ≤ r.crossingTime
  · exact hfive
  · have hcases : r.crossingTime = 3 ∨ r.crossingTime = 4 := by omega
    rcases hcases with heq | heq
    · rw [heq] at hforced
      exact absurd hforced (by decide)
    · rw [heq] at hclock
      exact absurd hclock (by decide)

/-- Clock five straddles only targets `8..13`, all of which occur in the
orbit by time sixteen. -/
theorem six_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    6 ≤ r.crossingTime := by
  have hfive := r.five_le_crossingTime
  by_cases hsix : 6 ≤ r.crossingTime
  · exact hsix
  · have heq : r.crossingTime = 5 := by omega
    have hstraddle := r.crossing_straddles_target
    rw [heq] at hstraddle
    have hmissing := r.target_missing
    have hlow : 7 < target := by
      have hvalue : a 5 = 7 := by decide
      have := hstraddle.1
      omega
    have hhigh : target ≤ 13 := by
      have hvalue : a 6 = 13 := by decide
      have hle : target ≤ a 6 := by simpa using hstraddle.2
      omega
    have hcases : target = 8 ∨ target = 9 ∨ target = 10 ∨ target = 11 ∨
        target = 12 ∨ target = 13 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd ⟨16, by decide⟩ hmissing
    · exact absurd ⟨14, by decide⟩ hmissing
    · exact absurd ⟨12, by decide⟩ hmissing
    · exact absurd ⟨10, by decide⟩ hmissing
    · exact absurd ⟨8, by decide⟩ hmissing
    · exact absurd ⟨6, by decide⟩ hmissing

/-- Hence any replay fixed point straddles a target of at least eight. -/
theorem eight_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    8 ≤ target := by
  have hsix := r.six_le_crossingTime
  have hclock := r.crossingTime_lt_target
  omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
