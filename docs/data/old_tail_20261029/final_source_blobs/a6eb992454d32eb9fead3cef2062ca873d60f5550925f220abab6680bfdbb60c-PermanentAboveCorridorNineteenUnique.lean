import Recaman.PermanentAboveCorridorNineteenReplay

namespace Recaman

noncomputable section

/-! # Uniqueness of the nineteen replay cycle

The nineteen replay still had two candidate clocks.  The discharge itself
removes one: the historical downcross needs an orbit value at or above
nineteen strictly before the crossing, and before clock six the orbit never
exceeds thirteen.  Before clock eight the only value at or above nineteen
is `a 7 = 20`, so the downcross time is exactly seven and the fresh
endpoint is the crossing itself — an immediate return.

A hypothetical counterexample at nineteen therefore replays exactly one
fully explicit cycle: the downcross `20 → 12` at time seven, returning
immediately through the crossing `a 8 = 12 < 19 ≤ 21 = a 9`, with anchor
twelve, blocker three, and blocker first time two.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Clock six cannot host a nineteen replay: its downcross would need an
orbit value at or above nineteen before time six, and none exists. -/
theorem crossingTime_ne_six_of_nineteen
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    r.crossingTime ≠ 6 := by
  intro hsix
  have heligible := r.eligible
  have htime := r.time_eq
  have hdown : source.downTime ≤ 5 := by omega
  have habove := source.downcross.start_at_or_above
  have habove' : 19 ≤ a source.downTime := by omega
  have hcases : source.downTime = 0 ∨ source.downTime = 1 ∨
      source.downTime = 2 ∨ source.downTime = 3 ∨ source.downTime = 4 ∨
      source.downTime = 5 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq <;>
    rw [heq] at habove' <;> exact absurd habove' (by decide)

/-- The nineteen replay clock is exactly eight. -/
theorem crossingTime_eq_eight_of_nineteen
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    r.crossingTime = 8 := by
  rcases r.crossingTime_eq_six_or_eight_of_nineteen h19 with hsix | height
  · exact absurd hsix (r.crossingTime_ne_six_of_nineteen h19)
  · exact height

/-- At clock eight the downcross time is exactly seven: the only orbit
value at or above nineteen before time eight is `a 7 = 20`. -/
theorem downTime_eq_seven_of_nineteen
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    source.downTime = 7 := by
  have height := r.crossingTime_eq_eight_of_nineteen h19
  have heligible := r.eligible
  have htime := r.time_eq
  have hdown : source.downTime ≤ 7 := by omega
  have habove := source.downcross.start_at_or_above
  have habove' : 19 ≤ a source.downTime := by omega
  by_cases hseven : source.downTime = 7
  · exact hseven
  · have hcases : source.downTime = 0 ∨ source.downTime = 1 ∨
        source.downTime = 2 ∨ source.downTime = 3 ∨
        source.downTime = 4 ∨ source.downTime = 5 ∨
        source.downTime = 6 := by omega
    rcases hcases with heq | heq | heq | heq | heq | heq | heq <;>
      rw [heq] at habove' <;> exact absurd habove' (by decide)

/-- Full uniqueness: the nineteen replay is one explicit cycle — downcross
at seven, immediate return through the crossing at eight, anchor twelve,
blocker three first seen at two. -/
theorem nineteen_replay_unique
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    r.crossingTime = 8 ∧ source.downTime = 7 ∧ source.returnTime = 8 ∧
      source.oldCrossingTime = 8 ∧ parent.anchorParent = 12 ∧
      r.candidate = 3 ∧ r.firstTime = 2 := by
  have height := r.crossingTime_eq_eight_of_nineteen h19
  have hdown := r.downTime_eq_seven_of_nineteen h19
  have hreturn := r.return_eq_crossingTime
  have hold := r.time_eq
  have hpins := r.eight_replay_pins height
  exact ⟨height, hdown, by omega, by omega, hpins.1, hpins.2.1,
    hpins.2.2⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
