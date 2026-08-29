import Recaman.PermanentAboveCorridorReplayFloor

namespace Recaman

noncomputable section

/-! # Second kernel floor of the replay fixed point

The first floor stopped at clock six.  Continuing the same three-way
elimination — actual orbit step, clock bound, straddled-target witnesses —
pushes the corridor much further, with one genuine obstruction: the value
nineteen does not occur in the orbit until time 99734, far beyond kernel
range, and nineteen lies inside both remaining straddle bands below clock
nine (`(13, 20]` at clock six and `(12, 21]` at clock eight).  Every other
target in those bands occurs by time 31, so clocks six and eight survive
only when the missing target is exactly nineteen.

Clocks seven, nine, eleven, thirteen, and fifteen subtract in the actual
orbit; clocks ten, twelve, fourteen, and sixteen fail the clock bound.
Clock seventeen is a real forced addition (`a 18 = 43 = 25 + 18`) but its
whole band `26..43` occurs in the orbit by time 111, so it dies
unconditionally.  Hence the crossing clock is at least eighteen unless the
target is exactly nineteen, and in either case the target is at least
nineteen.

The next boundary is clock eighteen: its band `(43, 62]` contains 61, whose
first orbit occurrence is at time 181653 — again far beyond kernel range
(the other members 44..60, 62 occur by time 222).  Raising the floor past
eighteen therefore needs a non-computational argument for the two deep
stragglers nineteen and sixty-one.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Clock six straddles exactly the targets `14..20`.  All of them except
nineteen occur in the orbit by time 31, and nineteen stays missing until
time 99734, so the only surviving target is nineteen. -/
theorem target_eq_nineteen_of_crossingTime_six
    (r : TerminalExactDischargeReplayCertificate source)
    (heq : r.crossingTime = 6) : target = 19 := by
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hmissing := r.target_missing
  have hlow : 13 < target := by
    have hvalue : a 6 = 13 := by decide
    have := hstraddle.1
    omega
  have hhigh : target ≤ 20 := by
    have hvalue : a 7 = 20 := by decide
    have hle : target ≤ a 7 := by simpa using hstraddle.2
    omega
  have hcases : target = 14 ∨ target = 15 ∨ target = 16 ∨ target = 17 ∨
      target = 18 ∨ target = 19 ∨ target = 20 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · rfl
  · exact absurd ⟨7, by decide⟩ hmissing

/-- Clock seven subtracts in the actual orbit (`a 8 = 12 ≠ 20 + 8`), so it
cannot carry the forced replay crossing. -/
theorem crossingTime_ne_seven
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 7 := by
  intro heq
  have hforced := r.forced_addition_at_crossing
  rw [heq] at hforced
  exact absurd hforced (by decide)

/-- Clock eight straddles exactly the targets `13..21`.  All of them except
nineteen occur in the orbit by time 31, so again only nineteen survives. -/
theorem target_eq_nineteen_of_crossingTime_eight
    (r : TerminalExactDischargeReplayCertificate source)
    (heq : r.crossingTime = 8) : target = 19 := by
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hmissing := r.target_missing
  have hlow : 12 < target := by
    have hvalue : a 8 = 12 := by decide
    have := hstraddle.1
    omega
  have hhigh : target ≤ 21 := by
    have hvalue : a 9 = 21 := by decide
    have hle : target ≤ a 9 := by simpa using hstraddle.2
    omega
  have hcases : target = 13 ∨ target = 14 ∨ target = 15 ∨ target = 16 ∨
      target = 17 ∨ target = 18 ∨ target = 19 ∨ target = 20 ∨
      target = 21 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨6, by decide⟩ hmissing
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · rfl
  · exact absurd ⟨7, by decide⟩ hmissing
  · exact absurd ⟨9, by decide⟩ hmissing

/-- Below clock nine, only the exceptional target nineteen survives. -/
theorem nine_le_crossingTime_or_target_eq_nineteen
    (r : TerminalExactDischargeReplayCertificate source) :
    9 ≤ r.crossingTime ∨ target = 19 := by
  have hsix := r.six_le_crossingTime
  by_cases hnine : 9 ≤ r.crossingTime
  · exact Or.inl hnine
  · have hcases : r.crossingTime = 6 ∨ r.crossingTime = 7 ∨
        r.crossingTime = 8 := by omega
    rcases hcases with heq | heq | heq
    · exact Or.inr (r.target_eq_nineteen_of_crossingTime_six heq)
    · exact absurd heq r.crossingTime_ne_seven
    · exact Or.inr (r.target_eq_nineteen_of_crossingTime_eight heq)

/-- Clocks nine through sixteen die by the actual orbit step or the clock
bound: odd clocks subtract, even clocks fall below their own clock. -/
theorem seventeen_le_crossingTime_or_target_eq_nineteen
    (r : TerminalExactDischargeReplayCertificate source) :
    17 ≤ r.crossingTime ∨ target = 19 := by
  rcases r.nine_le_crossingTime_or_target_eq_nineteen with hnine | htarget
  · by_cases hbig : 17 ≤ r.crossingTime
    · exact Or.inl hbig
    · have hforced := r.forced_addition_at_crossing
      have hclock := r.clock_lt_crossingValue
      have hcases : r.crossingTime = 9 ∨ r.crossingTime = 10 ∨
          r.crossingTime = 11 ∨ r.crossingTime = 12 ∨
          r.crossingTime = 13 ∨ r.crossingTime = 14 ∨
          r.crossingTime = 15 ∨ r.crossingTime = 16 := by omega
      rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq
      · rw [heq] at hforced
        exact absurd hforced (by decide)
      · rw [heq] at hclock
        exact absurd hclock (by decide)
      · rw [heq] at hforced
        exact absurd hforced (by decide)
      · rw [heq] at hclock
        exact absurd hclock (by decide)
      · rw [heq] at hforced
        exact absurd hforced (by decide)
      · rw [heq] at hclock
        exact absurd hclock (by decide)
      · rw [heq] at hforced
        exact absurd hforced (by decide)
      · rw [heq] at hclock
        exact absurd hclock (by decide)
  · exact Or.inr htarget

/-- Clock seventeen is a genuine forced addition straddling exactly the
targets `26..43`, but every one of them occurs in the orbit by time 111. -/
theorem crossingTime_ne_seventeen
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 17 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hmissing := r.target_missing
  have hlow : 25 < target := by
    have hvalue : a 17 = 25 := by decide
    have := hstraddle.1
    omega
  have hhigh : target ≤ 43 := by
    have hvalue : a 18 = 43 := by set_option maxRecDepth 100000 in decide
    have hle : target ≤ a 18 := by simpa using hstraddle.2
    omega
  have hcases : target = 26 ∨ target = 27 ∨ target = 28 ∨ target = 29 ∨
      target = 30 ∨ target = 31 ∨ target = 32 ∨ target = 33 ∨
      target = 34 ∨ target = 35 ∨ target = 36 ∨ target = 37 ∨
      target = 38 ∨ target = 39 ∨ target = 40 ∨ target = 41 ∨
      target = 42 ∨ target = 43 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨64, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨62, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨60, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨58, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨56, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨54, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨52, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨50, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨48, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨46, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨44, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨42, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨40, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨38, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨111, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨22, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨20, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨18, by set_option maxRecDepth 100000 in decide⟩ hmissing

/-- Below clock eighteen, only the exceptional target nineteen survives. -/
theorem eighteen_le_crossingTime_or_target_eq_nineteen
    (r : TerminalExactDischargeReplayCertificate source) :
    18 ≤ r.crossingTime ∨ target = 19 := by
  rcases r.seventeen_le_crossingTime_or_target_eq_nineteen with hbig | htarget
  · by_cases hmore : 18 ≤ r.crossingTime
    · exact Or.inl hmore
    · have heq : r.crossingTime = 17 := by omega
      exact absurd heq r.crossingTime_ne_seventeen
  · exact Or.inr htarget

/-- Away from the exceptional target nineteen the crossing clock is at
least eighteen. -/
theorem eighteen_le_crossingTime_of_target_ne_nineteen
    (r : TerminalExactDischargeReplayCertificate source)
    (hne : target ≠ 19) : 18 ≤ r.crossingTime := by
  rcases r.eighteen_le_crossingTime_or_target_eq_nineteen with hbig | htarget
  · exact hbig
  · exact absurd htarget hne

/-- Hence any replay fixed point straddles a target of at least nineteen:
either the target is literally nineteen, or the clock floor pushes the
target above nineteen. -/
theorem nineteen_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    19 ≤ target := by
  have hclock := r.crossingTime_lt_target
  rcases r.eighteen_le_crossingTime_or_target_eq_nineteen with hbig | htarget
  · omega
  · omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
