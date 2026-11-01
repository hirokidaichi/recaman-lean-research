import Recaman.PermanentAboveCorridorReplayFloorTwo

namespace Recaman

noncomputable section

/-! # Third kernel floor of the replay fixed point

The second floor stopped at clock eighteen with the single exceptional
target nineteen.  Continuing the same three-way elimination — actual orbit
step, clock bound, straddled-target witnesses — meets a second genuine
obstruction: the value sixty-one does not occur in the orbit until time
181653, far beyond kernel range, and sixty-one lies inside both remaining
straddle bands below clock twenty-one (`(43, 62]` at clock eighteen and
`(42, 63]` at clock twenty).  Every other target in those bands occurs by
time 222, so clocks eighteen and twenty survive only when the missing
target is exactly sixty-one.

Clock nineteen subtracts in the actual orbit (`a 20 = 42 ≠ 62 + 20`).
Past clock twenty the comb is mechanical: clocks 21, 22, 24, 26, 28, and
30 subtract in the actual orbit, and the descending low rail `a 23 = 18`,
`a 25 = 17`, `a 27 = 16`, `a 29 = 15`, `a 31 = 14` fails the clock bound
at the odd clocks 23, 25, 27, 29, 31.  Hence the crossing clock is at
least thirty-two unless the target is nineteen or sixty-one, and away
from those exceptional targets the target is at least thirty-four.

The next boundary is clock thirty-two: it is a real forced addition
(`a 33 = 79 = 46 + 33`) but its band `(46, 79]` contains 76, whose first
orbit occurrence is at time 181643 — a third deep straggler beyond kernel
range (the other members occur by time 222).  Raising the floor past
thirty-two therefore needs a non-computational argument for the deep
stragglers 19, 61, and 76.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Clock eighteen straddles exactly the targets `44..62`.  All of them
except sixty-one occur in the orbit by time 222, and sixty-one stays
missing until time 181653, so the only surviving target is sixty-one. -/
theorem target_eq_sixtyone_of_crossingTime_eighteen
    (r : TerminalExactDischargeReplayCertificate source)
    (heq : r.crossingTime = 18) : target = 61 := by
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hmissing := r.target_missing
  have hlow : 43 < target := by
    have hvalue : a 18 = 43 := by set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have hhigh : target ≤ 62 := by
    have hvalue : a 19 = 62 := by set_option maxRecDepth 100000 in decide
    have hle : target ≤ a 19 := by simpa using hstraddle.2
    omega
  have hcases : target = 44 ∨ target = 45 ∨ target = 46 ∨ target = 47 ∨
      target = 48 ∨ target = 49 ∨ target = 50 ∨ target = 51 ∨
      target = 52 ∨ target = 53 ∨ target = 54 ∨ target = 55 ∨
      target = 56 ∨ target = 57 ∨ target = 58 ∨ target = 59 ∨
      target = 60 ∨ target = 61 ∨ target = 62 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨28, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨30, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨32, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨222, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨220, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨218, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨216, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨214, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨212, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨210, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨208, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨206, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨204, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨202, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨200, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨198, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨196, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · rfl
  · exact absurd ⟨19, by set_option maxRecDepth 100000 in decide⟩ hmissing

/-- Clock nineteen subtracts in the actual orbit (`a 20 = 42 ≠ 62 + 20`),
so it cannot carry the forced replay crossing. -/
theorem crossingTime_ne_nineteen
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 19 := by
  intro heq
  have hforced := r.forced_addition_at_crossing
  rw [heq] at hforced
  exact absurd hforced (by set_option maxRecDepth 100000 in decide)

/-- Clock twenty straddles exactly the targets `43..63`.  All of them
except sixty-one occur in the orbit by time 222, so again only sixty-one
survives. -/
theorem target_eq_sixtyone_of_crossingTime_twenty
    (r : TerminalExactDischargeReplayCertificate source)
    (heq : r.crossingTime = 20) : target = 61 := by
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hmissing := r.target_missing
  have hlow : 42 < target := by
    have hvalue : a 20 = 42 := by set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have hhigh : target ≤ 63 := by
    have hvalue : a 21 = 63 := by set_option maxRecDepth 100000 in decide
    have hle : target ≤ a 21 := by simpa using hstraddle.2
    omega
  have hcases : target = 43 ∨ target = 44 ∨ target = 45 ∨ target = 46 ∨
      target = 47 ∨ target = 48 ∨ target = 49 ∨ target = 50 ∨
      target = 51 ∨ target = 52 ∨ target = 53 ∨ target = 54 ∨
      target = 55 ∨ target = 56 ∨ target = 57 ∨ target = 58 ∨
      target = 59 ∨ target = 60 ∨ target = 61 ∨ target = 62 ∨
      target = 63 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨18, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨28, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨30, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨32, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨222, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨220, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨218, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨216, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨214, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨212, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨210, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨208, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨206, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨204, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨202, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨200, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨198, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨196, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · rfl
  · exact absurd ⟨19, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨21, by set_option maxRecDepth 100000 in decide⟩ hmissing

/-- Below clock twenty-one, only the exceptional targets nineteen and
sixty-one survive. -/
theorem twentyone_le_crossingTime_or_exceptional
    (r : TerminalExactDischargeReplayCertificate source) :
    21 ≤ r.crossingTime ∨ target = 19 ∨ target = 61 := by
  rcases r.eighteen_le_crossingTime_or_target_eq_nineteen with hbig | ht
  · by_cases hmore : 21 ≤ r.crossingTime
    · exact Or.inl hmore
    · have hcases : r.crossingTime = 18 ∨ r.crossingTime = 19 ∨
          r.crossingTime = 20 := by omega
      rcases hcases with heq | heq | heq
      · exact Or.inr (Or.inr
          (r.target_eq_sixtyone_of_crossingTime_eighteen heq))
      · exact absurd heq r.crossingTime_ne_nineteen
      · exact Or.inr (Or.inr
          (r.target_eq_sixtyone_of_crossingTime_twenty heq))
  · exact Or.inr (Or.inl ht)

/-- Clocks twenty-one through thirty-one die mechanically: clocks 21, 22,
24, 26, 28, and 30 subtract in the actual orbit, while the descending low
rail fails the clock bound at 23, 25, 27, 29, and 31. -/
theorem thirtytwo_le_crossingTime_or_exceptional
    (r : TerminalExactDischargeReplayCertificate source) :
    32 ≤ r.crossingTime ∨ target = 19 ∨ target = 61 := by
  rcases r.twentyone_le_crossingTime_or_exceptional with hbig | hexc
  · by_cases hmore : 32 ≤ r.crossingTime
    · exact Or.inl hmore
    · have hforced := r.forced_addition_at_crossing
      have hclock := r.clock_lt_crossingValue
      have hcases : r.crossingTime = 21 ∨ r.crossingTime = 22 ∨
          r.crossingTime = 23 ∨ r.crossingTime = 24 ∨
          r.crossingTime = 25 ∨ r.crossingTime = 26 ∨
          r.crossingTime = 27 ∨ r.crossingTime = 28 ∨
          r.crossingTime = 29 ∨ r.crossingTime = 30 ∨
          r.crossingTime = 31 := by omega
      rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq |
        heq | heq | heq
      · rw [heq] at hforced
        exact absurd hforced (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hforced
        exact absurd hforced (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hclock
        exact absurd hclock (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hforced
        exact absurd hforced (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hclock
        exact absurd hclock (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hforced
        exact absurd hforced (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hclock
        exact absurd hclock (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hforced
        exact absurd hforced (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hclock
        exact absurd hclock (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hforced
        exact absurd hforced (by set_option maxRecDepth 100000 in decide)
      · rw [heq] at hclock
        exact absurd hclock (by set_option maxRecDepth 100000 in decide)
  · exact Or.inr hexc

/-- Away from the exceptional targets nineteen and sixty-one the crossing
clock is at least thirty-two. -/
theorem thirtytwo_le_crossingTime_of_ne_exceptional
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target ≠ 19) (h61 : target ≠ 61) : 32 ≤ r.crossingTime := by
  rcases r.thirtytwo_le_crossingTime_or_exceptional with hbig | ht | ht
  · exact hbig
  · exact absurd ht h19
  · exact absurd ht h61

/-- Hence any replay fixed point is exceptional or deep: its target is
literally nineteen or sixty-one, or the clock floor pushes the target to
at least thirty-four. -/
theorem target_split
    (r : TerminalExactDischargeReplayCertificate source) :
    target = 19 ∨ target = 61 ∨ 34 ≤ target := by
  have hclock := r.crossingTime_lt_target
  rcases r.thirtytwo_le_crossingTime_or_exceptional with hbig | ht | ht
  · exact Or.inr (Or.inr (by omega))
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)

end TerminalExactDischargeReplayCertificate

end

end Recaman
