import Recaman.PermanentAboveCorridorFixedPointFloor

namespace Recaman

noncomputable section

/-! # Second kernel floor of the unified fixed-point core

The first core floor stopped at clock six.  The replay side pushed its
floor to eighteen using the terminal blocker for the even clocks, but the
unified core carries no blocker, so every surviving clock must die by band
elimination alone: the straddle `a C < target ≤ a (C + 1)` pins the target
into a finite band, and each band member that occurs in the kernel-range
orbit contradicts the missing-target hypothesis.

Odd clocks seven through fifteen subtract in the actual orbit, refuting
the forced addition directly.  Every even clock from six to sixteen
straddles a band whose members all occur by time 31 — except the value
nineteen, which stays missing until time 99734, far beyond kernel range,
and lies inside all six bands.  Clock seventeen is a genuine forced
addition (`a 18 = 43 = 25 + 18`) but its whole band `26..43` occurs by
time 111, so it dies unconditionally.  Hence the crossing clock is at
least eighteen unless the target is exactly nineteen.

Independently of any clock analysis, the target itself is at least
nineteen: it is positive because the crossing value sits below it, and
every value from one to eighteen occurs in the orbit by time 131.

The next boundary is clock eighteen: its band `(43, 62]` contains 61,
whose first orbit occurrence is at time 181653 — again far beyond kernel
range.  Raising the core floor past eighteen therefore needs a
non-computational argument for the two deep stragglers nineteen and
sixty-one, exactly as on the replay side.
-/

namespace TailFixedPointCore

variable {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}

/-- Any missing target of a fixed-point core is at least nineteen: the
crossing value below it makes it positive, and every value from one to
eighteen occurs in the orbit by time 131.  No clock analysis is needed. -/
theorem nineteen_le_target
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target) :
    19 ≤ target := by
  by_cases hbig : 19 ≤ target
  · exact hbig
  · have hbelow := core.below
    have hcases : target = 1 ∨ target = 2 ∨ target = 3 ∨ target = 4 ∨
        target = 5 ∨ target = 6 ∨ target = 7 ∨ target = 8 ∨
        target = 9 ∨ target = 10 ∨ target = 11 ∨ target = 12 ∨
        target = 13 ∨ target = 14 ∨ target = 15 ∨ target = 16 ∨
        target = 17 ∨ target = 18 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd ⟨1, by decide⟩ missing
    · exact absurd ⟨4, by decide⟩ missing
    · exact absurd ⟨2, by decide⟩ missing
    · exact absurd ⟨131, by
        set_option maxRecDepth 100000 in decide⟩ missing
    · exact absurd ⟨129, by
        set_option maxRecDepth 100000 in decide⟩ missing
    · exact absurd ⟨3, by decide⟩ missing
    · exact absurd ⟨5, by decide⟩ missing
    · exact absurd ⟨16, by decide⟩ missing
    · exact absurd ⟨14, by decide⟩ missing
    · exact absurd ⟨12, by decide⟩ missing
    · exact absurd ⟨10, by decide⟩ missing
    · exact absurd ⟨8, by decide⟩ missing
    · exact absurd ⟨6, by decide⟩ missing
    · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ missing
    · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ missing
    · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ missing
    · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ missing
    · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ missing

/-- Clock six straddles exactly the targets `14..20`.  All of them except
nineteen occur in the orbit by time 31, and nineteen stays missing until
time 99734, so the only surviving target is nineteen. -/
theorem target_eq_nineteen_of_crossingTime_six
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (heq : crossingTime = 6) : target = 19 := by
  have hbelow := core.below
  have hendpoint := core.endpoint_ge
  rw [heq] at hbelow hendpoint
  have hlow : 13 < target := by
    have hvalue : a 6 = 13 := by decide
    omega
  have hhigh : target ≤ 20 := by
    have hvalue : a 7 = 20 := by decide
    have hle : target ≤ a 7 := by simpa using hendpoint
    omega
  have hcases : target = 14 ∨ target = 15 ∨ target = 16 ∨ target = 17 ∨
      target = 18 ∨ target = 19 ∨ target = 20 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ missing
  · rfl
  · exact absurd ⟨7, by decide⟩ missing

/-- Clock seven subtracts in the actual orbit (`a 8 = 12 ≠ 20 + 8`), so
the unified core cannot force an addition there. -/
theorem crossingTime_ne_seven
    (core : TailFixedPointCore target parent crossingTime) :
    crossingTime ≠ 7 := by
  intro heq
  have hforced := core.forced
  rw [heq] at hforced
  exact absurd hforced (by decide)

/-- Clock eight straddles exactly the targets `13..21`.  All of them
except nineteen occur in the orbit by time 31, so only nineteen
survives. -/
theorem target_eq_nineteen_of_crossingTime_eight
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (heq : crossingTime = 8) : target = 19 := by
  have hbelow := core.below
  have hendpoint := core.endpoint_ge
  rw [heq] at hbelow hendpoint
  have hlow : 12 < target := by
    have hvalue : a 8 = 12 := by decide
    omega
  have hhigh : target ≤ 21 := by
    have hvalue : a 9 = 21 := by decide
    have hle : target ≤ a 9 := by simpa using hendpoint
    omega
  have hcases : target = 13 ∨ target = 14 ∨ target = 15 ∨ target = 16 ∨
      target = 17 ∨ target = 18 ∨ target = 19 ∨ target = 20 ∨
      target = 21 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨6, by decide⟩ missing
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ missing
  · rfl
  · exact absurd ⟨7, by decide⟩ missing
  · exact absurd ⟨9, by decide⟩ missing

/-- Clock nine subtracts in the actual orbit (`a 10 = 11 ≠ 21 + 10`). -/
theorem crossingTime_ne_nine
    (core : TailFixedPointCore target parent crossingTime) :
    crossingTime ≠ 9 := by
  intro heq
  have hforced := core.forced
  rw [heq] at hforced
  exact absurd hforced (by decide)

/-- Clock ten is a genuine forced addition (`a 11 = 22 = 11 + 11`)
straddling exactly the targets `12..22`.  All of them except nineteen
occur in the orbit by time 31, so only nineteen survives. -/
theorem target_eq_nineteen_of_crossingTime_ten
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (heq : crossingTime = 10) : target = 19 := by
  have hbelow := core.below
  have hendpoint := core.endpoint_ge
  rw [heq] at hbelow hendpoint
  have hlow : 11 < target := by
    have hvalue : a 10 = 11 := by decide
    omega
  have hhigh : target ≤ 22 := by
    have hvalue : a 11 = 22 := by decide
    have hle : target ≤ a 11 := by simpa using hendpoint
    omega
  have hcases : target = 12 ∨ target = 13 ∨ target = 14 ∨ target = 15 ∨
      target = 16 ∨ target = 17 ∨ target = 18 ∨ target = 19 ∨
      target = 20 ∨ target = 21 ∨ target = 22 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact absurd ⟨8, by decide⟩ missing
  · exact absurd ⟨6, by decide⟩ missing
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ missing
  · rfl
  · exact absurd ⟨7, by decide⟩ missing
  · exact absurd ⟨9, by decide⟩ missing
  · exact absurd ⟨11, by decide⟩ missing

/-- Clock eleven subtracts in the actual orbit
(`a 12 = 10 ≠ 22 + 12`). -/
theorem crossingTime_ne_eleven
    (core : TailFixedPointCore target parent crossingTime) :
    crossingTime ≠ 11 := by
  intro heq
  have hforced := core.forced
  rw [heq] at hforced
  exact absurd hforced (by decide)

/-- Clock twelve is a genuine forced addition (`a 13 = 23 = 10 + 13`)
straddling exactly the targets `11..23`.  All of them except nineteen
occur in the orbit by time 31, so only nineteen survives. -/
theorem target_eq_nineteen_of_crossingTime_twelve
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (heq : crossingTime = 12) : target = 19 := by
  have hbelow := core.below
  have hendpoint := core.endpoint_ge
  rw [heq] at hbelow hendpoint
  have hlow : 10 < target := by
    have hvalue : a 12 = 10 := by decide
    omega
  have hhigh : target ≤ 23 := by
    have hvalue : a 13 = 23 := by decide
    have hle : target ≤ a 13 := by simpa using hendpoint
    omega
  have hcases : target = 11 ∨ target = 12 ∨ target = 13 ∨ target = 14 ∨
      target = 15 ∨ target = 16 ∨ target = 17 ∨ target = 18 ∨
      target = 19 ∨ target = 20 ∨ target = 21 ∨ target = 22 ∨
      target = 23 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨10, by decide⟩ missing
  · exact absurd ⟨8, by decide⟩ missing
  · exact absurd ⟨6, by decide⟩ missing
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ missing
  · rfl
  · exact absurd ⟨7, by decide⟩ missing
  · exact absurd ⟨9, by decide⟩ missing
  · exact absurd ⟨11, by decide⟩ missing
  · exact absurd ⟨13, by decide⟩ missing

/-- Clock thirteen subtracts in the actual orbit
(`a 14 = 9 ≠ 23 + 14`). -/
theorem crossingTime_ne_thirteen
    (core : TailFixedPointCore target parent crossingTime) :
    crossingTime ≠ 13 := by
  intro heq
  have hforced := core.forced
  rw [heq] at hforced
  exact absurd hforced (by decide)

/-- Clock fourteen is a genuine forced addition (`a 15 = 24 = 9 + 15`)
straddling exactly the targets `10..24`.  All of them except nineteen
occur in the orbit by time 31, so only nineteen survives. -/
theorem target_eq_nineteen_of_crossingTime_fourteen
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (heq : crossingTime = 14) : target = 19 := by
  have hbelow := core.below
  have hendpoint := core.endpoint_ge
  rw [heq] at hbelow hendpoint
  have hlow : 9 < target := by
    have hvalue : a 14 = 9 := by decide
    omega
  have hhigh : target ≤ 24 := by
    have hvalue : a 15 = 24 := by decide
    have hle : target ≤ a 15 := by simpa using hendpoint
    omega
  have hcases : target = 10 ∨ target = 11 ∨ target = 12 ∨ target = 13 ∨
      target = 14 ∨ target = 15 ∨ target = 16 ∨ target = 17 ∨
      target = 18 ∨ target = 19 ∨ target = 20 ∨ target = 21 ∨
      target = 22 ∨ target = 23 ∨ target = 24 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨12, by decide⟩ missing
  · exact absurd ⟨10, by decide⟩ missing
  · exact absurd ⟨8, by decide⟩ missing
  · exact absurd ⟨6, by decide⟩ missing
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ missing
  · rfl
  · exact absurd ⟨7, by decide⟩ missing
  · exact absurd ⟨9, by decide⟩ missing
  · exact absurd ⟨11, by decide⟩ missing
  · exact absurd ⟨13, by decide⟩ missing
  · exact absurd ⟨15, by decide⟩ missing

/-- Clock fifteen subtracts in the actual orbit
(`a 16 = 8 ≠ 24 + 16`). -/
theorem crossingTime_ne_fifteen
    (core : TailFixedPointCore target parent crossingTime) :
    crossingTime ≠ 15 := by
  intro heq
  have hforced := core.forced
  rw [heq] at hforced
  exact absurd hforced (by decide)

/-- Clock sixteen is a genuine forced addition (`a 17 = 25 = 8 + 17`)
straddling exactly the targets `9..25`.  All of them except nineteen
occur in the orbit by time 31, so only nineteen survives. -/
theorem target_eq_nineteen_of_crossingTime_sixteen
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target)
    (heq : crossingTime = 16) : target = 19 := by
  have hbelow := core.below
  have hendpoint := core.endpoint_ge
  rw [heq] at hbelow hendpoint
  have hlow : 8 < target := by
    have hvalue : a 16 = 8 := by decide
    omega
  have hhigh : target ≤ 25 := by
    have hvalue : a 17 = 25 := by decide
    have hle : target ≤ a 17 := by simpa using hendpoint
    omega
  have hcases : target = 9 ∨ target = 10 ∨ target = 11 ∨ target = 12 ∨
      target = 13 ∨ target = 14 ∨ target = 15 ∨ target = 16 ∨
      target = 17 ∨ target = 18 ∨ target = 19 ∨ target = 20 ∨
      target = 21 ∨ target = 22 ∨ target = 23 ∨ target = 24 ∨
      target = 25 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨14, by decide⟩ missing
  · exact absurd ⟨12, by decide⟩ missing
  · exact absurd ⟨10, by decide⟩ missing
  · exact absurd ⟨8, by decide⟩ missing
  · exact absurd ⟨6, by decide⟩ missing
  · exact absurd ⟨31, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨29, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨27, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨25, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨23, by set_option maxRecDepth 100000 in decide⟩ missing
  · rfl
  · exact absurd ⟨7, by decide⟩ missing
  · exact absurd ⟨9, by decide⟩ missing
  · exact absurd ⟨11, by decide⟩ missing
  · exact absurd ⟨13, by decide⟩ missing
  · exact absurd ⟨15, by decide⟩ missing
  · exact absurd ⟨17, by decide⟩ missing

/-- Clock seventeen is a genuine forced addition straddling exactly the
targets `26..43`, but every one of them occurs in the orbit by time
111, so it is eliminated unconditionally. -/
theorem crossingTime_ne_seventeen
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target) :
    crossingTime ≠ 17 := by
  intro heq
  have hbelow := core.below
  have hendpoint := core.endpoint_ge
  rw [heq] at hbelow hendpoint
  have hlow : 25 < target := by
    have hvalue : a 17 = 25 := by decide
    omega
  have hhigh : target ≤ 43 := by
    have hvalue : a 18 = 43 := by set_option maxRecDepth 100000 in decide
    have hle : target ≤ a 18 := by simpa using hendpoint
    omega
  have hcases : target = 26 ∨ target = 27 ∨ target = 28 ∨ target = 29 ∨
      target = 30 ∨ target = 31 ∨ target = 32 ∨ target = 33 ∨
      target = 34 ∨ target = 35 ∨ target = 36 ∨ target = 37 ∨
      target = 38 ∨ target = 39 ∨ target = 40 ∨ target = 41 ∨
      target = 42 ∨ target = 43 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨64, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨62, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨60, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨58, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨56, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨54, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨52, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨50, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨48, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨46, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨44, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨42, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨40, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨38, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨111, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨22, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨20, by set_option maxRecDepth 100000 in decide⟩ missing
  · exact absurd ⟨18, by set_option maxRecDepth 100000 in decide⟩ missing

/-- Below clock eighteen, only the exceptional target nineteen survives
the unified core: odd clocks subtract, even clocks and clock seventeen
die by band elimination. -/
theorem eighteen_le_crossingTime_or_target_eq_nineteen
    (core : TailFixedPointCore target parent crossingTime)
    (missing : ¬ ∃ time, a time = target) :
    18 ≤ crossingTime ∨ target = 19 := by
  have hsix := core.six_le_crossingTime missing
  by_cases hbig : 18 ≤ crossingTime
  · exact Or.inl hbig
  · have hcases : crossingTime = 6 ∨ crossingTime = 7 ∨
        crossingTime = 8 ∨ crossingTime = 9 ∨ crossingTime = 10 ∨
        crossingTime = 11 ∨ crossingTime = 12 ∨ crossingTime = 13 ∨
        crossingTime = 14 ∨ crossingTime = 15 ∨ crossingTime = 16 ∨
        crossingTime = 17 := by omega
    rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq |
      heq | heq | heq | heq
    · exact Or.inr
        (core.target_eq_nineteen_of_crossingTime_six missing heq)
    · exact absurd heq core.crossingTime_ne_seven
    · exact Or.inr
        (core.target_eq_nineteen_of_crossingTime_eight missing heq)
    · exact absurd heq core.crossingTime_ne_nine
    · exact Or.inr
        (core.target_eq_nineteen_of_crossingTime_ten missing heq)
    · exact absurd heq core.crossingTime_ne_eleven
    · exact Or.inr
        (core.target_eq_nineteen_of_crossingTime_twelve missing heq)
    · exact absurd heq core.crossingTime_ne_thirteen
    · exact Or.inr
        (core.target_eq_nineteen_of_crossingTime_fourteen missing heq)
    · exact absurd heq core.crossingTime_ne_fifteen
    · exact Or.inr
        (core.target_eq_nineteen_of_crossingTime_sixteen missing heq)
    · exact absurd heq (core.crossingTime_ne_seventeen missing)

end TailFixedPointCore

end

end Recaman
