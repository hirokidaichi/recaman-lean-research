import Recaman.PinnedForwardOrbit
import Recaman.PermanentAboveCorridorReplayFloorFour

namespace Recaman

noncomputable section

/-! # Backward determination of the pinned configuration

`pinned_forward_orbit` determines three steps past the tail minimum.  This
module is its mirror image: it determines the two steps *before* the pinned
predecessor clock.

The pinned configuration stores `a clock = target + 1` as a first occurrence.
The transition into that clock is therefore either a legal subtraction, which
pins `a (clock - 1) = target + clock + 1`, or a forced addition, which pins
`a (clock - 1) + clock = target + 1`.  Repeating the split one step earlier
determines `a (clock - 2)` in all four combinations:

| step `clock` | step `clock - 1` | `a (clock - 1)` | `a (clock - 2)` |
|---|---|---|---|
| subtract | subtract | `target + clock + 1` | `target + 2 * clock` |
| subtract | add      | `target + clock + 1` | `target + 2` |
| add      | subtract | `target + 1 - clock` | `target` |
| add      | add      | `target + 1 - clock` | `target + 2 - 2 * clock` |

The third row is impossible: it places the missing target on the orbit two
steps before the clock.  So a pinned configuration can never enter its clock
by a forced addition out of a legal subtraction, and only three backward
shapes survive.

A numeric scan of the clocks satisfying the four decidable fields of the
configuration over `clock < 60000` finds 310 of them, split exactly as the
table predicts: 189 in the eliminated row, 88 in the `target + 2` row, 21 in
the last row and 12 in the first.  So the elimination below removes the
largest of the four backward shapes.

The `target + 2` row carries a further consequence recorded at the end: the
tail minimum value of the pinned configuration is itself `target + 2`, and in
that row the value already occurs at `clock - 2`, so late recurrence forbids
it at every later time exceeding it.
-/

namespace PinnedTailMinimumConfiguration

variable {target clock : Nat}

/-- The pinned clock is at least two, so both backward steps exist.  A clock
of one would need its target below one and above four at the same time. -/
theorem two_le_clock (h : PinnedTailMinimumConfiguration target clock) :
    2 ≤ clock := by
  have hpos := h.clock_pos
  have hbound := h.clock_bound
  have htri := h.upperTri_bound
  by_cases hone : clock = 1
  · subst hone
    have hone' : upperTri 1 = 1 := by decide
    omega
  · omega

/-- Backward transition into the pinned clock.  Either the step subtracts,
and the previous value is the pinned value raised by the clock, or it adds,
and the previous value is the pinned value lowered by the clock. -/
theorem backward_one_step {target h : Nat}
    (hp : PinnedTailMinimumConfiguration target (h + 2)) :
    a (h + 1) = target + h + 3 ∨ a (h + 1) + h + 2 = target + 1 := by
  have hvalue : a (h + 2) = target + 1 := hp.value_eq
  by_cases hsub : CanSubtract (h + 1 + 1) (stateAt (h + 1))
  · left
    have hstep : a (h + 1 + 1) = a (h + 1) - (h + 1 + 1) :=
      a_succ_of_canSubtract hsub
    have hpos : h + 1 + 1 < a (h + 1) := hsub.1
    have hstep' : a (h + 2) = a (h + 1) - (h + 2) := by simpa using hstep
    omega
  · right
    have hstep : a (h + 1 + 1) = a (h + 1) + (h + 1 + 1) :=
      a_succ_of_not_canSubtract hsub
    have hstep' : a (h + 2) = a (h + 1) + (h + 2) := by simpa using hstep
    omega

/-- Two backward steps.  All four combinations are determined exactly. -/
theorem backward_two_steps {target h : Nat}
    (hp : PinnedTailMinimumConfiguration target (h + 2)) :
    (a (h + 1) = target + h + 3 ∧ a h = target + 2 * h + 4) ∨
    (a (h + 1) = target + h + 3 ∧ a h = target + 2) ∨
    (a (h + 1) + h + 2 = target + 1 ∧ a h = target) ∨
    (a (h + 1) + h + 2 = target + 1 ∧ a h + 2 * h + 2 = target) := by
  have houter := hp.backward_one_step
  have hclock := hp.clock_bound
  by_cases hsub : CanSubtract (h + 1) (stateAt h)
  · have hstep : a (h + 1) = a h - (h + 1) := a_succ_of_canSubtract hsub
    have hpos : h + 1 < a h := hsub.1
    rcases houter with hup | hdown
    · exact Or.inl ⟨hup, by omega⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hdown, by omega⟩))
  · have hstep : a (h + 1) = a h + (h + 1) :=
      a_succ_of_not_canSubtract hsub
    rcases houter with hup | hdown
    · exact Or.inr (Or.inl ⟨hup, by omega⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hdown, by omega⟩))

/-- The eliminated row.  A forced addition into the clock out of a legal
subtraction one step earlier would place the missing target at `clock - 2`. -/
theorem not_add_then_subtract {target h : Nat}
    (hp : PinnedTailMinimumConfiguration target (h + 2))
    (hadd : ¬ CanSubtract (h + 1 + 1) (stateAt (h + 1)))
    (hsub : CanSubtract (h + 1) (stateAt h)) : False := by
  have hvalue : a (h + 2) = target + 1 := hp.value_eq
  have hstepOuter : a (h + 1 + 1) = a (h + 1) + (h + 1 + 1) :=
    a_succ_of_not_canSubtract hadd
  have hstepOuter' : a (h + 2) = a (h + 1) + (h + 2) := by
    simpa using hstepOuter
  have hstepInner : a (h + 1) = a h - (h + 1) := a_succ_of_canSubtract hsub
  have hpos : h + 1 < a h := hsub.1
  exact hp.target_missing ⟨h, by omega⟩

/-- Backward trichotomy: after the elimination only three shapes survive. -/
theorem backward_trichotomy {target h : Nat}
    (hp : PinnedTailMinimumConfiguration target (h + 2)) :
    (a (h + 1) = target + h + 3 ∧ a h = target + 2 * h + 4) ∨
    (a (h + 1) = target + h + 3 ∧ a h = target + 2) ∨
    (a (h + 1) + h + 2 = target + 1 ∧ a h + 2 * h + 2 = target) := by
  rcases hp.backward_two_steps with hone | htwo | hthree | hfour
  · exact Or.inl hone
  · exact Or.inr (Or.inl htwo)
  · exact False.elim (hp.target_missing ⟨h, hthree.2⟩)
  · exact Or.inr (Or.inr hfour)

/-- The value two steps before the clock is never the missing target, and the
three surviving shapes place it either far above, exactly two above, or a
computed distance below. -/
theorem backward_value_ne_target {target h : Nat}
    (hp : PinnedTailMinimumConfiguration target (h + 2)) :
    a h ≠ target := by
  intro heq
  exact hp.target_missing ⟨h, heq⟩

/-- General form at an unrestricted clock: the two backward steps exist and
are determined.  `two_le_clock` supplies the decomposition. -/
theorem backward_trichotomy_general
    (h : PinnedTailMinimumConfiguration target clock) :
    ∃ base, clock = base + 2 ∧
      ((a (base + 1) = target + base + 3 ∧
          a base = target + 2 * base + 4) ∨
        (a (base + 1) = target + base + 3 ∧ a base = target + 2) ∨
        (a (base + 1) + base + 2 = target + 1 ∧
          a base + 2 * base + 2 = target)) := by
  have htwo := h.two_le_clock
  refine ⟨clock - 2, by omega, ?_⟩
  have hrewrite : clock - 2 + 2 = clock := by omega
  have h' : PinnedTailMinimumConfiguration target (clock - 2 + 2) := by
    rw [hrewrite]
    exact h
  exact h'.backward_trichotomy

/-! ## Consequence for the middle row -/

/-- In the middle row the value `target + 2` already occurs two steps before
the clock.  Since the pinned tail minimum value is exactly `target + 2`, late
recurrence forbids that minimum at every time which exceeds both the clock
and the value.  This is the hook for eliminating the middle row from the
replay side, where the tail minimum time is known to exceed the target. -/
theorem middle_row_forbids_late_minimum {target h m : Nat}
    (_hp : PinnedTailMinimumConfiguration target (h + 2))
    (hcase : a h = target + 2)
    (hlate : h < m) (hbig : target + 2 < m) :
    a m ≠ target + 2 := by
  intro hm
  exact value_no_late_recurrence (v := target + 2) (w := h) (m := m)
    hcase hlate hbig hm

/-- Sharper form of the same hook.  The replay side already knows that the
tail minimum time exceeds the target and that the minimum value is
`target + 2`.  In the middle row those facts leave only two possible minimum
times, so the row survives only inside a two-point window. -/
theorem middle_row_pins_minimum_time {target h m : Nat}
    (hp : PinnedTailMinimumConfiguration target (h + 2))
    (hcase : a h = target + 2)
    (hlate : h < m) (habove : target < m) (hminimum : a m = target + 2) :
    m = target + 1 ∨ m = target + 2 := by
  by_cases hbig : target + 2 < m
  · exact False.elim
      (hp.middle_row_forbids_late_minimum hcase hlate hbig hminimum)
  · omega

end PinnedTailMinimumConfiguration

end

end Recaman
