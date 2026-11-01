import Recaman.PreTailBudgetSeparation

namespace Recaman

noncomputable section

/-! # The pinned tail-minimum configuration

The counting separation left exactly one way for `target + 2 < a m` to fail:
the tail minimum sits two above the target, the follow-up branch is forced to
be the double subtraction, and the three orbit values around the minimum
predecessor are fixed by the target and the predecessor clock alone.  This
module isolates that configuration as a structure of its own and works out
what it forces.

Two things come out of it.

First, the tail minimum is a genuine first occurrence there.  The step into
the tail minimum is either a subtraction, which lands fresh, or a forced
addition, which needs `a (m - 1) + m = a m`.  The addition also forces the
minimum to be reached exactly at the tail start, and in the pinned
configuration the counting bound `target < tailStart` squeezes `a (m - 1)`
down to at most one, which only times zero and one can supply.  So the
addition case dies and `FirstAt a (a m) m` holds.  With that the orbit is
determined for three further steps past the minimum.

Second, the configuration is not eliminable by clock enumeration.  The target
is determined by the predecessor clock through `target = a f - 1`, so a single
occurrence of `a f - 1` kills a given clock, and `elim_of_predecessor_witness`
is exactly that hook.  But the clock window is `2 * f + 2 < target` together
with `target + 1 ≤ upperTri f`, a window whose width grows with the target
rather than closing.  A search over the real orbit confirms the shape: clocks
carrying a first occurrence, two consecutive legal subtractions, the clock
bound and the current target floor keep accumulating without end, twenty-five
below a thousand, four hundred and twenty-three below a hundred thousand, two
thousand four hundred and thirty-eight below three million.  Their density
thins but their count keeps growing, so enumeration faces the same unbounded
treadmill as the floor-raising route, and the pinned configuration has to fall
to a structural argument instead.
-/

/-- The one configuration in which the tail minimum fails to clear the target
by three.  Stated purely in terms of the target and the predecessor clock, so
that it can be attacked without the surrounding certificate. -/
structure PinnedTailMinimumConfiguration (target clock : Nat) : Prop where
  predecessor_first : FirstAt a (target + 1) clock
  subtract_one : CanSubtract (clock + 1) (stateAt clock)
  subtract_two : CanSubtract (clock + 2) (stateAt (clock + 1))
  clock_bound : 2 * clock + 2 < target
  target_missing : ¬ ∃ time, a time = target

namespace PinnedTailMinimumConfiguration

variable {target clock : Nat}

/-- The predecessor value at the pinned clock. -/
theorem value_eq (h : PinnedTailMinimumConfiguration target clock) :
    a clock = target + 1 := h.predecessor_first.1

/-- The target is determined by the clock, so a concrete clock determines a
concrete missing value. -/
theorem target_eq (h : PinnedTailMinimumConfiguration target clock) :
    target = a clock - 1 := by
  have hv := h.value_eq
  omega

/-- The pinned configuration is a double subtraction. -/
theorem toDoubleSubtractStep (h : PinnedTailMinimumConfiguration target clock) :
    DoubleSubtractStep (a clock) clock :=
  ⟨by rw [h.value_eq]; exact h.predecessor_first, h.subtract_one,
    h.subtract_two⟩

/-- First landing of the pinned double subtraction. -/
theorem first_landing (h : PinnedTailMinimumConfiguration target clock) :
    a (clock + 1) = target - clock := by
  have hstep := h.toDoubleSubtractStep.first_value
  have hv := h.value_eq
  omega

/-- Second landing of the pinned double subtraction. -/
theorem second_landing (h : PinnedTailMinimumConfiguration target clock) :
    a (clock + 2) = target - 2 * clock - 2 := by
  have hstep := h.toDoubleSubtractStep.second_value
  have hv := h.value_eq
  omega

/-- The clock is positive. -/
theorem clock_pos (h : PinnedTailMinimumConfiguration target clock) :
    0 < clock := h.toDoubleSubtractStep.time_pos

/-- Upper triangular bound at the pinned clock: the clock cannot be too
small for the target it carries. -/
theorem upperTri_bound (h : PinnedTailMinimumConfiguration target clock) :
    target + 1 ≤ upperTri clock := by
  have hv := h.value_eq
  have hbound := a_le_upperTri clock
  omega

/-- The full clock window.  Its lower end grows like the square root of the
target and its upper end like half the target, so the window widens with the
target instead of closing. -/
theorem clock_window (h : PinnedTailMinimumConfiguration target clock) :
    2 * clock + 2 < target ∧ target + 1 ≤ upperTri clock :=
  ⟨h.clock_bound, h.upperTri_bound⟩

/-- Elimination hook for a concrete clock: any occurrence of the value one
below the pinned predecessor value refutes the configuration. -/
theorem elim_of_predecessor_witness
    (h : PinnedTailMinimumConfiguration target clock)
    (witness : Nat) (hwitness : a witness + 1 = a clock) : False := by
  have hv := h.value_eq
  exact h.target_missing ⟨witness, by omega⟩

end PinnedTailMinimumConfiguration

/-- The value one never recurs after time one. -/
theorem one_no_late_occurrence (time : Nat) (htime : 1 < time) :
    a time ≠ 1 := by
  have hone : a 1 = 1 := rfl
  have hmem : (1 : Nat) ∈ valuesThrough 1 :=
    mem_valuesThrough_iff.mpr ⟨1, Nat.le_refl _, hone⟩
  have hseen : (1 : Nat) ∈ valuesThrough (time - 1) :=
    valuesThrough_mono (by omega) hmem
  have hne := a_succ_ne_of_seen hseen (show (1 : Nat) < time - 1 + 1 by omega)
  intro heq
  apply hne
  have hsucc : time - 1 + 1 = time := by omega
  rw [hsucc]
  exact heq

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The tail minimum time exceeds four: it is past the tail start, which is
past the target, which is past the predecessor clock plus two. -/
theorem five_le_minimumTime
    (r : TerminalExactDischargeReplayCertificate source) :
    5 ≤ source.historicalMinimumTime := by
  have hpos := r.firstTime_pos
  have hclock := r.minimum_predecessor_clock_below_target
  have hpre := r.target_lt_tailStart
  have hle := source.historical_minimum.minimum.start_le_time
  omega

/-- Unconditional transition dichotomy at the tail minimum: the step into it
either subtracts, landing fresh, or is a forced addition which also pins the
minimum to the tail start. -/
theorem tailMinimum_transition
    (r : TerminalExactDischargeReplayCertificate source) :
    (a (source.historicalMinimumTime - 1) =
        a source.historicalMinimumTime + source.historicalMinimumTime ∧
      FirstAt a (a source.historicalMinimumTime)
        source.historicalMinimumTime) ∨
    (source.historicalMinimumTime = source.tailStart ∧
      a (source.historicalMinimumTime - 1) +
        source.historicalMinimumTime =
          a source.historicalMinimumTime) := by
  have h5 := r.five_le_minimumTime
  obtain ⟨k, hk⟩ : ∃ k, source.historicalMinimumTime = k + 1 :=
    ⟨source.historicalMinimumTime - 1, by omega⟩
  have hkeq : source.historicalMinimumTime - 1 = k := by omega
  have hk1 : k + 1 = source.historicalMinimumTime := hk.symm
  rw [hkeq]
  by_cases hcan : CanSubtract (k + 1) (stateAt k)
  · left
    have hsub := a_succ_of_canSubtract hcan
    have hfresh := firstAt_succ_of_canSubtract hcan
    have hposv : k + 1 < (stateAt k).value := hcan.1
    have hposv' : (stateAt k).value = a k := rfl
    rw [hk1] at hsub hfresh hposv
    exact ⟨by omega, hfresh⟩
  · right
    have hadd := a_succ_of_not_canSubtract hcan
    rw [hk1] at hadd
    have hle := source.historical_minimum.minimum.start_le_time
    have heqStart : source.historicalMinimumTime = source.tailStart := by
      by_cases hlt : source.tailStart < source.historicalMinimumTime
      · exfalso
        have hlate : source.tailStart ≤ k := by omega
        have hmin := source.historical_minimum.minimum.minimal k hlate
        omega
      · omega
    exact ⟨heqStart, by omega⟩

/-- Whenever the tail minimum value does not exceed its own time by more than
one, the forced-addition branch is impossible and the tail minimum is a first
occurrence. -/
theorem tailMinimum_firstAt_of_small_value
    (r : TerminalExactDischargeReplayCertificate source)
    (hsmall : a source.historicalMinimumTime ≤
      source.historicalMinimumTime + 1) :
    a (source.historicalMinimumTime - 1) =
        a source.historicalMinimumTime + source.historicalMinimumTime ∧
      FirstAt a (a source.historicalMinimumTime)
        source.historicalMinimumTime := by
  have h5 := r.five_le_minimumTime
  rcases r.tailMinimum_transition with hgood | ⟨_, hadd⟩
  · exact hgood
  · exfalso
    have hposv := a_pos_of_pos_time
      (n := source.historicalMinimumTime - 1) (by omega)
    have hone := one_no_late_occurrence
      (source.historicalMinimumTime - 1) (by omega)
    omega

/-- Unconditional form: either the tail minimum is a first occurrence, or it
exceeds its own time by more than one and the blocked step at the minimum
supplies an occurrence of `a m - (m + 1)`.  The second branch is the exact
residue left by the transition analysis. -/
theorem tailMinimum_firstAt_or_blockedWitness
    (r : TerminalExactDischargeReplayCertificate source) :
    FirstAt a (a source.historicalMinimumTime)
        source.historicalMinimumTime ∨
      (source.historicalMinimumTime + 1 < a source.historicalMinimumTime ∧
        ∃ time, a time = a source.historicalMinimumTime -
          (source.historicalMinimumTime + 1)) := by
  by_cases hsmall : a source.historicalMinimumTime ≤
      source.historicalMinimumTime + 1
  · exact Or.inl (r.tailMinimum_firstAt_of_small_value hsmall).2
  · right
    refine ⟨by omega, ?_⟩
    rcases not_canSubtract_cases source.historical_minimum.first_forced with
      hle | hseen
    · exact False.elim (hsmall hle)
    · rcases mem_valuesThrough_iff.mp hseen with ⟨t, _, hval⟩
      exact ⟨t, hval⟩

/-- In the pinned configuration the counting bound squeezes the tail minimum
below its own time, so the tail minimum is a first occurrence and the step
into it is a subtraction. -/
theorem pinned_tailMinimum_firstAt
    (r : TerminalExactDischargeReplayCertificate source)
    (hpin : a source.historicalMinimumTime = target + 2) :
    a (source.historicalMinimumTime - 1) =
        a source.historicalMinimumTime + source.historicalMinimumTime ∧
      FirstAt a (a source.historicalMinimumTime)
        source.historicalMinimumTime := by
  have hpre := r.target_lt_tailStart
  have hle := source.historical_minimum.minimum.start_le_time
  exact r.tailMinimum_firstAt_of_small_value (by omega)

/-- In the pinned configuration the orbit is determined for three steps past
the tail minimum: two forced additions from the certificate, then a third
whose subtraction candidate is exactly the value the orbit held one step
before the minimum. -/
theorem pinned_forward_orbit
    (r : TerminalExactDischargeReplayCertificate source)
    (hpin : a source.historicalMinimumTime = target + 2) :
    a (source.historicalMinimumTime + 1) =
        target + source.historicalMinimumTime + 3 ∧
      a (source.historicalMinimumTime + 2) =
        target + 2 * source.historicalMinimumTime + 5 ∧
      a (source.historicalMinimumTime + 3) =
        target + 3 * source.historicalMinimumTime + 8 := by
  have h5 := r.five_le_minimumTime
  have hback := (r.pinned_tailMinimum_firstAt hpin).1
  have h1 := source.historical_minimum.first_addition
  have hforced := source.historical_minimum.followup_forced
  have h2 : a (source.historicalMinimumTime + 2) =
      a (source.historicalMinimumTime + 1) +
        (source.historicalMinimumTime + 2) := by
    have hstep := a_succ_of_not_canSubtract
      (n := source.historicalMinimumTime + 1) hforced
    simpa using hstep
  have hmem : a (source.historicalMinimumTime - 1) ∈
      valuesThrough (source.historicalMinimumTime + 2) :=
    mem_valuesThrough_iff.mpr
      ⟨source.historicalMinimumTime - 1, by omega, rfl⟩
  have hcand : a (source.historicalMinimumTime + 2) -
      (source.historicalMinimumTime + 2 + 1) =
      a (source.historicalMinimumTime - 1) := by omega
  have hblock : ¬ CanSubtract (source.historicalMinimumTime + 2 + 1)
      (stateAt (source.historicalMinimumTime + 2)) := by
    intro hcan
    apply hcan.2
    have hv : (stateAt (source.historicalMinimumTime + 2)).value =
        a (source.historicalMinimumTime + 2) := rfl
    have hs : (stateAt (source.historicalMinimumTime + 2)).seen =
        valuesThrough (source.historicalMinimumTime + 2) := rfl
    rw [hs, hv, hcand]
    exact hmem
  have h3 : a (source.historicalMinimumTime + 3) =
      a (source.historicalMinimumTime + 2) +
        (source.historicalMinimumTime + 3) := by
    have hstep := a_succ_of_not_canSubtract hblock
    simpa using hstep
  exact ⟨by omega, by omega, by omega⟩

/-- Refined form of the counting separation: either the tail minimum clears
the target by three, or the pinned configuration holds at the minimum
predecessor clock, with the tail minimum exactly two above the target. -/
theorem tailMinimum_gap_or_pinnedConfiguration
    (r : TerminalExactDischargeReplayCertificate source)
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    target + 2 < a source.historicalMinimumTime ∨
      (PinnedTailMinimumConfiguration target source.historicalFirstTime ∧
        a source.historicalMinimumTime = target + 2) := by
  by_cases hgap : target + 2 < a source.historicalMinimumTime
  · exact Or.inl hgap
  · right
    have hthree := r.tailMinimum_ge_three
    have htgt := source.historical_minimum.target_lt_predecessor
    have hp1 : a source.historicalFirstTime =
        a source.historicalMinimumTime - 1 :=
      source.historical_minimum.predecessor_first.1
    have hpin : a source.historicalMinimumTime = target + 2 := by omega
    refine ⟨?_, hpin⟩
    rcases r.minimum_predecessor_followUp_refined hvalue horder with
      ⟨_, hsep⟩ | ⟨hd, _, _, _⟩
    · exact False.elim (hgap hsep)
    · have hvf : a source.historicalFirstTime = target + 1 := by omega
      have hclock := hd.clock_bound
      refine ⟨?_, hd.subtract_one, hd.subtract_two, by omega,
        source.historical_tail.target_missing⟩
      have hfirst := hd.first
      rw [hvf] at hfirst
      exact hfirst

/-- Consequently every replay either clears the target by three at the tail
minimum, or supplies a concrete clock whose predecessor value is one above a
value the orbit never reaches. -/
theorem tailMinimum_gap_or_missing_predecessor
    (r : TerminalExactDischargeReplayCertificate source)
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    target + 2 < a source.historicalMinimumTime ∨
      ¬ ∃ time, a time + 1 = a source.historicalFirstTime := by
  rcases r.tailMinimum_gap_or_pinnedConfiguration hvalue horder with
    hgap | ⟨hpin, _⟩
  · exact Or.inl hgap
  · right
    intro hex
    rcases hex with ⟨witness, hwitness⟩
    exact hpin.elim_of_predecessor_witness witness hwitness

end TerminalExactDischargeReplayCertificate

end

end Recaman
