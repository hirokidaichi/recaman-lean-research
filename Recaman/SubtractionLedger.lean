import Recaman.CoordinateDynamics
import Recaman.OrbitBounds
import Recaman.PinnedAdjacentWitness

namespace Recaman

/-! # The subtraction ledger

Every Recamán step either adds or subtracts its clock.  Recording the total
clock mass spent on subtraction steps yields an exact conservation law: the
value plus twice the subtraction ledger always equals the triangular total
`upperTri t` of all clocks.  This single identity forces a mod-4 parity
pattern on occurrence times, a backward propagation inequality tying late
heights to early heights, and two-sided bounds on the number of subtraction
steps.  None of this information was previously available on the certificate
interface. -/

/-- Total of the clocks at which the orbit performed a subtraction step,
up to and including time `t`. -/
def subSum : Nat → Nat
  | 0 => 0
  | t + 1 => subSum t + (if CanSubtract (t + 1) (stateAt t) then t + 1 else 0)

/-- Number of subtraction steps performed up to and including time `t`. -/
def subCount : Nat → Nat
  | 0 => 0
  | t + 1 => subCount t + (if CanSubtract (t + 1) (stateAt t) then 1 else 0)

@[simp] theorem subSum_zero : subSum 0 = 0 := rfl

@[simp] theorem subCount_zero : subCount 0 = 0 := rfl

theorem subSum_succ (t : Nat) :
    subSum (t + 1) =
      subSum t + (if CanSubtract (t + 1) (stateAt t) then t + 1 else 0) := rfl

theorem subCount_succ (t : Nat) :
    subCount (t + 1) =
      subCount t + (if CanSubtract (t + 1) (stateAt t) then 1 else 0) := rfl

/-- One unfolding of the triangular total. -/
theorem upperTri_succ (t : Nat) :
    upperTri (t + 1) = upperTri t + t + 1 := rfl

/-- The ledger identity: the current value plus twice the subtraction ledger
is exactly the triangular sum of all clocks used so far.  An addition step
moves the whole clock into the value, a subtraction step moves it out of the
value and books it twice in the ledger. -/
theorem ledger_identity : ∀ t, a t + 2 * subSum t = upperTri t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      by_cases hcan : CanSubtract (t + 1) (stateAt t)
      · have hval := a_succ_of_canSubtract hcan
        have hlt : t + 1 < a t := hcan.1
        have hsum : subSum (t + 1) = subSum t + (t + 1) := by
          rw [subSum_succ, if_pos hcan]
        have htri := upperTri_succ t
        omega
      · have hval := a_succ_of_not_canSubtract hcan
        have hsum : subSum (t + 1) = subSum t := by
          rw [subSum_succ, if_neg hcan]
          omega
        have htri := upperTri_succ t
        omega

/-- The value and the triangular total always have the same parity. -/
theorem parity_invariant : ∀ t, (a t + upperTri t) % 2 = 0 := by
  intro t
  have h := ledger_identity t
  omega

/-- Any occurrence of a value `v` must happen at a time whose triangular
total matches the parity of `v`. -/
theorem occurrence_parity {v t : Nat} (h : a t = v) :
    (v + upperTri t) % 2 = 0 := by
  rw [← h]
  exact parity_invariant t

/-- Crossing one block of four clocks adds an even amount plus `4t + 10`
to the triangular total. -/
theorem upperTri_add_four (t : Nat) :
    upperTri (t + 4) = upperTri t + (4 * t + 10) := by
  have h1 : upperTri (t + 1) = upperTri t + t + 1 := upperTri_succ t
  have h2 : upperTri (t + 2) = upperTri (t + 1) + (t + 1) + 1 :=
    upperTri_succ (t + 1)
  have h3 : upperTri (t + 3) = upperTri (t + 2) + (t + 2) + 1 :=
    upperTri_succ (t + 2)
  have h4 : upperTri (t + 4) = upperTri (t + 3) + (t + 3) + 1 :=
    upperTri_succ (t + 3)
  omega

/-- The parity of the triangular total is invariant under shifting the index
by any multiple of four. -/
theorem upperTri_add_four_mul (t k : Nat) :
    upperTri (t + 4 * k) % 2 = upperTri t % 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have harg : t + 4 * (k + 1) = t + 4 * k + 4 := by omega
      rw [harg, upperTri_add_four]
      omega

/-- The parity of the triangular total only depends on the index mod 4:
the pattern is even, odd, odd, even. -/
theorem upperTri_mod_two_eq (t : Nat) :
    upperTri t % 2 = upperTri (t % 4) % 2 := by
  have hdecomp : t % 4 + 4 * (t / 4) = t := by omega
  calc upperTri t % 2
      = upperTri (t % 4 + 4 * (t / 4)) % 2 := by rw [hdecomp]
    _ = upperTri (t % 4) % 2 := upperTri_add_four_mul (t % 4) (t / 4)

/-- An even value can only occur at times congruent to 0 or 3 mod 4. -/
theorem even_value_time_mod_four {v t : Nat}
    (hv : v % 2 = 0) (h : a t = v) :
    t % 4 = 0 ∨ t % 4 = 3 := by
  have hpar := occurrence_parity h
  have hU : upperTri t % 2 = 0 := by omega
  have hmod := upperTri_mod_two_eq t
  have hcases : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · rw [h1] at hmod
    have hone : upperTri 1 = 1 := rfl
    omega
  · rw [h2] at hmod
    have htwo : upperTri 2 = 3 := upperTri_two
    omega
  · exact Or.inr h3

/-- An odd value can only occur at times congruent to 1 or 2 mod 4. -/
theorem odd_value_time_mod_four {v t : Nat}
    (hv : v % 2 = 1) (h : a t = v) :
    t % 4 = 1 ∨ t % 4 = 2 := by
  have hpar := occurrence_parity h
  have hU : upperTri t % 2 = 1 := by omega
  have hmod := upperTri_mod_two_eq t
  have hcases : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · rw [h0] at hmod
    have hzero : upperTri 0 = 0 := rfl
    omega
  · exact Or.inl h1
  · exact Or.inr h2
  · rw [h3] at hmod
    have hthree : upperTri 3 = 6 := upperTri_three
    omega

/-- The subtraction ledger never decreases in one step. -/
theorem subSum_le_succ (t : Nat) : subSum t ≤ subSum (t + 1) := by
  rw [subSum_succ]
  exact Nat.le_add_right _ _

/-- The subtraction ledger is monotone in time. -/
theorem subSum_mono {w t : Nat} (hwt : w ≤ t) : subSum w ≤ subSum t := by
  induction t with
  | zero =>
      have hw : w = 0 := by omega
      subst hw
      exact Nat.le_refl _
  | succ t ih =>
      rcases Nat.eq_or_lt_of_le hwt with heq | hlt
      · subst heq
        exact Nat.le_refl _
      · exact Nat.le_trans (ih (Nat.le_of_lt_succ hlt)) (subSum_le_succ t)

/-- Backward propagation: a high value at a late time forces the whole
earlier orbit to be correspondingly high.  Written additively so that no
truncated subtraction appears. -/
theorem backward_propagation {w t : Nat} (hwt : w ≤ t) :
    a t + upperTri w ≤ a w + upperTri t := by
  have hw := ledger_identity w
  have ht := ledger_identity t
  have hmono := subSum_mono hwt
  omega

/-- The deficit `upperTri t - a t` is exactly twice the subtraction ledger. -/
theorem two_mul_subSum_eq_deficit (t : Nat) :
    2 * subSum t = upperTri t - a t := by
  have h := ledger_identity t
  omega

/-- The deficit below the triangular ceiling is monotone in time. -/
theorem deficit_mono {w t : Nat} (hwt : w ≤ t) :
    upperTri w - a w ≤ upperTri t - a t := by
  have hw := ledger_identity w
  have ht := ledger_identity t
  have hmono := subSum_mono hwt
  omega

/-- In one step the ledger either stays fixed or grows by exactly the clock. -/
theorem subSum_step_dichotomy (t : Nat) :
    subSum (t + 1) = subSum t ∨ subSum (t + 1) = subSum t + (t + 1) := by
  by_cases hcan : CanSubtract (t + 1) (stateAt t)
  · exact Or.inr (by rw [subSum_succ, if_pos hcan])
  · exact Or.inl (by rw [subSum_succ, if_neg hcan]; omega)

/-- The additive value equation of a subtraction step certifies legality of
that subtraction: an addition step would overshoot by twice the clock. -/
theorem canSubtract_of_step_eq {t : Nat}
    (h : a (t + 1) + (t + 1) = a t) :
    CanSubtract (t + 1) (stateAt t) := by
  by_cases hcan : CanSubtract (t + 1) (stateAt t)
  · exact hcan
  · exfalso
    have hadd := a_succ_of_not_canSubtract hcan
    omega

/-- The additive value equation characterizes subtraction steps exactly. -/
theorem subtraction_step_iff {t : Nat} :
    a (t + 1) + (t + 1) = a t ↔ CanSubtract (t + 1) (stateAt t) := by
  constructor
  · exact canSubtract_of_step_eq
  · intro hcan
    have hval := a_succ_of_canSubtract hcan
    have hlt : t + 1 < a t := hcan.1
    omega

/-- Every subtraction landing is fresh: whenever the value equation of a
subtraction step holds, the landing time is the first occurrence of the
landing value. -/
theorem firstAt_of_subtraction_step {t : Nat}
    (h : a (t + 1) + (t + 1) = a t) :
    FirstAt a (a (t + 1)) (t + 1) :=
  firstAt_succ_of_canSubtract (canSubtract_of_step_eq h)

/-- There are at most `t` subtraction steps up to time `t`. -/
theorem subCount_le (t : Nat) : subCount t ≤ t := by
  induction t with
  | zero => exact Nat.le_refl 0
  | succ t ih =>
      rw [subCount_succ]
      by_cases hcan : CanSubtract (t + 1) (stateAt t)
      · rw [if_pos hcan]
        omega
      · rw [if_neg hcan]
        omega

/-- Upper bound of the ledger by the count: each booked clock is at most
the current time. -/
theorem subSum_le_mul_subCount (t : Nat) :
    subSum t ≤ t * subCount t := by
  induction t with
  | zero => exact Nat.le_refl 0
  | succ t ih =>
      have hmono : t * subCount t ≤ (t + 1) * subCount t :=
        Nat.mul_le_mul_right (subCount t) (Nat.le_succ t)
      by_cases hcan : CanSubtract (t + 1) (stateAt t)
      · have hsum : subSum (t + 1) = subSum t + (t + 1) := by
          rw [subSum_succ, if_pos hcan]
        have hcount : subCount (t + 1) = subCount t + 1 := by
          rw [subCount_succ, if_pos hcan]
        have hmul : (t + 1) * (subCount t + 1) =
            (t + 1) * subCount t + (t + 1) :=
          Nat.mul_succ (t + 1) (subCount t)
        rw [hsum, hcount, hmul]
        omega
      · have hsum : subSum (t + 1) = subSum t := by
          rw [subSum_succ, if_neg hcan]
          omega
        have hcount : subCount (t + 1) = subCount t := by
          rw [subCount_succ, if_neg hcan]
          omega
        rw [hsum, hcount]
        exact Nat.le_trans ih hmono

/-- Lower bound of the ledger by the count: the booked clocks are distinct
positive integers, so `subCount t` of them total at least the triangular
number `upperTri (subCount t)`. -/
theorem upperTri_subCount_le_subSum (t : Nat) :
    upperTri (subCount t) ≤ subSum t := by
  induction t with
  | zero => exact Nat.le_refl 0
  | succ t ih =>
      by_cases hcan : CanSubtract (t + 1) (stateAt t)
      · have hsum : subSum (t + 1) = subSum t + (t + 1) := by
          rw [subSum_succ, if_pos hcan]
        have hcount : subCount (t + 1) = subCount t + 1 := by
          rw [subCount_succ, if_pos hcan]
        have htri := upperTri_succ (subCount t)
        have hle := subCount_le t
        rw [hsum, hcount, htri]
        omega
      · have hsum : subSum (t + 1) = subSum t := by
          rw [subSum_succ, if_neg hcan]
          omega
        have hcount : subCount (t + 1) = subCount t := by
          rw [subCount_succ, if_neg hcan]
          omega
        rw [hsum, hcount]
        exact ih

/-! ## The parity constraint on the pinned configuration

Two applications of the ledger to the pinned tail-minimum front.  First,
occurrences of two adjacent values must sit in complementary time classes
mod 4, because their triangular totals have opposite parities.  Second, the
pinned predecessor value `target + 1` pins the clock residue itself. -/

/-- Occurrences of two adjacent values force opposite parities on the
triangular totals of their times. -/
theorem adjacent_occurrence_opposite_parity {w b : Nat}
    (h : a w + 1 = a b) :
    (upperTri w + upperTri b) % 2 = 1 := by
  have hw := parity_invariant w
  have hb := parity_invariant b
  omega

/-- Full characterization of the triangular parity by the time class:
the triangular total is even exactly on the residues 0 and 3 mod 4. -/
theorem upperTri_even_iff (t : Nat) :
    upperTri t % 2 = 0 ↔ (t % 4 = 0 ∨ t % 4 = 3) := by
  have hmod := upperTri_mod_two_eq t
  have hcases : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · rw [h0] at hmod
    have hzero : upperTri 0 = 0 := rfl
    omega
  · rw [h1] at hmod
    have hone : upperTri 1 = 1 := rfl
    omega
  · rw [h2] at hmod
    have htwo : upperTri 2 = 3 := upperTri_two
    omega
  · rw [h3] at hmod
    have hthree : upperTri 3 = 6 := upperTri_three
    omega

namespace PinnedTailMinimumConfiguration

variable {target clock : Nat}

/-- An even missing target makes the pinned predecessor value odd, so the
pinned clock is 1 or 2 mod 4. -/
theorem clock_mod_four_of_target_even
    (h : PinnedTailMinimumConfiguration target clock)
    (ht : target % 2 = 0) :
    clock % 4 = 1 ∨ clock % 4 = 2 :=
  odd_value_time_mod_four (by omega) h.value_eq

/-- An odd missing target makes the pinned predecessor value even, so the
pinned clock is 0 or 3 mod 4. -/
theorem clock_mod_four_of_target_odd
    (h : PinnedTailMinimumConfiguration target clock)
    (ht : target % 2 = 1) :
    clock % 4 = 0 ∨ clock % 4 = 3 :=
  even_value_time_mod_four (by omega) h.value_eq

/-- Backward propagation instantiated at the pinned predecessor: every time
at or before the pinned clock carries a value at least `target + 1` less the
triangular gap.  This is the "small times must be high" constraint the third
row was missing, stated without truncated subtraction. -/
theorem early_orbit_floor
    (h : PinnedTailMinimumConfiguration target clock)
    {w : Nat} (hw : w ≤ clock) :
    target + 1 + upperTri w ≤ a w + upperTri clock := by
  have hv := h.value_eq
  have hprop := backward_propagation hw
  omega

end PinnedTailMinimumConfiguration

namespace TerminalExactDischargeReplayCertificate

variable {target : Nat}

/-- The adding row stores `a base = target - 2 * base - 2` at time `base`,
one above its blocked witness; parity therefore pins the residue of `base`
by the parity of the target alone.  Even targets allow only 0 and 3 mod 4. -/
theorem lastRow_base_mod_four_of_target_even {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hsecond : a base + 2 * base + 2 = target)
    (ht : target % 2 = 0) :
    base % 4 = 0 ∨ base % 4 = 3 := by
  have hclock := hp.clock_bound
  have hv : a base = target - 2 * base - 2 := by omega
  exact even_value_time_mod_four (by omega) hv

/-- Odd targets allow only the residues 1 and 2 mod 4 for the adding row. -/
theorem lastRow_base_mod_four_of_target_odd {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hsecond : a base + 2 * base + 2 = target)
    (ht : target % 2 = 1) :
    base % 4 = 1 ∨ base % 4 = 2 := by
  have hclock := hp.clock_bound
  have hv : a base = target - 2 * base - 2 := by omega
  exact odd_value_time_mod_four (by omega) hv

/-- Parity shift of the blocked witness.  The witness value sits one below
the row value `a base`, so its time lies in the complementary mod-4 class of
`base`.  On the residues 0 and 2 the time `base - 1` belongs to the same
class as `base`, so the witness is pushed at least one step further down,
strengthening `lastRow_witness_early` from `w + 1 ≤ base` to `w + 2 ≤ base`. -/
theorem lastRow_witness_beyond_adjacent {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target)
    (hbase : base % 4 = 0 ∨ base % 4 = 2) :
    ∃ w, w + 2 ≤ base ∧ a w = target - 2 * base - 3 := by
  have hclock := hp.clock_bound
  have hsix := hp.six_le_clock
  rcases lastRow_witness_early hp hprevious hsecond with ⟨w, hw, hvalue⟩
  refine ⟨w, ?_, hvalue⟩
  by_cases hadj : w = base - 1
  · exfalso
    have hstep : a w + 1 = a base := by omega
    have hpar := adjacent_occurrence_opposite_parity hstep
    have hUw := upperTri_mod_two_eq w
    have hUb := upperTri_mod_two_eq base
    rcases hbase with h0 | h2
    · have hw4 : w % 4 = 3 := by omega
      rw [hw4] at hUw
      rw [h0] at hUb
      have hthree : upperTri 3 = 6 := upperTri_three
      have hzero : upperTri 0 = 0 := rfl
      omega
    · have hw4 : w % 4 = 1 := by omega
      rw [hw4] at hUw
      rw [h2] at hUb
      have hone : upperTri 1 = 1 := rfl
      have htwo : upperTri 2 = 3 := upperTri_two
      omega
  · omega

/-- On the residues 0 and 2 of the adding row the parity shift converts into
a genuinely smaller window top: the target is bounded through the triangular
number at `base - 2` instead of `base - 1`, a saving of `base - 1`. -/
theorem lastRow_target_upper_bound_sharpened {base : Nat}
    (hp : PinnedTailMinimumConfiguration target (base + 2))
    (hprevious : a (base + 1) + base + 2 = target + 1)
    (hsecond : a base + 2 * base + 2 = target)
    (hbase : base % 4 = 0 ∨ base % 4 = 2) :
    target ≤ upperTri (base - 2) + 2 * base + 3 := by
  have hclock := hp.clock_bound
  rcases lastRow_witness_beyond_adjacent hp hprevious hsecond hbase
    with ⟨w, hw, hvalue⟩
  have hle : w ≤ base - 2 := by omega
  have hmono : upperTri w ≤ upperTri (base - 2) := upperTri_mono hle
  have hbound := a_le_upperTri w
  omega

end TerminalExactDischargeReplayCertificate

end Recaman
