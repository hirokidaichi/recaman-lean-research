import Recaman.CoordinateDynamics

namespace Recaman

/-! # Comb runs: closed forms for alternating orbit segments

Long stretches of the Recamán orbit alternate a forced addition with an
immediately repaying legal subtraction.  Over such a comb run the orbit is
determined by its entry value: the low rail decreases by exactly one per
period and the high rail is the low rail plus the current clock.

These closed forms are the first ingredient of compressed orbit
verification: a comb run of any length is certified by its two boundary
transitions per period, each of which is decidable, and the values inside
the run then follow by the rail formulas instead of step-by-step kernel
evaluation.
-/

/-- One comb period: a forced addition immediately repaid by a legal
subtraction. -/
structure CombStep (s : Nat) : Prop where
  forced_up : ¬ CanSubtract (s + 1) (stateAt s)
  legal_down : CanSubtract (s + 2) (stateAt (s + 1))

instance (s : Nat) : Decidable (CombStep s) :=
  decidable_of_iff
    (¬ CanSubtract (s + 1) (stateAt s) ∧
      CanSubtract (s + 2) (stateAt (s + 1)))
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.forced_up, h.legal_down⟩⟩

/-- The high rail of one period sits a full clock above the entry value. -/
theorem CombStep.high_rail {s : Nat} (h : CombStep s) :
    a (s + 1) = a s + (s + 1) :=
  a_succ_of_not_canSubtract h.forced_up

/-- The low rail of one period drops by exactly one. -/
theorem CombStep.low_rail {s : Nat} (h : CombStep s) :
    a (s + 2) + 1 = a s :=
  a_add_then_sub_eq_pred h.forced_up h.legal_down

/-- A comb run: `k` consecutive comb periods starting at `s`. -/
def CombRun (s k : Nat) : Prop :=
  ∀ i, i < k → CombStep (s + 2 * i)

instance (s k : Nat) : Decidable (CombRun s k) :=
  Nat.decidableBallLT k fun i _ => CombStep (s + 2 * i)

/-- A prefix of a comb run is a comb run. -/
theorem CombRun.mono {s k j : Nat} (h : CombRun s k) (hle : j ≤ k) :
    CombRun s j :=
  fun i hi => h i (by omega)

/-- Low-rail closed form: after `i` periods the value has dropped by
exactly `i`. -/
theorem CombRun.low_rail {s k : Nat} (h : CombRun s k) :
    ∀ i, i ≤ k → a (s + 2 * i) + i = a s := by
  intro i
  induction i with
  | zero =>
      intro _
      simp
  | succ i ih =>
      intro hle
      have hstep : CombStep (s + 2 * i) := h i (by omega)
      have hprev := ih (by omega)
      have hlow := hstep.low_rail
      have harith : s + 2 * (i + 1) = s + 2 * i + 2 := by omega
      rw [harith]
      omega

/-- High-rail closed form: each odd step adds the current clock to the
descending low rail. -/
theorem CombRun.high_rail {s k : Nat} (h : CombRun s k) :
    ∀ i, i < k → a (s + 2 * i + 1) + i = a s + (s + 2 * i + 1) := by
  intro i hik
  have hstep := h i hik
  have hlowRun := h.low_rail i (by omega)
  have hhigh := hstep.high_rail
  omega

/-- Exit value of a full comb run. -/
theorem CombRun.exit_value {s k : Nat} (h : CombRun s k) :
    a (s + 2 * k) + k = a s :=
  h.low_rail k (Nat.le_refl _)

/-- Kernel-checked sample: the actual orbit runs a four-period comb from
time 23, taking the low rail from `a 23 = 18` down to `a 31 = 14`. -/
example : CombRun 23 4 := by
  set_option maxRecDepth 100000 in decide

end Recaman
