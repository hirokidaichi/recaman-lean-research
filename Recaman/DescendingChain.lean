import Recaman.History

namespace Recaman

/-! # Descending chains

A *descending chain* is the exact local mechanism by which the canonical
orbit visits values just above its clock and, occasionally, small values
late.  Write the orbit value at an interior clock `n` as `a n = n + h` and
call `h` the *height*.  The subtraction candidate presented at the next
transition is the small value `h - 1`.

* When `h - 1` is already in history, the transition is a forced addition and
  the orbit jumps to `2 * n + h + 1`.  The candidate presented at the
  following transition is then the band value `n + h - 1`, sitting just above
  the clock `n + 2`.
* When that band value is fresh at time `n + 1`, the orbit lands it: at clock
  `n + 2` the value is `n + h - 1`, of height `h - 3`.

Iterating fills the band contiguously (`n + h - 1`, `n + h - 2`, ...) while
the small candidates `h - 1`, `h - 4`, `h - 7`, ... stay in a single residue
class modulo three.  A chain has exactly two exits: the band value is already
visited, so the chain leaves upward to `3 * n + h + 3`; or the small candidate
is fresh, so the orbit lands that small value `h - 1` late.  The final theorem
characterizes such a late landing: a value `t` with `1 ≤ t ≤ n` is landed at
clock `n + 1` precisely when clock `n` sits at height `t + 1` and `t` is still
unvisited.

Everything here is a direct consequence of the step recurrence.  No target,
cutoff, or reachability hypothesis is used.
-/

/-- Forced addition from height `h` when the small candidate `h - 1` is in history. -/
theorem chain_forced_addition {n h : Nat} (hval : a n = n + h)
    (hblocked : h - 1 ∈ valuesThrough n) : a (n + 1) = 2 * n + h + 1 := by
  have hrec := recurrence n
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · exfalso
    apply hcan.2
    have hcand : (stateAt n).value - (n + 1) = h - 1 := by
      show a n - (n + 1) = h - 1
      omega
    rw [hcand]
    exact hblocked
  · rw [if_neg hcan] at hrec
    omega

/-- From height `h ≥ 2` with the small candidate blocked and the band value `n + h - 1`
fresh at time `n + 1`, the orbit lands `n + h - 1` at clock `n + 2` (height `h - 3`). -/
theorem chain_landing {n h : Nat} (hval : a n = n + h) (hh : 2 ≤ h)
    (hblocked : h - 1 ∈ valuesThrough n)
    (hfresh : n + h - 1 ∉ valuesThrough (n + 1)) : a (n + 2) = n + h - 1 := by
  have h₁ : a (n + 1) = 2 * n + h + 1 := chain_forced_addition hval hblocked
  have hrec : a (n + 2) =
      if CanSubtract (n + 2) (stateAt (n + 1)) then a (n + 1) - (n + 2)
      else a (n + 1) + (n + 2) := recurrence (n + 1)
  have hcan : CanSubtract (n + 2) (stateAt (n + 1)) := by
    refine ⟨?_, ?_⟩
    · show n + 2 < a (n + 1)
      omega
    · have hcand : (stateAt (n + 1)).value - (n + 2) = n + h - 1 := by
        show a (n + 1) - (n + 2) = n + h - 1
        omega
      rw [hcand]
      exact hfresh
  rw [if_pos hcan] at hrec
  omega

/-- Upward exit: if the band value is already visited, the chain leaves upward. -/
theorem chain_exit_up {n h : Nat} (hval : a n = n + h)
    (hblocked : h - 1 ∈ valuesThrough n)
    (hseen : n + h - 1 ∈ valuesThrough (n + 1)) : a (n + 2) = 3 * n + h + 3 := by
  have h₁ : a (n + 1) = 2 * n + h + 1 := chain_forced_addition hval hblocked
  have hrec : a (n + 2) =
      if CanSubtract (n + 2) (stateAt (n + 1)) then a (n + 1) - (n + 2)
      else a (n + 1) + (n + 2) := recurrence (n + 1)
  by_cases hcan : CanSubtract (n + 2) (stateAt (n + 1))
  · exfalso
    apply hcan.2
    have hcand : (stateAt (n + 1)).value - (n + 2) = n + h - 1 := by
      show a (n + 1) - (n + 2) = n + h - 1
      omega
    rw [hcand]
    exact hseen
  · rw [if_neg hcan] at hrec
    omega

/-- Late landing: from height `h ≥ 2` with the small candidate `h - 1` fresh, the orbit
lands the small value `h - 1` at the next clock. -/
theorem chain_late_landing {n h : Nat} (hval : a n = n + h) (hh : 2 ≤ h)
    (hfresh : h - 1 ∉ valuesThrough n) : a (n + 1) = h - 1 := by
  have hrec := recurrence n
  have hcan : CanSubtract (n + 1) (stateAt n) := by
    refine ⟨?_, ?_⟩
    · show n + 1 < a n
      omega
    · have hcand : (stateAt n).value - (n + 1) = h - 1 := by
        show a n - (n + 1) = h - 1
        omega
      rw [hcand]
      exact hfresh
  rw [if_pos hcan] at hrec
  omega

/-- Iterated descent: `k` chain steps from height `h` land `n + h - k` at clock `n + 2k`,
that is height `h - 3k`. -/
theorem chain_descends {n h : Nat} : ∀ k, 3 * k + 2 ≤ h →
    (∀ i, i < k → h - 1 - 3 * i ∈ valuesThrough (n + 2 * i)) →
    (∀ i, i < k → n + h - 1 - i ∉ valuesThrough (n + 2 * i + 1)) →
    a n = n + h → a (n + 2 * k) = n + h - k := by
  intro k
  induction k with
  | zero =>
      intro _ _ _ hval
      have h₀ : n + 2 * 0 = n := by omega
      rw [h₀]
      omega
  | succ k ih =>
      intro hk hblocked hfresh hval
      have hprev : a (n + 2 * k) = n + h - k :=
        ih (by omega) (fun i hi => hblocked i (by omega))
          (fun i hi => hfresh i (by omega)) hval
      have hval' : a (n + 2 * k) = n + 2 * k + (h - 3 * k) := by
        rw [hprev]
        omega
      have hh' : 2 ≤ h - 3 * k := by omega
      have hblocked' : h - 3 * k - 1 ∈ valuesThrough (n + 2 * k) := by
        have heq : h - 3 * k - 1 = h - 1 - 3 * k := by omega
        rw [heq]
        exact hblocked k (by omega)
      have hfresh' :
          n + 2 * k + (h - 3 * k) - 1 ∉ valuesThrough (n + 2 * k + 1) := by
        have heq : n + 2 * k + (h - 3 * k) - 1 = n + h - 1 - k := by omega
        rw [heq]
        exact hfresh k (by omega)
      have hland := chain_landing hval' hh' hblocked' hfresh'
      have hidx : n + 2 * (k + 1) = n + 2 * k + 2 := by omega
      rw [hidx, hland]
      omega

/-- The small candidates of a chain stay in one residue class modulo three. -/
theorem chain_small_candidate_mod_three (h i : Nat) (hi : 3 * i + 1 ≤ h) :
    (h - 1 - 3 * i) % 3 = (h - 1) % 3 := by
  omega

/-- Late-landing characterization: a value `t` with `1 ≤ t ≤ n` is landed at clock
`n + 1` exactly when clock `n` sits at height `t + 1` and `t` is still unvisited. -/
theorem late_landing_iff {n t : Nat} (ht : 1 ≤ t) (htn : t ≤ n) :
    a (n + 1) = t ↔ (a n = n + (t + 1) ∧ t ∉ valuesThrough n) := by
  have hrec := recurrence n
  constructor
  · intro hland
    by_cases hcan : CanSubtract (n + 1) (stateAt n)
    · rw [if_pos hcan] at hrec
      have hlt : n + 1 < a n := hcan.1
      refine ⟨by omega, ?_⟩
      have hcand : (stateAt n).value - (n + 1) = t := by
        show a n - (n + 1) = t
        omega
      have hnot := hcan.2
      rw [hcand] at hnot
      exact hnot
    · rw [if_neg hcan] at hrec
      exfalso
      omega
  · rintro ⟨hval, hfresh⟩
    have hcan : CanSubtract (n + 1) (stateAt n) := by
      refine ⟨?_, ?_⟩
      · show n + 1 < a n
        omega
      · have hcand : (stateAt n).value - (n + 1) = t := by
          show a n - (n + 1) = t
          omega
        rw [hcand]
        exact hfresh
    rw [if_pos hcan] at hrec
    omega

end Recaman
