import Recaman.LockResidue

namespace Recaman

/-! # Ping-pong runs at every level

A *ping-pong* between the levels `p + 2` and `p + 1` is the alternation
"subtract (the lower value is fresh), add (the next candidate is visited)".  The
descending chain (`DescendingChain`, `p = 0`), the level-2/3 phase (`LevelTwoThree`,
`p = 1`) and the level-3/4 lock (`PopupLock`, `p = 2`) are its instances.  This module
records the level-free facts behind all of them:

* one pair sends `a m = (p + 2) m + r` to the lower value `(p + 1)(m + 1) + (r - (p + 2))`
  and back to the upper value `(p + 2)(m + 2) + (r - (2 p + 3))`, so the residue drops by
  `2 p + 3` per pair (`pingpong_pair`, `pingpong_pair_residues`);
* along a run of `K` pairs the upper values form the increasing run `a m + k` and the
  lower values the decreasing run `a m - (m + k + 1)` (`pingpong_run`).  A value visited
  by a ping-pong therefore sits in a run of consecutive integers visited two clocks apart,
  which is what the blocker-provenance census (`H-20260903-01`) tests on the orbit.

The two step lemmas `forced_addition_of_mem` and `landing_of_fresh` are the recurrence
read through the candidate: a visited candidate forces the addition, a fresh candidate
below the current value forces the subtraction.
-/

/-- A visited candidate forces the addition. -/
theorem forced_addition_of_mem {n : Nat} (h : a n - (n + 1) ∈ valuesThrough n) :
    a (n + 1) = a n + (n + 1) := by
  have hrec := recurrence n
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · exfalso
    exact hcan.2 h
  · rw [if_neg hcan] at hrec
    exact hrec

/-- A fresh candidate below the current value forces the subtraction. -/
theorem landing_of_fresh {n : Nat} (hlt : n + 1 < a n)
    (hfresh : a n - (n + 1) ∉ valuesThrough n) : a (n + 1) = a n - (n + 1) := by
  have hrec := recurrence n
  have hcan : CanSubtract (n + 1) (stateAt n) := by
    refine ⟨?_, ?_⟩
    · show n + 1 < a n
      exact hlt
    · show a n - (n + 1) ∉ valuesThrough n
      exact hfresh
  rw [if_pos hcan] at hrec
  exact hrec

/-- One ping-pong pair between the levels `p + 2` and `p + 1`: from the upper value
`a m = (p + 2) m + r` with `2 p + 3 ≤ r < m`, a fresh candidate lands the lower value
`(p + 1)(m + 1) + (r - (p + 2))`, and a visited next candidate returns to the upper value
`(p + 2)(m + 2) + (r - (2 p + 3)) = a m + 1`. -/
theorem pingpong_pair {m p r : Nat} (hval : a m = (p + 2) * m + r) (hr : r < m)
    (hpr : 2 * p + 3 ≤ r) (hfresh : a m - (m + 1) ∉ valuesThrough m)
    (hblocked : a (m + 1) - (m + 2) ∈ valuesThrough (m + 1)) :
    a (m + 1) = (p + 1) * (m + 1) + (r - (p + 2)) ∧
      a (m + 2) = (p + 2) * (m + 2) + (r - (2 * p + 3)) ∧
      a (m + 1) = a m - (m + 1) ∧ a (m + 2) = a m + 1 := by
  have hexp1 : (p + 2) * m = p * m + 2 * m := Nat.add_mul p 2 m
  have hexp2 : (p + 1) * (m + 1) = p * m + p + (m + 1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  have hexp3 : (p + 2) * (m + 2) = p * m + p * 2 + (2 * m + 2 * 2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  have hlt : m + 1 < a m := by omega
  have h1 : a (m + 1) = a m - (m + 1) := landing_of_fresh hlt hfresh
  have h2 : a (m + 1 + 1) = a (m + 1) + (m + 1 + 1) := forced_addition_of_mem hblocked
  rw [show m + 1 + 1 = m + 2 by omega] at h2
  refine ⟨by omega, by omega, h1, by omega⟩

/-- Residues along one ping-pong pair: `r`, then `r - (p + 2)`, then `r - (2 p + 3)`, with
the levels `p + 2`, `p + 1`, `p + 2`. -/
theorem pingpong_pair_residues {m p r : Nat} (hval : a m = (p + 2) * m + r) (hr : r < m)
    (hpr : 2 * p + 3 ≤ r) (hfresh : a m - (m + 1) ∉ valuesThrough m)
    (hblocked : a (m + 1) - (m + 2) ∈ valuesThrough (m + 1)) :
    a m / m = p + 2 ∧ a m % m = r ∧
      a (m + 1) / (m + 1) = p + 1 ∧ a (m + 1) % (m + 1) = r - (p + 2) ∧
      a (m + 2) / (m + 2) = p + 2 ∧ a (m + 2) % (m + 2) = r - (2 * p + 3) := by
  obtain ⟨h1, h2, _, _⟩ := pingpong_pair hval hr hpr hfresh hblocked
  have h1lt : r - (p + 2) < m + 1 := by omega
  have h2lt : r - (2 * p + 3) < m + 2 := by omega
  exact ⟨div_eq_of_decomp hval hr, mod_eq_of_decomp hval hr,
    div_eq_of_decomp h1 h1lt, mod_eq_of_decomp h1 h1lt,
    div_eq_of_decomp h2 h2lt, mod_eq_of_decomp h2 h2lt⟩

/-- A run of `K` ping-pong pairs, written through the candidates.  As long as the lower
values `a m - (m + k + 1)` are fresh when presented (at clock `m + 2 k`) and the next
candidates `a m - (2 m + 3 k + 3)` are visited when presented (at clock `m + 2 k + 1`), the
upper values are the increasing run `a (m + 2 k) = a m + k` and the lower values the
decreasing run `a (m + 2 k + 1) = a m - (m + k + 1)`.  The legality of every subtraction
is `m + K < a m`.  No level hypothesis is needed. -/
theorem pingpong_run {m K : Nat} (hlegal : m + K < a m)
    (hfresh : ∀ k, k < K → a m - (m + k + 1) ∉ valuesThrough (m + 2 * k))
    (hblocked : ∀ k, k < K → a m - (2 * m + 3 * k + 3) ∈ valuesThrough (m + 2 * k + 1)) :
    ∀ k, k ≤ K →
      a (m + 2 * k) = a m + k ∧ (k < K → a (m + 2 * k + 1) = a m - (m + k + 1)) := by
  intro k
  induction k with
  | zero =>
      intro _
      have h0 : m + 2 * 0 = m := by omega
      refine ⟨by rw [h0]; omega, ?_⟩
      intro hK
      have hf := hfresh 0 hK
      rw [h0, show m + 0 + 1 = m + 1 by omega] at hf
      have hlt : m + 1 < a m := by omega
      have hland := landing_of_fresh hlt hf
      rw [h0]
      omega
  | succ k ih =>
      intro hk
      obtain ⟨hup, hlow⟩ := ih (by omega)
      have hlower := hlow (by omega)
      have hb := hblocked k (by omega)
      have hcand : a (m + 2 * k + 1) - (m + 2 * k + 1 + 1) = a m - (2 * m + 3 * k + 3) := by
        omega
      rw [← hcand] at hb
      have hadd := forced_addition_of_mem hb
      have hidx : m + 2 * (k + 1) = m + 2 * k + 1 + 1 := by omega
      have hup' : a (m + 2 * (k + 1)) = a m + (k + 1) := by
        rw [hidx]
        omega
      refine ⟨hup', ?_⟩
      intro hK
      have hf := hfresh (k + 1) hK
      have hlt : m + 2 * (k + 1) + 1 < a (m + 2 * (k + 1)) := by omega
      have hcand' : a (m + 2 * (k + 1)) - (m + 2 * (k + 1) + 1) = a m - (m + (k + 1) + 1) := by
        omega
      rw [← hcand'] at hf
      have hland := landing_of_fresh hlt hf
      omega

end Recaman
