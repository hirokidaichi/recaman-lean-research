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

/-- A ping-pong pair whose residue budget is below its full cost `2 p + 3` must wrap
on one of its two steps.  If `r < p + 2`, the upper-to-lower step wraps immediately;
otherwise that subtraction is regular and leaves residue below the lower level `p + 1`,
so the return step wraps. -/
theorem pingpong_pair_wrap {m p r : Nat} (hval : a m = (p + 2) * m + r)
    (hr : r < m) (hq : p + 2 ≤ m) (hlegal : m + 1 < a m)
    (hfresh : a m - (m + 1) ∉ valuesThrough m) (hbudget : r < 2 * p + 3) :
    a m % m < a (m + 1) % (m + 1) ∨
      a (m + 1) % (m + 1) < a (m + 2) % (m + 2) := by
  by_cases hlow : r < p + 2
  · left
    exact (residue_wrap hval hr hlow hq).2
  · right
    have hland := landing_of_fresh hlegal hfresh
    have hsub := residue_sub (q := p + 1) hval hr (by omega) hland
    have hwrap := (residue_wrap hsub.1 (by omega) (by omega) (by omega)).2
    rw [show m + 1 + 1 = m + 2 by omega] at hwrap
    exact hwrap

/-- A level-5/4 run spends nine residue units per completed pair.  If `K` pairs consume
all but fewer than nine units, the next pair forces a residue increase.  This is the
conditional local end mechanism after a pop-up lock exits through a blocked level-three
candidate; it does not assert that the required level-5/4 candidate history persists. -/
theorem level45_run_wrap {m r K : Nat} (hval : a m = 5 * m + r) (hr : r < m)
    (hm : 5 ≤ m) (hspent : 9 * K ≤ r) (hbudget : r < 9 * (K + 1))
    (hfresh : ∀ k, k ≤ K → a m - (m + k + 1) ∉ valuesThrough (m + 2 * k))
    (hblocked : ∀ k, k < K →
      a m - (2 * m + 3 * k + 3) ∈ valuesThrough (m + 2 * k + 1)) :
    a (m + 2 * K) % (m + 2 * K) <
        a (m + 2 * K + 1) % (m + 2 * K + 1) ∨
      a (m + 2 * K + 1) % (m + 2 * K + 1) <
        a (m + 2 * K + 2) % (m + 2 * K + 2) := by
  have hrun := pingpong_run (m := m) (K := K) (by omega)
    (fun k hk => hfresh k (Nat.le_of_lt hk)) hblocked K (Nat.le_refl K)
  have hup := hrun.1
  have hvalK : a (m + 2 * K) = 5 * (m + 2 * K) + (r - 9 * K) := by
    omega
  have hfreshK : a (m + 2 * K) - (m + 2 * K + 1) ∉ valuesThrough (m + 2 * K) := by
    have hf := hfresh K (Nat.le_refl K)
    have hcand : a (m + 2 * K) - (m + 2 * K + 1) = a m - (m + K + 1) := by
      omega
    rw [hcand]
    exact hf
  exact pingpong_pair_wrap (p := 3) hvalK (by omega) (by omega) (by omega) hfreshK (by omega)

/-- A blocked level-three candidate exits the level-3/4 pop-up lock upward, entering
level five with residue `v - 10 - 7 k`.  This is the exact bridge from the `l3blocked`
outcome coordinates to a level-5/4 ping-pong run. -/
theorem popup_l3blocked_level45_entry {i v k : Nat}
    (hupper : a (i + 5 + 2 * k) =
      3 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k))
    (hres : 10 + 7 * k ≤ v)
    (hblocked :
      2 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 1 ∈
        valuesThrough (i + 5 + 2 * k)) :
    a (i + 5 + 2 * k + 1) =
      5 * (i + 5 + 2 * k + 1) + (v - 10 - 7 * k) := by
  have hcand :
      a (i + 5 + 2 * k) - (i + 5 + 2 * k + 1) =
        2 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 1 := by
    omega
  rw [← hcand] at hblocked
  have hadd := forced_addition_of_mem hblocked
  omega

/-- If the level-5/4 candidate history after an `l3blocked` exit persists until its
nine-unit residue budget is exhausted, the Chaffin residue increases in the first
failing pair.  All survival assumptions remain explicit. -/
theorem popup_l3blocked_level45_wrap {i v k K : Nat}
    (hupper : a (i + 5 + 2 * k) =
      3 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k))
    (hle : v ≤ i) (hres : 10 + 7 * k ≤ v)
    (hl3blocked :
      2 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 1 ∈
        valuesThrough (i + 5 + 2 * k))
    (hspent : 9 * K ≤ v - 10 - 7 * k)
    (hbudget : v - 10 - 7 * k < 9 * (K + 1))
    (hfresh : ∀ j, j ≤ K →
      a (i + 5 + 2 * k + 1) - (i + 5 + 2 * k + 1 + j + 1) ∉
        valuesThrough (i + 5 + 2 * k + 1 + 2 * j))
    (hblocked : ∀ j, j < K →
      a (i + 5 + 2 * k + 1) -
          (2 * (i + 5 + 2 * k + 1) + 3 * j + 3) ∈
        valuesThrough (i + 5 + 2 * k + 1 + 2 * j + 1)) :
    a (i + 5 + 2 * k + 1 + 2 * K) % (i + 5 + 2 * k + 1 + 2 * K) <
        a (i + 5 + 2 * k + 1 + 2 * K + 1) %
          (i + 5 + 2 * k + 1 + 2 * K + 1) ∨
      a (i + 5 + 2 * k + 1 + 2 * K + 1) %
          (i + 5 + 2 * k + 1 + 2 * K + 1) <
        a (i + 5 + 2 * k + 1 + 2 * K + 2) %
          (i + 5 + 2 * k + 1 + 2 * K + 2) := by
  have hentry := popup_l3blocked_level45_entry hupper hres hl3blocked
  exact level45_run_wrap hentry (by omega) (by omega) hspent hbudget hfresh hblocked

end Recaman
