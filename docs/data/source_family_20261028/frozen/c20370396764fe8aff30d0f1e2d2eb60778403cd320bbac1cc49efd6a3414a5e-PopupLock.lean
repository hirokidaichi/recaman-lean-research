import Recaman.HoleHopping

namespace Recaman

/-! # Pop-up lock

After an *isolated* late landing (the landed value `v` has `v - 1` already visited),
`late_landing_popup` shows that the orbit adds three times in a row: from the landing
clock `c = i + 1` it climbs to `c + v`, `2 c + v + 1`, `3 c + v + 3` (in the `i`
coordinates of `HoleHopping`: `v + i + 2`, `v + 2 i + 5`, `v + 3 i + 9`).

The candidate presented at the next transition is the level-two value `2 c + v + 2`.
When that value is already visited the orbit adds a fourth time and reaches level four,
`4 c + v + 6`.  From there it performs a *level-3/4 ping-pong*: every subtraction lands a
level-three value `2 m + t - 1` (for `a m = 3 m + t`), and the following candidate is the
level-two value `m + t - 3`; as long as those level-two candidates are visited, the orbit
is forced back up to level four.  Consequently the orbit visits no value below its clock
for the whole duration of the lock.

The level-two candidates presented during the lock are the orbit's own earlier values:
the additions of the level-1/2 ping-pong that precedes the landing produce exactly the
values `2 i + v + 2 - j`, and the last theorem records that identity.

Everything here is a direct consequence of the step recurrence and of the
descending-chain lemmas.  No target, cutoff, or reachability hypothesis is used.
-/

/-- Lock entry: after the pop-up of an isolated late landing at clock `i + 1`, if the
level-two continuation value `2 i + v + 4` (that is `2 c + v + 2` for `c = i + 1`) is
already visited, the next step adds too and the orbit reaches level four:
`a (i + 5) = 4 i + v + 14`. -/
theorem popup_lock_entry {i v : Nat} (hprev : a i = v + i + 1)
    (hland : a (i + 1) = v) (hle : v ≤ i)
    (hblocked : v - 1 ∈ valuesThrough (i + 2))
    (hlock : 2 * i + v + 4 ∈ valuesThrough (i + 4)) :
    a (i + 5) = 4 * i + v + 14 := by
  obtain ⟨_, _, h4⟩ := late_landing_popup hprev hland hle hblocked
  have hval : a (i + 4) = (i + 4) + (2 * i + v + 5) := by omega
  have hblocked' : 2 * i + v + 5 - 1 ∈ valuesThrough (i + 4) := by
    rw [show 2 * i + v + 5 - 1 = 2 * i + v + 4 by omega]
    exact hlock
  have hstep := chain_forced_addition hval hblocked'
  rw [show i + 4 + 1 = i + 5 by omega] at hstep
  omega

/-- One pair of the level-3/4 ping-pong.  From an upper value `a m = 3 * m + t` (so the
candidate at `m + 1` is `2 * m + t - 1`) with that candidate unvisited, the orbit lands
`a (m + 1) = 2 * m + t - 1`; then, if the candidate `m + t - 3` presented at `m + 2` is
visited, the orbit adds to `a (m + 2) = 3 * m + t + 1`. -/
theorem level34_pair {m t : Nat} (hval : a m = 3 * m + t) (ht : 3 ≤ t)
    (hfresh : 2 * m + t - 1 ∉ valuesThrough m)
    (hblocked : m + t - 3 ∈ valuesThrough (m + 1)) :
    a (m + 1) = 2 * m + t - 1 ∧ a (m + 2) = 3 * m + t + 1 := by
  have h1 : a (m + 1) = 2 * m + t - 1 := by
    have hrec := recurrence m
    have hcan : CanSubtract (m + 1) (stateAt m) := by
      refine ⟨?_, ?_⟩
      · show m + 1 < a m
        omega
      · have hcand : (stateAt m).value - (m + 1) = 2 * m + t - 1 := by
          show a m - (m + 1) = 2 * m + t - 1
          omega
        rw [hcand]
        exact hfresh
    rw [if_pos hcan] at hrec
    omega
  have h2 : a (m + 2) = 3 * m + t + 1 := by
    have hval' : a (m + 1) = (m + 1) + (m + t - 2) := by omega
    have hblocked' : m + t - 2 - 1 ∈ valuesThrough (m + 1) := by
      rw [show m + t - 2 - 1 = m + t - 3 by omega]
      exact hblocked
    have hstep := chain_forced_addition hval' hblocked'
    rw [show m + 1 + 1 = m + 2 by omega] at hstep
    omega
  exact ⟨h1, h2⟩

/-- Iterated level-3/4 ping-pong: starting from `a m = 3 * m + t`, as long as the
level-three values `2 * (m + 2 k) + (t - 5 k) - 1` are unvisited when presented and the
level-two candidates `(m + 2 k) + (t - 5 k) - 3` are visited when presented, the orbit
returns to level four every two clocks: `a (m + 2 k) = 3 * (m + 2 k) + (t - 5 k)`.  Each
pair lowers the level-three offset by five. -/
theorem level34_lock {m t : Nat} (hval : a m = 3 * m + t) :
    ∀ K, 5 * K + 3 ≤ t →
      (∀ k, k < K → 2 * (m + 2 * k) + (t - 5 * k) - 1 ∉ valuesThrough (m + 2 * k)) →
      (∀ k, k < K → (m + 2 * k) + (t - 5 * k) - 3 ∈ valuesThrough (m + 2 * k + 1)) →
      ∀ k, k ≤ K → a (m + 2 * k) = 3 * (m + 2 * k) + (t - 5 * k) := by
  intro K hK hfresh hblocked k
  induction k with
  | zero =>
      intro _
      have h₀ : m + 2 * 0 = m := by omega
      rw [h₀]
      omega
  | succ k ih =>
      intro hk
      have hprev : a (m + 2 * k) = 3 * (m + 2 * k) + (t - 5 * k) := ih (by omega)
      have ht' : 3 ≤ t - 5 * k := by omega
      have hpair := level34_pair hprev ht' (hfresh k (by omega)) (hblocked k (by omega))
      have hidx : m + 2 * (k + 1) = m + 2 * k + 2 := by omega
      rw [hidx, hpair.2]
      omega

/-- During the lock the orbit never visits a value below its clock: every clock
`n` with `m ≤ n ≤ m + 2 K` satisfies `n ≤ a n`. -/
theorem level34_lock_above_clock {m t K : Nat} (hval : a m = 3 * m + t)
    (hK : 5 * K + 3 ≤ t)
    (hfresh : ∀ k, k < K → 2 * (m + 2 * k) + (t - 5 * k) - 1 ∉ valuesThrough (m + 2 * k))
    (hblocked : ∀ k, k < K → (m + 2 * k) + (t - 5 * k) - 3 ∈ valuesThrough (m + 2 * k + 1)) :
    ∀ n, m ≤ n → n ≤ m + 2 * K → n ≤ a n := by
  intro n hmn hnK
  have hlock := level34_lock hval K hK hfresh hblocked
  obtain ⟨k, hk⟩ : ∃ k, k = (n - m) / 2 := ⟨_, rfl⟩
  have hcases : n = m + 2 * k ∨ n = m + 2 * k + 1 := by omega
  rcases hcases with heven | hodd
  · have hv := hlock k (by omega)
    rw [heven]
    omega
  · have hkK : k < K := by omega
    have hprev := hlock k (by omega)
    have ht' : 3 ≤ t - 5 * k := by omega
    have hpair := level34_pair hprev ht' (hfresh k hkK) (hblocked k hkK)
    rw [hodd]
    omega

/-- The level-two candidates presented during the lock are the orbit's own earlier
level-two values.  With the landing at clock `i + 1` from height `v + 1`, if the chain
before the landing had heights `v + 1 + 3 j` at clocks `i - 2 j` (for `j ≤ J`, all small
candidates blocked), then the addition step after the interior clock `i - 2 j` produces
`a (i - 2 j + 1) = 2 i + v + 2 - j` for `1 ≤ j ≤ J`. -/
theorem prelanding_upper_values {i v J : Nat} (hJ : 2 * J + 1 ≤ i)
    (hchain : ∀ j, j ≤ J → a (i - 2 * j) = (i - 2 * j) + (v + 1 + 3 * j))
    (hblocked : ∀ j, j ≤ J → v + 3 * j ∈ valuesThrough (i - 2 * j)) :
    ∀ j, 1 ≤ j → j ≤ J → a (i - 2 * j + 1) = 2 * i + v + 2 - j := by
  intro j _ hjJ
  have hval := hchain j hjJ
  have hblocked' : v + 1 + 3 * j - 1 ∈ valuesThrough (i - 2 * j) := by
    rw [show v + 1 + 3 * j - 1 = v + 3 * j by omega]
    exact hblocked j hjJ
  have hstep := chain_forced_addition hval hblocked'
  omega

end Recaman
