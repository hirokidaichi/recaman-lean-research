import Recaman.PopupLock

namespace Recaman

/-! # Level-2/3 ping-pong

After the pop-up of an *isolated* late landing (`late_landing_popup`), the candidate
presented at the next transition is the level-two value `2 c + v + 2` for the landing
clock `c = i + 1`, that is `2 i + v + 4`.  `PopupLock` treats the case where that value is
already visited (the orbit climbs to level four and enters the level-3/4 lock).  This file
treats the complementary case: when the level-two continuation value is fresh, the orbit
lands it and sits at level two, `a (i + 5) = 2 i + v + 4`.

From a level-two value `a m = 2 m + s` the candidate presented at the next transition is
the level-one value `m + s - 1`.

* When that candidate is fresh the orbit lands it and returns to level one at height
  `s - 2`: `a (m + 1) = m + s - 1`.
* When that candidate is visited the transition is a forced addition to level three,
  `a (m + 1) = 3 m + s + 1`, and the candidate presented next is the level-two value
  `2 m + s - 1`; when it is fresh the orbit lands it, `a (m + 2) = 2 m + s - 1`.

Iterating the second alternative gives a *level-2/3 ping-pong*: every two clocks the orbit
returns to level two, and the level-two offset drops by five per pair,
`a (m + 2 k) = 2 (m + 2 k) + (s - 5 k)`.  The phase ends with the first alternative: after
`K` pairs the orbit lands the level-one value `(m + 2 K) + (s - 5 K) - 1` at clock
`m + 2 K + 1`, that is at height `s - 5 K - 2`.  The potential `value + clock` of that
level-one clock equals `2 m + s - K`: it drops by one per pair of the phase, so a long
phase leaves the orbit with a lower potential than a short one.  (If `a m` itself arose by
a forced addition from a level-one clock `m - 1` at height `s + 1`, whose potential is
`2 m + s - 1`, the exit potential is `1 - K` higher than before the phase.)

Everything here is a direct consequence of the step recurrence and of the
descending-chain lemmas.  No target, cutoff, or reachability hypothesis is used.
-/

/-- After the pop-up of an isolated late landing at clock `i + 1`, if the level-two
continuation value `2 i + v + 4` is fresh at time `i + 4`, the orbit lands it. -/
theorem popup_return_level_two {i v : Nat} (hprev : a i = v + i + 1)
    (hland : a (i + 1) = v) (hle : v ≤ i)
    (hblocked : v - 1 ∈ valuesThrough (i + 2))
    (hfresh : 2 * i + v + 4 ∉ valuesThrough (i + 4)) :
    a (i + 5) = 2 * i + v + 4 := by
  obtain ⟨_, _, h4⟩ := late_landing_popup hprev hland hle hblocked
  have hrec := recurrence (i + 4)
  have hcan : CanSubtract (i + 4 + 1) (stateAt (i + 4)) := by
    refine ⟨?_, ?_⟩
    · show i + 4 + 1 < a (i + 4)
      omega
    · have hcand : (stateAt (i + 4)).value - (i + 4 + 1) = 2 * i + v + 4 := by
        show a (i + 4) - (i + 4 + 1) = 2 * i + v + 4
        omega
      rw [hcand]
      exact hfresh
  rw [if_pos hcan] at hrec
  rw [show i + 4 + 1 = i + 5 by omega] at hrec
  omega

/-- From a level-two value `a m = 2 m + s` (with `2 ≤ s`) whose level-one candidate
`m + s - 1` is fresh, the orbit returns to level one: `a (m + 1) = m + s - 1`. -/
theorem level2_to_level1 {m s : Nat} (hval : a m = 2 * m + s) (hs : 2 ≤ s)
    (hfresh : m + s - 1 ∉ valuesThrough m) : a (m + 1) = m + s - 1 := by
  have hrec := recurrence m
  have hcan : CanSubtract (m + 1) (stateAt m) := by
    refine ⟨?_, ?_⟩
    · show m + 1 < a m
      omega
    · have hcand : (stateAt m).value - (m + 1) = m + s - 1 := by
        show a m - (m + 1) = m + s - 1
        omega
      rw [hcand]
      exact hfresh
  rw [if_pos hcan] at hrec
  omega

/-- One pair of the level-2/3 ping-pong: from `a m = 2 m + s` with the level-one candidate
`m + s - 1` visited, the orbit adds to `3 m + s + 1`; then, if the next level-two value
`2 m + s - 1` is fresh, it lands it: `a (m + 2) = 2 m + s - 1`. -/
theorem level23_pair {m s : Nat} (hval : a m = 2 * m + s) (hs : 3 ≤ s)
    (hblocked : m + s - 1 ∈ valuesThrough m)
    (hfresh : 2 * m + s - 1 ∉ valuesThrough (m + 1)) :
    a (m + 1) = 3 * m + s + 1 ∧ a (m + 2) = 2 * m + s - 1 := by
  have h1 : a (m + 1) = 3 * m + s + 1 := by
    have hval' : a m = m + (m + s) := by omega
    have hstep := chain_forced_addition hval' hblocked
    omega
  have h2 : a (m + 2) = 2 * m + s - 1 := by
    have hrec := recurrence (m + 1)
    have hcan : CanSubtract (m + 1 + 1) (stateAt (m + 1)) := by
      refine ⟨?_, ?_⟩
      · show m + 1 + 1 < a (m + 1)
        omega
      · have hcand : (stateAt (m + 1)).value - (m + 1 + 1) = 2 * m + s - 1 := by
          show a (m + 1) - (m + 1 + 1) = 2 * m + s - 1
          omega
        rw [hcand]
        exact hfresh
    rw [if_pos hcan] at hrec
    rw [show m + 1 + 1 = m + 2 by omega] at hrec
    omega
  exact ⟨h1, h2⟩

/-- Iterated level-2/3 ping-pong: the level-two offset drops by five per pair. -/
theorem level23_phase {m s : Nat} (hval : a m = 2 * m + s) :
    ∀ K, 5 * K + 3 ≤ s →
      (∀ k, k < K → (m + 2 * k) + (s - 5 * k) - 1 ∈ valuesThrough (m + 2 * k)) →
      (∀ k, k < K → 2 * (m + 2 * k) + (s - 5 * k) - 1 ∉ valuesThrough (m + 2 * k + 1)) →
      ∀ k, k ≤ K → a (m + 2 * k) = 2 * (m + 2 * k) + (s - 5 * k) := by
  intro K hK hblocked hfresh k
  induction k with
  | zero =>
      intro _
      have h₀ : m + 2 * 0 = m := by omega
      rw [h₀]
      omega
  | succ k ih =>
      intro hk
      have hprev : a (m + 2 * k) = 2 * (m + 2 * k) + (s - 5 * k) := ih (by omega)
      have hs' : 3 ≤ s - 5 * k := by omega
      have hpair := level23_pair hprev hs' (hblocked k (by omega)) (hfresh k (by omega))
      have hidx : m + 2 * (k + 1) = m + 2 * k + 2 := by omega
      rw [hidx, hpair.2]
      omega

/-- Exit of the level-2/3 phase to level one after `K` pairs: the landed level-one value is
`(m + 2 K) + (s - 5 K) - 1`, whose potential `value + clock` equals `2 m + s - K`. -/
theorem level23_exit {m s K : Nat} (hval : a m = 2 * m + s) (hK : 5 * K + 3 ≤ s)
    (hblocked : ∀ k, k < K → (m + 2 * k) + (s - 5 * k) - 1 ∈ valuesThrough (m + 2 * k))
    (hfresh : ∀ k, k < K → 2 * (m + 2 * k) + (s - 5 * k) - 1 ∉ valuesThrough (m + 2 * k + 1))
    (hexit : (m + 2 * K) + (s - 5 * K) - 1 ∉ valuesThrough (m + 2 * K)) :
    a (m + 2 * K + 1) = (m + 2 * K) + (s - 5 * K) - 1 ∧
      a (m + 2 * K + 1) + (m + 2 * K + 1) = 2 * m + s - K := by
  have hphase := level23_phase hval K hK hblocked hfresh K (Nat.le_refl K)
  have hs' : 2 ≤ s - 5 * K := by omega
  have hland := level2_to_level1 hphase hs' hexit
  exact ⟨hland, by omega⟩

end Recaman
