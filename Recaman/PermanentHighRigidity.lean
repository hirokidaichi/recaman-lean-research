import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger
import Recaman.LeastTailMinimumDynamics
import Recaman.EventualHighCorridorStructure
import Recaman.DebtInvariant

namespace Recaman

/-! # Permanent High Structural Rigidity and Oscillation Obstructions

In this module, we formalize the bilateral rigidity governing the Permanent
High Regime (`∀ n ≥ H, 2n ≤ a n`):

1. **Subtraction Escalation**:
   - Single subtraction requires `3(k + 1) ≤ a k`.
   - Two consecutive subtractions require `4k + 7 ≤ a k`.
   - Three consecutive subtractions require `5k + 12 ≤ a k`.

2. **Forced Addition Height Elevation**:
   - For any `n ≥ 6`, two consecutive additions in the permanent high regime
     strictly elevate the orbit height to `3(n + 3) ≤ a (n + 2)`.

3. **Historical Blocker Requirement for Three Additions**:
   - If a third consecutive addition occurs at step `n + 3`, the failure to
     subtract cannot be due to insufficient height; it MUST be blocked by
     the candidate `a (n + 1) - 1`.
   - The candidate satisfies `a n < a (n + 1) - 1 < a (n + 1) < a (n + 2)`.
   - Hence the blocker must have appeared at an earlier time `j ≤ n - 1`,
     forcing the existence of a prior summit `3n ≤ a j`.
   - In any segment without a prior summit exceeding `3n`, three consecutive
     additions are strictly impossible: step `n + 3` is forced to subtract.

4. **Landing Law of Forced Subtraction**:
   - When step `n + 3` subtracts, it lands on the historically fresh value
     `a (n + 3) = a n + n`, depositing clock `n + 3` into `subSum`.

5. **Infinitely Many Subtractions**:
   - Additions can never persist indefinitely (`no_perpetual_forcedAddition_ray`),
     so legal subtractions must recur infinitely often.
   - However, the subtraction ledger mass is permanently capped by
     `2 * subSum n ≤ upperTri n - 2n`, and `subCount` is capped by
     `2 * upperTri (subCount n) + 2n ≤ upperTri n`.
-/

/-! ### Part 1: Subtraction Escalation -/

/-- In the permanent high regime, two consecutive subtractions require the initial
value to be at least `4k + 7`. -/
theorem permanent_high_two_subtractions_requires_four_times
    {H k : Nat}
    (hhigh : ∀ n, H ≤ n → 2 * n ≤ a n)
    (hk : H ≤ k)
    (hcan1 : CanSubtract (k + 1) (stateAt k))
    (hcan2 : CanSubtract (k + 2) (stateAt (k + 1))) :
    4 * k + 7 ≤ a k := by
  have hstep1 := a_succ_of_canSubtract hcan1
  have hsub2 := permanent_high_subtraction_requires_three_times hhigh (by omega) hcan2
  have hlt : k + 1 < a k := hcan1.1
  omega

/-- In the permanent high regime, three consecutive subtractions require the initial
value to be at least `5k + 12`. -/
theorem permanent_high_three_subtractions_requires_five_times
    {H k : Nat}
    (hhigh : ∀ n, H ≤ n → 2 * n ≤ a n)
    (hk : H ≤ k)
    (hcan1 : CanSubtract (k + 1) (stateAt k))
    (hcan2 : CanSubtract (k + 2) (stateAt (k + 1)))
    (hcan3 : CanSubtract (k + 3) (stateAt (k + 2))) :
    5 * k + 12 ≤ a k := by
  have hstep1 := a_succ_of_canSubtract hcan1
  have hstep2 := a_succ_of_canSubtract hcan2
  have heq : k + 1 + 1 = k + 2 := by omega
  rw [heq] at hstep2
  have hsub3 := permanent_high_subtraction_requires_three_times hhigh (by omega) hcan3
  have hlt1 : k + 1 < a k := hcan1.1
  have hlt2 : k + 2 < a (k + 1) := hcan2.1
  omega

/-- If `a k < 4k + 7`, two consecutive subtractions are strictly impossible. -/
theorem permanent_high_not_two_subtractions_of_lt_four
    {H k : Nat}
    (hhigh : ∀ n, H ≤ n → 2 * n ≤ a n)
    (hk : H ≤ k)
    (hlt : a k < 4 * k + 7)
    (hcan1 : CanSubtract (k + 1) (stateAt k)) :
    ¬ CanSubtract (k + 2) (stateAt (k + 1)) := by
  intro hcan2
  have hge := permanent_high_two_subtractions_requires_four_times hhigh hk hcan1 hcan2
  omega

/-- If `a k < 5k + 12`, three consecutive subtractions are strictly impossible. -/
theorem permanent_high_not_three_subtractions_of_lt_five
    {H k : Nat}
    (hhigh : ∀ n, H ≤ n → 2 * n ≤ a n)
    (hk : H ≤ k)
    (hlt : a k < 5 * k + 12)
    (hcan1 : CanSubtract (k + 1) (stateAt k))
    (hcan2 : CanSubtract (k + 2) (stateAt (k + 1))) :
    ¬ CanSubtract (k + 3) (stateAt (k + 2)) := by
  intro hcan3
  have hge := permanent_high_three_subtractions_requires_five_times hhigh hk hcan1 hcan2 hcan3
  omega

/-! ### Part 2: Forced Addition Height Elevation -/

/-- For any `n ≥ 6`, two consecutive additions in the permanent high regime
strictly elevate the orbit height to at least `3(n + 3)`. -/
theorem permanent_high_two_additions_reach_three
    {H n : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hnH : H ≤ n)
    (hn6 : 6 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1))) :
    3 * (n + 3) ≤ a (n + 2) := by
  have hval_n := hhigh n hnH
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq : n + 1 + 1 = n + 2 := by omega
  rw [heq] at hstep2
  omega

/-! ### Part 3: Historical Blocker Requirement for Three Additions -/

/-- The subtraction candidate after two additions satisfies `a (n + 2) - (n + 3) = a (n + 1) - 1`. -/
theorem permanent_high_candidate_after_two_additions
    {n : Nat}
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1))) :
    a (n + 2) - (n + 3) = a (n + 1) - 1 := by
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq : n + 1 + 1 = n + 2 := by omega
  rw [heq] at hstep2
  omega

/-- The candidate `a (n + 1) - 1` strictly sits between `a n` and `a (n + 1)`. -/
theorem permanent_high_candidate_between
    {n : Nat} (hn1 : 1 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n)) :
    a n < a (n + 1) - 1 ∧ a (n + 1) - 1 < a (n + 1) := by
  have hstep1 := a_succ_of_not_canSubtract hnot1
  omega

/-- If three consecutive additions occur, the subtraction failure at step `n + 3`
must be caused by a historical collision in `valuesThrough (n + 2)`. -/
theorem permanent_high_third_addition_must_be_blocked
    {H n : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hnH : H ≤ n)
    (hn6 : 6 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hnot3 : ¬ CanSubtract (n + 3) (stateAt (n + 2))) :
    a (n + 1) - 1 ∈ valuesThrough (n + 2) := by
  have hthree := permanent_high_two_additions_reach_three hhigh hnH hn6 hnot1 hnot2
  have hcand := permanent_high_candidate_after_two_additions hnot2
  have heq : (n + 2) + 1 = n + 3 := by omega
  have hnot3' : ¬ CanSubtract ((n + 2) + 1) (stateAt (n + 2)) := by
    rw [heq]
    exact hnot3
  have hcases := not_canSubtract_cases hnot3'
  rcases hcases with hsmall | hseen
  · have : False := by omega
    exact False.elim this
  · rw [hcand] at hseen
    exact hseen

/-- The historical blocker for the third addition must have appeared at an earlier
time `j ≤ n - 1`. -/
theorem permanent_high_third_addition_blocker_prior
    {H n : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hnH : H ≤ n)
    (hn6 : 6 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hnot3 : ¬ CanSubtract (n + 3) (stateAt (n + 2))) :
    a (n + 1) - 1 ∈ valuesThrough (n - 1) := by
  have hblocked := permanent_high_third_addition_must_be_blocked hhigh hnH hn6 hnot1 hnot2 hnot3
  rcases mem_valuesThrough_iff.mp hblocked with ⟨j, hj, hval⟩
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq : n + 1 + 1 = n + 2 := by omega
  rw [heq] at hstep2
  have hj_lt : j ≤ n - 1 := by
    by_cases hj_ge : n ≤ j
    · have hcases : j = n ∨ j = n + 1 ∨ j = n + 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · omega
      · omega
      · omega
    · omega
  exact mem_valuesThrough_iff.mpr ⟨j, hj_lt, hval⟩

/-- Any three-addition run in the permanent high regime forces the existence of
an earlier summit of height at least `3n`. -/
theorem permanent_high_third_addition_prior_summit
    {H n : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hnH : H ≤ n)
    (hn6 : 6 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hnot3 : ¬ CanSubtract (n + 3) (stateAt (n + 2))) :
    ∃ j, j ≤ n - 1 ∧ 3 * n ≤ a j ∧ a j = a n + n := by
  have hprior := permanent_high_third_addition_blocker_prior hhigh hnH hn6 hnot1 hnot2 hnot3
  rcases mem_valuesThrough_iff.mp hprior with ⟨j, hj, hval⟩
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hval_n := hhigh n hnH
  have heq : a j = a n + n := by omega
  have hge : 3 * n ≤ a j := by omega
  exact ⟨j, hj, hge, heq⟩

/-- In any segment without a prior summit of height `3n`, three consecutive
additions are strictly impossible: the third step is forced to subtract. -/
theorem permanent_high_no_three_consecutive_additions_under_summit_bound
    {H n : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hnH : H ≤ n)
    (hn6 : 6 ≤ n)
    (hsummit : ∀ j, j ≤ n - 1 → a j < 3 * n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1))) :
    CanSubtract (n + 3) (stateAt (n + 2)) := by
  by_cases hcan3 : CanSubtract (n + 3) (stateAt (n + 2))
  · exact hcan3
  · rcases permanent_high_third_addition_prior_summit hhigh hnH hn6 hnot1 hnot2 hcan3 with ⟨j, hj, hge, _heq⟩
    have hlt := hsummit j hj
    omega

/-! ### Part 4: Landing Value of Forced Subtraction -/

/-- When step `n + 3` subtracts after two additions, it lands precisely on `a n + n`. -/
theorem permanent_high_forced_subtraction_landing_value
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2))) :
    a (n + 3) = a n + n := by
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq2 : n + 1 + 1 = n + 2 := by omega
  rw [heq2] at hstep2
  have heq3 : (n + 2) + 1 = n + 3 := by omega
  have hcan3' : CanSubtract ((n + 2) + 1) (stateAt (n + 2)) := by
    rw [heq3]
    exact hcan3
  have hstep3 := a_succ_of_canSubtract hcan3'
  rw [heq3] at hstep3
  have hlt : n + 3 < a (n + 2) := hcan3.1
  omega

/-- The forced subtraction landing value is historically fresh. -/
theorem permanent_high_forced_subtraction_landing_fresh
    {n : Nat}
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2))) :
    a (n + 3) ∉ valuesThrough (n + 2) := by
  have heq3 : (n + 2) + 1 = n + 3 := by omega
  have hcan3' : CanSubtract ((n + 2) + 1) (stateAt (n + 2)) := by
    rw [heq3]
    exact hcan3
  have hstep3 := a_succ_of_canSubtract hcan3'
  rw [heq3] at hstep3
  rw [hstep3]
  exact hcan3.2

/-! ### Part 5: Oscillation and Recurrence -/

/-- In the permanent high regime, legal subtractions must occur infinitely often:
an eventual all-addition ray is impossible. -/
theorem permanent_high_infinitely_many_subtractions
    {H : Nat}
    (M : Nat) :
    ∃ n, max H M ≤ n ∧ CanSubtract (n + 1) (stateAt n) := by
  exact exists_canSubtract_of_ray (max H M)

/-- Grand Synthesis Theorem:
The Permanent High Regime is subject to bilateral structural rigidity:
- Subtractions require rapid height escalation (`3(k + 1)`, `4k + 7`, `5k + 12`).
- Additions rapidly elevate height (`3(n + 3) ≤ a (n + 2)` for `n ≥ 6`).
- Three additions require a prior summit `a j ≥ 3n` at `j ≤ n - 1`.
- Without a prior summit, step `n + 3` must subtract and land on fresh `a n + n`.
- Legal subtractions recur infinitely often, while `subSum` and `subCount` are
  permanently capped by the triangular capacity bounds. -/
theorem permanent_high_bilateral_rigidity
    {H : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m) :
    (∀ k, H ≤ k → CanSubtract (k + 1) (stateAt k) → 3 * (k + 1) ≤ a k) ∧
    (∀ k, H ≤ k → CanSubtract (k + 1) (stateAt k) → CanSubtract (k + 2) (stateAt (k + 1)) →
      4 * k + 7 ≤ a k) ∧
    (∀ k, H ≤ k → CanSubtract (k + 1) (stateAt k) → CanSubtract (k + 2) (stateAt (k + 1)) →
      CanSubtract (k + 3) (stateAt (k + 2)) → 5 * k + 12 ≤ a k) ∧
    (∀ n, H ≤ n → 6 ≤ n →
      ¬ CanSubtract (n + 1) (stateAt n) → ¬ CanSubtract (n + 2) (stateAt (n + 1)) →
      3 * (n + 3) ≤ a (n + 2)) ∧
    (∀ n, H ≤ n → 6 ≤ n → (∀ j, j ≤ n - 1 → a j < 3 * n) →
      ¬ CanSubtract (n + 1) (stateAt n) → ¬ CanSubtract (n + 2) (stateAt (n + 1)) →
      CanSubtract (n + 3) (stateAt (n + 2))) ∧
    (∀ n, H ≤ n → 2 * subSum n ≤ upperTri n - 2 * n) ∧
    (∀ n, H ≤ n → 2 * upperTri (subCount n) + 2 * n ≤ upperTri n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hcan
    exact permanent_high_subtraction_requires_three_times hhigh hk hcan
  · intro k hk hcan1 hcan2
    exact permanent_high_two_subtractions_requires_four_times hhigh hk hcan1 hcan2
  · intro k hk hcan1 hcan2 hcan3
    exact permanent_high_three_subtractions_requires_five_times hhigh hk hcan1 hcan2 hcan3
  · intro n hnH hn6 hnot1 hnot2
    exact permanent_high_two_additions_reach_three hhigh hnH hn6 hnot1 hnot2
  · intro n hnH hn6 hsummit hnot1 hnot2
    exact permanent_high_no_three_consecutive_additions_under_summit_bound hhigh hnH hn6 hsummit hnot1 hnot2
  · intro n hn
    exact permanent_high_subSum_upper_bound hhigh hn
  · intro n hn
    exact permanent_high_subCount_upper_bound hhigh hn

end Recaman
