import Recaman.TwoSSTightDisjoint
import Recaman.TwoSSAvoidTight
import Recaman.TenGateT6Resolution
import Recaman.PermanentAboveTail
import Recaman.ActualDescent
import Recaman.CoordinateDynamics
import Recaman.History
import Recaman.OrbitBounds
import Recaman.SubtractionLedger
import Recaman.LagElevenPeriodic
import Recaman.DebtInvariant

/-!
# AuditSalvage

Lemmas salvaged on 2026-09-15 from modules deleted after the audit E-343
(docs/AUDIT_GRAND_SYNTHESIS_2026-09-15.md). They are local facts about the
actual orbit or about tight avoiding subsets; none of them proves a regime,
a branch elimination, or a capacity inequality.

Each section below names the original source module. Theorem names and
namespaces are preserved exactly, and proofs are copied verbatim; only the
helpers each salvaged lemma actually depends on were carried along.

Sections:
- A. `Recaman/TwelveGateT6Unconditional.lean`
- B. `Recaman/LeastTailMinimumDynamics.lean`
- C. `Recaman/TailDowncrossingLedger.lean`
- D. `Recaman/CorridorDensityObstruction.lean`
- E. `Recaman/PermanentHighBlockerCapacity.lean`
- F. `Recaman/PermanentHighRigidity.lean`
-/

namespace Recaman.TwelveGateT6Unconditional

open TwoSSTightDisjoint TwoSSAvoidTight TenGateT6Resolution

/-! ### A. From `Recaman/TwelveGateT6Unconditional.lean`

A tight avoiding subset of size at most 2 whose lags all lie in `{3, 7}` and
whose period exceeds 7 must have every lag equal to 3: a lag 7 window alone
already covers at least three subtraction phases
(`lag_seven_neighborhood_ge_three`), which is more than the subset can be
tight against. -/

/-- In any periodic word, any tight avoiding subset of size ≤ 2 with non-wrapping P2 windows
and lags ≤ 7 has all lags equal to 3. -/
theorem tight_avoiding_le_two_all_lag_three_general (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p) :
    ∀ u ∈ A, lag u = 3 := by
  intro u hu
  have hcases := hlags u hu
  rcases hcases with h3 | h7
  · exact h3
  · exfalso
    have hPu := hP_A u hu
    rw [h7] at hPu
    have hN_ge3 := lag_seven_neighborhood_ge_three e p hp hper u lag h7 hp_gt hPu
    have hsub : neighborhood e p [u] lag ⊆ neighborhood e p A lag := by
      unfold neighborhood
      intro s hs
      rw [List.mem_filter] at hs ⊢
      refine ⟨hs.1, ?_⟩
      rw [isCoveredBySubset_iff] at hs ⊢
      obtain ⟨w, hw, hcov⟩ := hs.2
      simp only [List.mem_singleton] at hw
      subst w
      exact ⟨u, hu, hcov⟩
    have hN_le := (neighborhood_nodup e p [u] lag).length_le_of_subset hsub
    omega

end Recaman.TwelveGateT6Unconditional

namespace Recaman

/-! ### B. From `Recaman/LeastTailMinimumDynamics.lean`

Projections and arithmetic on `PermanentTailMinimumCertificate`: the value
two steps after the certified tail minimum, and the fact that a subtraction
at step `time + 3` forces an addition at step `time + 4`. -/

/-- Value at `time + 2` increases by `2 * time + 3` over `a time`. -/
theorem tail_minimum_followup_value
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    a (time + 2) = a time + 2 * time + 3 := by
  have h1 := hmin.first_addition
  have h2 : a (time + 2) = a (time + 1) + (time + 2) := by
    have hstep := a_succ_of_not_canSubtract hmin.followup_forced
    have heq : time + 1 + 1 = time + 2 := by omega
    simpa [heq] using hstep
  omega

/-- If step `time + 3` is a subtraction, step `time + 4` is forced to add
to preserve the tail minimum. -/
theorem tail_minimum_step3_subtraction_forces_step4_addition
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hsub3 : CanSubtract (time + 3) (stateAt (time + 2))) :
    ¬ CanSubtract (time + 4) (stateAt (time + 3)) := by
  intro hcan4
  have hval2 := tail_minimum_followup_value hmin
  have h3 : time + 2 + 1 = time + 3 := by omega
  have h4 : time + 3 + 1 = time + 4 := by omega
  have hstep3 := a_succ_of_canSubtract hsub3
  rw [h3] at hstep3
  have hval3 : a (time + 3) = a time + time := by omega
  have hstep4 := a_succ_of_canSubtract hcan4
  rw [h4] at hstep4
  have hcan4_pos : time + 4 < a (time + 3) := hcan4.1
  have hfour_lt : 4 < a time := by omega
  have hval4_eq : a (time + 4) = a time - 4 := by omega
  have htime4 : start ≤ time + 4 := by
    have hstart := hmin.minimum.start_le_time
    omega
  have hmin4 := hmin.minimum.minimal (time + 4) htime4
  omega

/-! ### C. From `Recaman/TailDowncrossingLedger.lean`

Single-step facts about the actual orbit: an addition from at or above `2k`
stays at or above `2(k + 1)`, so any downcrossing is a subtraction; and in a
certified tail, a subtraction needs enough height and lands strictly above
the tail minimum because that value is already historical. -/

/-- The tail descent barrier: any step where the value is below `k + 1 + a time`
is strictly prevented from subtracting, as doing so would contradict the tail minimum. -/
theorem tail_descent_barrier
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : start ≤ k)
    (hval : a k < k + 1 + a time) :
    ¬ CanSubtract (k + 1) (stateAt k) := by
  intro hcan
  have hstep := a_succ_of_canSubtract hcan
  have hlt : k + 1 < a k := hcan.1
  have hnextTime : start ≤ k + 1 := by omega
  have hminimal := hmin.minimum.minimal (k + 1) hnextTime
  omega

/-- A legal subtraction in the tail lands at or above `a time`. -/
theorem tail_subtraction_result_ge_minimum
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : start ≤ k)
    (hcan : CanSubtract (k + 1) (stateAt k)) :
    a time ≤ a (k + 1) := by
  have hstep := a_succ_of_canSubtract hcan
  have hnextTime : start ≤ k + 1 := by omega
  exact hmin.minimum.minimal (k + 1) hnextTime

/-- Every subtraction in the tail lands strictly above `a time`, because `a time`
is already historical and cannot be revisited by a legal subtraction. -/
theorem tail_subtraction_result_gt_minimum
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : time ≤ k)
    (hcan : CanSubtract (k + 1) (stateAt k)) :
    a time < a (k + 1) := by
  have hstart_le_time := hmin.minimum.start_le_time
  have hstart_le_k : start ≤ k := by omega
  have _hge := tail_subtraction_result_ge_minimum hmin hstart_le_k hcan
  have hstep := a_succ_of_canSubtract hcan
  have hfresh : a (k + 1) ∉ valuesThrough k := by
    rw [hstep]
    exact hcan.2
  have htime_seen : a time ∈ valuesThrough k := by
    apply mem_valuesThrough_iff.mpr
    exact ⟨time, hk, rfl⟩
  by_cases heq : a (k + 1) = a time
  · rw [heq] at hfresh
    exact False.elim (hfresh htime_seen)
  · have hlt : k + 1 < a k := hcan.1
    omega

/-- An addition step can never cross from above or at `2k` to below `2(k + 1)`. -/
theorem addition_step_cannot_cross_below_twice
    {k : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hadd : ¬ CanSubtract (k + 1) (stateAt k)) :
    2 * (k + 1) ≤ a (k + 1) := by
  have hstep := a_succ_of_not_canSubtract hadd
  omega

/-- Every downcrossing from `2k ≤ a k` to `a (k + 1) < 2(k + 1)` must be
a subtraction step. -/
theorem downcrossing_step_must_be_subtraction
    {k : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    CanSubtract (k + 1) (stateAt k) := by
  by_cases hcan : CanSubtract (k + 1) (stateAt k)
  · exact hcan
  · have hhigh_next := addition_step_cannot_cross_below_twice hk hhigh hcan
    omega

end Recaman

namespace Recaman.CorridorDensityObstruction

open Recaman

/-! ### D. From `Recaman/CorridorDensityObstruction.lean`

Two arithmetic consequences of the ledger identity for the actual orbit at a
single time: a linear lower bound on `subCount` from the upper corridor
inequality, and a quadratic upper bound from the lower one. Both rest on
`two_mul_upperTri`, `subSum_le_mul_subCount`, and
`upperTri_subCount_le_subSum`, which live in kept modules. -/

/-- In any ledger corridor satisfying `upperTri time < 2 * subSum time + 2 * time`,
the number of subtractions satisfies a linear lower bound: `time ≤ 4 * subCount time + 2`. -/
theorem subCount_lower_bound_of_ledger_corridor (time : Nat) (_htime : 0 < time)
    (hledger : upperTri time < 2 * subSum time + 2 * time) :
    time ≤ 4 * subCount time + 2 := by
  have htri := two_mul_upperTri time
  have hsum_le := subSum_le_mul_subCount time
  have h1 : 2 * upperTri time < 4 * subSum time + 4 * time := by omega
  rw [htri] at h1
  have hcomm : 4 * (time * subCount time) = time * (4 * subCount time) := by
    rw [← Nat.mul_assoc 4 time (subCount time), Nat.mul_comm 4 time, Nat.mul_assoc time 4 (subCount time)]
  have h2 : 4 * subSum time ≤ time * (4 * subCount time) := by
    calc
      4 * subSum time ≤ 4 * (time * subCount time) := Nat.mul_le_mul_left 4 hsum_le
      _ = time * (4 * subCount time) := hcomm
  have h3 : time * (time + 1) < time * (4 * subCount time + 4) := by
    have hsum4 : 4 * subSum time + 4 * time ≤ time * (4 * subCount time) + time * 4 := by
      have : 4 * time = time * 4 := by rw [Nat.mul_comm]
      rw [this]
      exact Nat.add_le_add h2 (Nat.le_refl (time * 4))
    have hdistr : time * (4 * subCount time) + time * 4 = time * (4 * subCount time + 4) := by
      rw [← Nat.mul_add]
    calc
      time * (time + 1) < 4 * subSum time + 4 * time := h1
      _ ≤ time * (4 * subCount time) + time * 4 := hsum4
      _ = time * (4 * subCount time + 4) := hdistr
  have hcancel : time + 1 < 4 * subCount time + 4 :=
    Nat.lt_of_mul_lt_mul_left h3
  omega

/-- In any ledger corridor where `2 * subSum time < upperTri time`,
the number of subtractions satisfies a quadratic upper bound:
`2 * (subCount time * (subCount time + 1)) < time * (time + 1)`. -/
theorem subCount_upper_bound_of_ledger_corridor (time : Nat)
    (hlower : 2 * subSum time < upperTri time) :
    2 * (subCount time * (subCount time + 1)) < time * (time + 1) := by
  have htri_time := two_mul_upperTri time
  have htri_sub := two_mul_upperTri (subCount time)
  have hsub_tri := upperTri_subCount_le_subSum time
  have h1 : 2 * upperTri (subCount time) ≤ 2 * subSum time := by omega
  have h2 : 2 * (2 * upperTri (subCount time)) < 2 * upperTri time := by omega
  rw [htri_sub] at h2
  rw [htri_time] at h2
  exact h2

end Recaman.CorridorDensityObstruction

namespace Recaman

/-! ### E. From `Recaman/PermanentHighBlockerCapacity.lean`

A pigeonhole fact about the actual orbit at a single high step: the `n`
distinct toothcomb candidates `a n + n - m` (`m < n`) cannot all be blocked
by the `n - 1` nonzero-index historical values, because index `0` never
blocks a positive candidate. -/

/-- The toothcomb candidate cannot equal 0 when 1 ≤ n and 2n ≤ a n. -/
theorem toothcomb_candidate_pos
    {n m : Nat} (hm : m < n) (hn_high : 2 * n ≤ a n) :
    0 < a n + n - m := by
  omega

/-- Base value at step 0 is 0. -/
theorem a_zero_eq_zero : a 0 = 0 := rfl

/-- Historical blocker index can never be 0. -/
theorem toothcomb_blocker_ne_zero
    {n m j : Nat} (hm : m < n) (hn_high : 2 * n ≤ a n)
    (hblock : a j = a n + n - m) :
    j ≠ 0 := by
  intro hj
  rw [hj, a_zero_eq_zero] at hblock
  have hpos := toothcomb_candidate_pos hm hn_high
  omega

/-- The list of toothcomb candidates for m < n has length n. -/
theorem toothcomb_candidates_length (n : Nat) (an : Nat) :
    ((List.range n).map (fun m => an + n - m)).length = n := by
  simp

/-- The list of toothcomb candidates for m < n has no duplicates. -/
theorem toothcomb_candidates_nodup (n : Nat) (an : Nat) :
    ((List.range n).map (fun m => an + n - m)).Nodup := by
  refine LagElevenPeriodic.nodup_map_of_inj List.nodup_range ?_
  intro x y hx hy heq
  rw [List.mem_range] at hx hy
  omega

/-- Candidate list membership characterization. -/
theorem mem_toothcomb_candidates_iff {n an x : Nat} :
    x ∈ (List.range n).map (fun m => an + n - m) ↔
    ∃ m, m < n ∧ x = an + n - m := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · intro ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.symm⟩
  · intro ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.symm⟩

/-- Historical non-zero values list has length n - 1. -/
theorem historical_nonzero_values_length (n : Nat) :
    ((List.range (n - 1)).map (fun i => a (i + 1))).length = n - 1 := by
  simp

/-- Blocker capacity impossibility:
It is mathematically impossible for all n toothcomb candidates to be
blocked by history j < n. -/
theorem toothcomb_not_all_blocked_by_history
    {n : Nat} (hn : 1 ≤ n) (hn_high : 2 * n ≤ a n)
    (h_all_blocked : ∀ m, m < n → ∃ j, j < n ∧ a j = a n + n - m) :
    False := by
  let cand_list := (List.range n).map (fun m => a n + n - m)
  let hist_list := (List.range (n - 1)).map (fun i => a (i + 1))
  have hsubset : cand_list ⊆ hist_list := by
    intro x hx
    rcases mem_toothcomb_candidates_iff.mp hx with ⟨m, hm, hx_eq⟩
    rcases h_all_blocked m hm with ⟨j, hj, hj_eq⟩
    have hj_ne : j ≠ 0 := toothcomb_blocker_ne_zero hm hn_high hj_eq
    have hj_lt : j - 1 < n - 1 := by omega
    rw [List.mem_map]
    refine ⟨j - 1, List.mem_range.mpr hj_lt, ?_⟩
    have : j - 1 + 1 = j := by omega
    rw [this, hj_eq, ← hx_eq]
  have hnodup := toothcomb_candidates_nodup n (a n)
  have hle := List.Nodup.length_le_of_subset hnodup hsubset
  have hlen1 : cand_list.length = n := toothcomb_candidates_length n (a n)
  have hlen2 : hist_list.length = n - 1 := historical_nonzero_values_length n
  rw [hlen1, hlen2] at hle
  omega

/-! ### F. From `Recaman/PermanentHighRigidity.lean`

Local facts about three consecutive additions of the actual orbit under a
pointwise hypothesis `∀ m ≥ H, 2m ≤ a m` supplied as an argument: after two
additions the height is at least `3(n + 3)`, so a third addition can only be
caused by the candidate `a (n + 1) - 1` already being in history, and that
blocker must sit at an index `j ≤ n - 1` with `a j = a n + n ≥ 3n`. -/

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

/-- The subtraction candidate after two additions satisfies `a (n + 2) - (n + 3) = a (n + 1) - 1`. -/
theorem permanent_high_candidate_after_two_additions
    {n : Nat}
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1))) :
    a (n + 2) - (n + 3) = a (n + 1) - 1 := by
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq : n + 1 + 1 = n + 2 := by omega
  rw [heq] at hstep2
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

end Recaman
