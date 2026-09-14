import Recaman.LeastTailMinimumDynamics
import Recaman.LeastTailLedgerMinimum
import Recaman.LeastTailLedgerProvenance
import Recaman.SubtractionLedger

namespace Recaman

/-! # Tail Downcrossing and Ledger Obstructions

Following the forced escape of the canonical tail minimum into quotient band
`q ≥ 2` (`tail_minimum_followup_quotient_ge_two`), this module formalizes the
dynamics and ledger constraints governing any subsequent return (downcrossing)
into the lower corridor `a n < 2n`.

Key results:
1. `subCount_mono`:
   Monotonicity of the subtraction counter: `a ≤ b → subCount a ≤ subCount b`.
2. `tail_descent_barrier`:
   Any step in the tail where `a k < k + 1 + a time` cannot subtract.
3. `tail_subtraction_lower_bound`:
   Any subtraction in the tail requires `k + 1 + a time ≤ a k`.
4. `tail_subtraction_result_gt_minimum`:
   Every subtraction in the tail lands strictly above `a time` (`a time < a (k + 1)`),
   because `a time` is already historical.
5. `tail_subtraction_prior_bound_sharp`:
   Sharpened prior height bound: `k + 2 + a time ≤ a k`.
6. `addition_step_cannot_cross_below_twice`:
   An addition step from `2k ≤ a k` can never cross below `2(k + 1)`.
7. `downcrossing_step_must_be_subtraction`:
   Every downcrossing from `2k ≤ a k` to `a (k + 1) < 2(k + 1)` MUST be a subtraction.
8. `downcrossing_prior_height_bounds`:
   At any downcrossing, the prior value satisfies `2k ≤ a k < 3k + 3`.
9. `downcrossing_subSum_increase`:
   The subtraction ledger strictly consumes the clock: `subSum (k + 1) = subSum k + k + 1`.
10. `downcrossing_subCount_increase`:
    `subCount (k + 1) = subCount k + 1`.
11. `tail_downcrossing_value_bounds`:
    `a time + 1 ≤ a (k + 1) < 2(k + 1)` and `k + 2 + a time ≤ a k < 3(k + 1)`.
12. `tail_downcrossing_ledger_corridor_reentry`:
    The re-entering state satisfies the two-sided ledger corridor.
13. `quotient_zero_ephemeral_in_tail`:
    Quotient band 0 cannot be occupied for two consecutive steps in the tail.
14. `no_double_subtraction_from_tail_escape`:
    Two consecutive subtractions cannot occur immediately from the escape state.
15. `least_missing_tail_downcrossing_ledger_obstruction`:
    Synthesis connecting `LeastMissingTarget` with downcrossing ledger constraints.
-/

/-- Monotonicity of the subtraction counter. -/
theorem subCount_mono {a b : Nat} (h : a ≤ b) : subCount a ≤ subCount b := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst this
      exact Nat.le_refl _
  | succ b ih =>
      by_cases hab : a ≤ b
      · have h1 := ih hab
        have h2 : subCount b ≤ subCount (b + 1) := by
          rw [subCount_succ]
          by_cases hcan : CanSubtract (b + 1) (stateAt b)
          · rw [if_pos hcan]
            omega
          · rw [if_neg hcan]
            omega
        exact Nat.le_trans h1 h2
      · have : a = b + 1 := by omega
        subst this
        exact Nat.le_refl _

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

/-- Any legal subtraction in the tail requires the prior value to be at least
`k + 1 + a time`. -/
theorem tail_subtraction_lower_bound
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : start ≤ k)
    (hcan : CanSubtract (k + 1) (stateAt k)) :
    k + 1 + a time ≤ a k := by
  by_cases hle : k + 1 + a time ≤ a k
  · exact hle
  · have hlt : a k < k + 1 + a time := by omega
    exact False.elim ((tail_descent_barrier hmin hk hlt) hcan)

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

/-- Sharpened prior height bound: any subtraction in the tail requires
`k + 2 + a time ≤ a k`. -/
theorem tail_subtraction_prior_bound_sharp
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : time ≤ k)
    (hcan : CanSubtract (k + 1) (stateAt k)) :
    k + 2 + a time ≤ a k := by
  have hgt := tail_subtraction_result_gt_minimum hmin hk hcan
  have hstep := a_succ_of_canSubtract hcan
  have hlt : k + 1 < a k := hcan.1
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

/-- At any downcrossing step, the prior value satisfies `2k ≤ a k < 3k + 3`. -/
theorem downcrossing_prior_height_bounds
    {k : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    2 * k ≤ a k ∧ a k < 3 * k + 3 := by
  have hsub := downcrossing_step_must_be_subtraction hk hhigh hlow
  have hstep := a_succ_of_canSubtract hsub
  have hlt : k + 1 < a k := hsub.1
  refine ⟨hhigh, by omega⟩

/-- At any downcrossing, the subtraction ledger strictly consumes the clock. -/
theorem downcrossing_subSum_increase
    {k : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    subSum (k + 1) = subSum k + (k + 1) := by
  have hsub := downcrossing_step_must_be_subtraction hk hhigh hlow
  rw [subSum_succ, if_pos hsub]

/-- At any downcrossing, the subtraction count increases by one. -/
theorem downcrossing_subCount_increase
    {k : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    subCount (k + 1) = subCount k + 1 := by
  have hsub := downcrossing_step_must_be_subtraction hk hhigh hlow
  rw [subCount_succ, if_pos hsub]

/-- Quantitative bounds on the downcrossing value and its prior state in the tail. -/
theorem tail_downcrossing_value_bounds
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : time ≤ k)
    (hk_pos : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    a time + 1 ≤ a (k + 1) ∧
    a (k + 1) < 2 * (k + 1) ∧
    k + 2 + a time ≤ a k ∧
    a k < 3 * (k + 1) := by
  have hsub := downcrossing_step_must_be_subtraction hk_pos hhigh hlow
  have hgt := tail_subtraction_result_gt_minimum hmin hk hsub
  have hprior := tail_subtraction_prior_bound_sharp hmin hk hsub
  have hstep := a_succ_of_canSubtract hsub
  have hlt : k + 1 < a k := hsub.1
  refine ⟨by omega, hlow, hprior, by omega⟩

/-- The downcrossing landing value satisfies the two-sided ledger corridor. -/
theorem tail_downcrossing_ledger_corridor_reentry
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : time ≤ k)
    (hk_pos : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
    upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1) := by
  have hbounds := tail_downcrossing_value_bounds hmin hk hk_pos hhigh hlow
  have hledger := ledger_identity (k + 1)
  constructor
  · omega
  · omega

/-- Quotient band 0 is ephemeral in the tail: any visit to band 0 forces the
next step to add and immediately enter quotient band `q ≥ 1`. -/
theorem quotient_zero_ephemeral_in_tail
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : start ≤ k)
    (hzero : a k < k) :
    ¬ CanSubtract (k + 1) (stateAt k) ∧
    k + 1 ≤ a (k + 1) := by
  have hbarrier : a k < k + 1 + a time := by omega
  have hnot := tail_descent_barrier hmin hk hbarrier
  have hstep := a_succ_of_not_canSubtract hnot
  refine ⟨hnot, by omega⟩

/-- Two consecutive subtractions cannot occur immediately from the escape state
at `time + 2`. -/
theorem no_double_subtraction_from_tail_escape
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    ¬ (CanSubtract (time + 3) (stateAt (time + 2)) ∧
       CanSubtract (time + 4) (stateAt (time + 3))) := by
  intro ⟨h1, h2⟩
  have hforced := tail_minimum_step3_subtraction_forces_step4_addition hmin h1
  exact hforced h2

/-- Cumulative `subSum` growth after any tail downcrossing:
the subtraction ledger at `k + 1` exceeds `subSum time + k + 1`. -/
theorem tail_downcrossing_subSum_ge_time
    {target start time firstTime k : Nat}
    (_hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : time ≤ k)
    (hk_pos : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    subSum time + (k + 1) ≤ subSum (k + 1) := by
  have hinc := downcrossing_subSum_increase hk_pos hhigh hlow
  have hmono := subSum_mono hk
  omega

/-- Cumulative `subCount` growth after any tail downcrossing:
the subtraction count at `k + 1` strictly exceeds `subCount time`. -/
theorem tail_downcrossing_subCount_gt_time
    {target start time firstTime k : Nat}
    (_hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk : time ≤ k)
    (hk_pos : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    subCount time + 1 ≤ subCount (k + 1) := by
  have hinc := downcrossing_subCount_increase hk_pos hhigh hlow
  have hmono := subCount_mono hk
  omega

/-- Synthesis theorem: for a hypothetical least missing target, every downcrossing
step from above `2k` back into the corridor is a certified subtraction that
advances the subtraction ledger, lands strictly above `a time`, and satisfies
the corridor bounds. -/
theorem least_missing_tail_downcrossing_ledger_obstruction
    {target start time firstTime q r k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (_hcoord : CoordinatesAt time q r)
    (hk : time ≤ k)
    (hk_pos : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    CanSubtract (k + 1) (stateAt k) ∧
    a time + 1 ≤ a (k + 1) ∧
    subSum time + (k + 1) ≤ subSum (k + 1) ∧
    subCount time + 1 ≤ subCount (k + 1) ∧
    2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
    upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1) := by
  have hsub := downcrossing_step_must_be_subtraction hk_pos hhigh hlow
  have hbounds := tail_downcrossing_value_bounds hmin hk hk_pos hhigh hlow
  have hsum := tail_downcrossing_subSum_ge_time hmin hk hk_pos hhigh hlow
  have hcount := tail_downcrossing_subCount_gt_time hmin hk hk_pos hhigh hlow
  have hledger := tail_downcrossing_ledger_corridor_reentry hmin hk hk_pos hhigh hlow
  exact ⟨hsub, hbounds.1, hsum, hcount, hledger.1, hledger.2⟩

end Recaman
