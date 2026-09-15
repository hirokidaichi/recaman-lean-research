import Recaman.TailDowncrossingLedger
import Recaman.LeastTailMinimumDynamics
import Recaman.LeastTailLedgerMinimum
import Recaman.SubtractionLedger

namespace Recaman

/-! # Tail Downcrossing Dichotomy and Grand Synthesis

Following the forced escape of the canonical tail minimum into quotient band
`q ≥ 2` (`tail_minimum_followup_quotient_ge_two`), this module establishes the
grand dynamical dichotomy governing the orbit's subsequent evolution:

Either:
1. **Eventual Permanent High Regime**:
   The orbit never downcrosses below `2n` after some horizon `H`:
   `∀ n ≥ H, 2n ≤ a n`.
   In this regime:
   - Every subtraction step requires `3(k + 1) ≤ a k` (quotient band `q ≥ 3`).
   - Any state with `a k < 3(k + 1)` is strictly forced to ADD (`¬ CanSubtract`).
   - The subtraction ledger mass is permanently capped:
     `2 * subSum n ≤ upperTri n - 2n`.
   - The subtraction count is permanently capped:
     `2 * upperTri (subCount n) + 2n ≤ upperTri n`.
   - Addition steps must dominate with positive density.

Or:
2. **Downcrossing Dynamics**:
   Any excursion that does not stay permanently high must perform a certified downcrossing:
   - Every downcrossing step is a certified subtraction (`CanSubtract u`).
   - Every downcrossing lands on a fresh, historically unique value:
     `a u₁ ≠ a u₂` for all `u₁ < u₂`.
   - Every downcrossing deposits its full clock into the subtraction ledger:
     `k + 1 ≤ subSum (k + 1)`.
   - If downcrossings recur indefinitely, `subSum` grows unboundedly:
     `∀ B, ∃ u, B < subSum u`.
   - The two-sided ledger corridor is revisited.
-/

/-! ### Part 1: The Permanent High Regime -/

/-- In the permanent high regime, any subtraction requires the prior value to be
at least three times the next clock: `3(k + 1) ≤ a k`. -/
theorem permanent_high_subtraction_requires_three_times
    {H k : Nat}
    (hhigh : ∀ n, H ≤ n → 2 * n ≤ a n)
    (hk : H ≤ k)
    (hcan : CanSubtract (k + 1) (stateAt k)) :
    3 * (k + 1) ≤ a k := by
  have hnext_high := hhigh (k + 1) (by omega)
  have hstep := a_succ_of_canSubtract hcan
  have hlt : k + 1 < a k := hcan.1
  omega

/-- In the permanent high regime, any state with `a k < 3(k + 1)` cannot subtract:
it is strictly forced to add. -/
theorem permanent_high_not_canSubtract_of_lt_three
    {H k : Nat}
    (hhigh : ∀ n, H ≤ n → 2 * n ≤ a n)
    (hk : H ≤ k)
    (hlt : a k < 3 * (k + 1)) :
    ¬ CanSubtract (k + 1) (stateAt k) := by
  intro hcan
  have hge := permanent_high_subtraction_requires_three_times hhigh hk hcan
  omega

/-- In the permanent high regime, forced additions in `q = 2` expand the value
to at least `3k + 1`. -/
theorem permanent_high_forced_addition_value
    {H k : Nat}
    (hhigh : ∀ n, H ≤ n → 2 * n ≤ a n)
    (hk : H ≤ k)
    (hlt : a k < 3 * (k + 1)) :
    3 * k + 1 ≤ a (k + 1) := by
  have hnot := permanent_high_not_canSubtract_of_lt_three hhigh hk hlt
  have hstep := a_succ_of_not_canSubtract hnot
  have hcur := hhigh k hk
  omega

/-- In the permanent high regime, the subtraction ledger mass is permanently
capped by `(upperTri n - 2n) / 2`. -/
theorem permanent_high_subSum_upper_bound
    {H n : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hn : H ≤ n) :
    2 * subSum n ≤ upperTri n - 2 * n := by
  have hledger := ledger_identity n
  have hval := hhigh n hn
  have hsum_le : 2 * n + 2 * subSum n ≤ upperTri n := by omega
  omega

/-- In the permanent high regime, the subtraction count is permanently capped
by the triangular capacity inequality `2 * upperTri (subCount n) + 2n ≤ upperTri n`. -/
theorem permanent_high_subCount_upper_bound
    {H n : Nat}
    (hhigh : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hn : H ≤ n) :
    2 * upperTri (subCount n) + 2 * n ≤ upperTri n := by
  have hledger := ledger_identity n
  have hval := hhigh n hn
  have htri_count := upperTri_subCount_le_subSum n
  omega

/-- An orbit segment without downcrossings maintains `2n ≤ a n` by induction. -/
theorem permanent_high_of_no_downcrossing
    {H : Nat}
    (hbase : 2 * H ≤ a H)
    (hstep : ∀ k, H ≤ k → 2 * k ≤ a k → 2 * (k + 1) ≤ a (k + 1)) :
    ∀ n, H ≤ n → 2 * n ≤ a n := by
  intro n hn
  have hind : ∀ d, 2 * (H + d) ≤ a (H + d) := by
    intro d
    induction d with
    | zero =>
        simpa using hbase
    | succ d ih =>
        have hge : H ≤ H + d := by omega
        have hnext := hstep (H + d) hge ih
        have heq : H + d + 1 = H + (d + 1) := by omega
        rw [← heq]
        exact hnext
  have heq : n = H + (n - H) := by omega
  rw [heq]
  exact hind (n - H)

/-! ### Part 2: Recurrent Downcrossing Dynamics -/

/-- Every downcrossing step deposits its full clock into the subtraction ledger,
so `k + 1 ≤ subSum (k + 1)`. -/
theorem downcrossing_subSum_ge_clock
    {k : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    k + 1 ≤ subSum (k + 1) := by
  have hinc := downcrossing_subSum_increase hk hhigh hlow
  omega

/-- Every downcrossing value is historically fresh: it has never appeared at
any earlier time. -/
theorem downcrossing_value_fresh
    {k earlier : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1))
    (hearlier : earlier ≤ k) :
    a (k + 1) ≠ a earlier := by
  have hsub := downcrossing_step_must_be_subtraction hk hhigh hlow
  have hfresh : a (k + 1) ∉ valuesThrough k := by
    have hstep := a_succ_of_canSubtract hsub
    rw [hstep]
    exact hsub.2
  intro heq
  have hseen : a earlier ∈ valuesThrough k :=
    mem_valuesThrough_iff.mpr ⟨earlier, hearlier, rfl⟩
  rw [heq] at hfresh
  exact hfresh hseen

/-- Two downcrossings at different times produce distinct orbit values. -/
theorem downcrossing_values_distinct
    {k₁ k₂ : Nat}
    (_hk₁ : 1 ≤ k₁)
    (_hhigh₁ : 2 * k₁ ≤ a k₁)
    (_hlow₁ : a (k₁ + 1) < 2 * (k₁ + 1))
    (hk₂ : 1 ≤ k₂)
    (hhigh₂ : 2 * k₂ ≤ a k₂)
    (hlow₂ : a (k₂ + 1) < 2 * (k₂ + 1))
    (hne : k₁ + 1 < k₂ + 1) :
    a (k₁ + 1) ≠ a (k₂ + 1) := by
  have hle : k₁ + 1 ≤ k₂ := by omega
  have hfresh := downcrossing_value_fresh hk₂ hhigh₂ hlow₂ hle
  exact hfresh.symm

/-- If downcrossings occur at or after arbitrary cutoffs, the subtraction ledger
mass is unbounded. -/
theorem recurrent_downcrossing_subSum_unbounded
    (hrec : ∀ H, ∃ k, H ≤ k ∧ 1 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1))
    (B : Nat) :
    ∃ u, B < subSum u := by
  rcases hrec (B + 1) with ⟨k, _hH, hk_pos, hhigh, hlow⟩
  have hclock := downcrossing_subSum_ge_clock hk_pos hhigh hlow
  refine ⟨k + 1, by omega⟩

/-! ### Part 3: The Grand Downcrossing Dichotomy -/

/-- At any horizon `H` where `2H ≤ a H`, the orbit either stays high permanently
from `H` onward, or performs a downcrossing at or after `H`. -/
theorem exists_permanent_high_or_downcrossing
    {H : Nat} (hH : 2 * H ≤ a H) :
    (∀ n, H ≤ n → 2 * n ≤ a n) ∨
    (∃ k, H ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) := by
  by_cases hdown : ∃ k, H ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)
  · exact Or.inr hdown
  · left
    have hstep : ∀ k, H ≤ k → 2 * k ≤ a k → 2 * (k + 1) ≤ a (k + 1) := by
      intro k hk hhigh
      by_cases hle : 2 * (k + 1) ≤ a (k + 1)
      · exact hle
      · have hlow : a (k + 1) < 2 * (k + 1) := by omega
        exact False.elim (hdown ⟨k, hk, hhigh, hlow⟩)
    exact permanent_high_of_no_downcrossing hH hstep

/-- The canonical tail downcrossing dichotomy:
From the certified escape state at `time + 2`, the orbit either stays high permanently
(`∀ n ≥ time + 2, 2n ≤ a n`), or performs at least one downcrossing step. -/
theorem tail_escape_downcrossing_dichotomy
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    (∀ n, time + 2 ≤ n → 2 * n ≤ a n) ∨
    (∃ k, time + 2 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) := by
  have hH : 2 * (time + 2) ≤ a (time + 2) := by
    have := tail_minimum_followup_gt_twice_time hmin
    omega
  exact exists_permanent_high_or_downcrossing hH

/-- Grand Synthesis Theorem:
In a hypothetical least missing target, either the tail permanently stays high
with capped subtraction ledger and forced additions on `a k < 3(k + 1)`,
or it performs a certified downcrossing back into the corridor. -/
theorem least_missing_tail_grand_dichotomy
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time firstTime,
      PermanentTailMinimumCertificate target start time firstTime ∧
      ((∀ n, time + 2 ≤ n → 2 * n ≤ a n ∧ 2 * subSum n ≤ upperTri n - 2 * n) ∨
       (∃ k, time + 2 ≤ k ∧
          CanSubtract (k + 1) (stateAt k) ∧
          a time + 1 ≤ a (k + 1) ∧
          a (k + 1) < 2 * (k + 1) ∧
          2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
          upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1))) := by
  rcases h.exists_leastTailLedgerMinimum with
    ⟨start, time, firstTime, _q, _r, _htail, _hleast, hmin,
     _hcoord, _htargetMin, _hminUpper, _hminTwice,
     _hq, _hpot, _hledgLower, _hledgUpper⟩
  refine ⟨start, time, firstTime, hmin, ?_⟩
  rcases tail_escape_downcrossing_dichotomy hmin with hhigh | ⟨k, hk, hhigh_k, hlow_k⟩
  · left
    intro n hn
    have hval := hhigh n hn
    have hcap := permanent_high_subSum_upper_bound hhigh hn
    exact ⟨hval, hcap⟩
  · right
    have hk_pos : 1 ≤ k := by omega
    have hk_time : time ≤ k := by omega
    have hsub := downcrossing_step_must_be_subtraction hk_pos hhigh_k hlow_k
    have hbounds := tail_downcrossing_value_bounds hmin hk_time hk_pos hhigh_k hlow_k
    have hledger := tail_downcrossing_ledger_corridor_reentry hmin hk_time hk_pos hhigh_k hlow_k
    exact ⟨k, hk, hsub, hbounds.1, hbounds.2.1, hledger.1, hledger.2⟩

end Recaman
