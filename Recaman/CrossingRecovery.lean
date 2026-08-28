import Recaman.DebtCrossing
import Recaman.Undershoot

namespace Recaman

/-- Semantic state exposed when a debt-ending forced addition jumps strictly
over the target.  Unlike a normal node, the predecessor is below `target`;
the state therefore records the actual crossing time and the still-missing
target explicitly. -/
structure CrossingRecoveryInvariant
    (target horizon anchor n q r : Nat) : Prop where
  target_missing : target ∉ valuesThrough n
  forced_addition : ¬ CanSubtract (n + 1) (stateAt n)
  crossing : DebtCrossing target (a (n + 1)) n
  coordinates : CoordinatesAt (n + 1) q r
  crossing_before_horizon : n + 1 < horizon
  predecessor_lt_anchor : a n < anchor

/-- The unfilled distance in a strict crossing is positive and is no larger
than the addition step.  This is the genuine finite parameter supplied by a
crossing; the absolute target need not be below the crossing time. -/
theorem debtCrossing_gap_bounds
    {target value n : Nat} (hcross : DebtCrossing target value n) :
    0 < target - a n ∧ target - a n ≤ n + 1 := by
  rcases hcross with ⟨hpre, hpost, hvalue⟩
  constructor <;> omega

/-- At the post-addition endpoint of an actual strict crossing, the signed
coordinate potential is always strictly below the crossed target.  Thus the
endpoint is either in the negative half-space or in the target's undershoot
strip; the above-target potential case is impossible. -/
theorem debtCrossing_post_potential_lt_target
    {target value n q r : Nat}
    (hcross : DebtCrossing target value n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hcoord : CoordinatesAt (n + 1) q r) :
    potential q r < Int.ofNat target := by
  have hnext := a_succ_of_not_canSubtract hnot
  have hendpoint : value = a (n + 1) := by
    rw [hcross.2.2, hnext]
  have heq := hcoord.eqn
  have hrlt := hcoord.remainder_lt
  have hqpos : 0 < q := by
    cases q with
    | zero =>
        simp at heq
        rw [← hendpoint, hcross.2.2] at heq
        omega
    | succ q => omega
  have htriPos : 0 < upperTri q := upperTri_pos hqpos
  have hrPre : r ≤ a n := by
    rw [← hendpoint, hcross.2.2] at heq
    have hqone : 1 ≤ q := hqpos
    have hmul := Nat.mul_le_mul_left (n + 1) hqone
    simp only [Nat.mul_one] at hmul
    omega
  have hrTarget : r < target := Nat.lt_of_le_of_lt hrPre hcross.1
  unfold potential
  have hcast : Int.ofNat r < Int.ofNat target := Int.ofNat_lt.mpr hrTarget
  have htriCast : 0 ≤ Int.ofNat (upperTri q) :=
    Int.natCast_nonneg (upperTri q)
  omega

/-- A strict crossing whose absolute target is within the epoch theorem's
time range connects directly to the existing negative/undershoot machinery.
Either the post-state already has a coverage certificate, or the actual orbit
reaches a later negative state or a state with a local coverage certificate.

The extra bound is intentionally explicit: it is not supplied by a generic
debt crossing (and is in fact incompatible with diagonal-origin debt below). -/
theorem debtCrossing_epoch_recovery
    {target value n q r : Nat}
    (hcross : DebtCrossing target value n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hcoord : CoordinatesAt (n + 1) q r)
    (htime : target ≤ n + 2) :
    CoverageStep target (a (n + 1)) (n + 1) ∨
      ∃ t k s,
        n + 1 ≤ t ∧ CoordinatesAt t k s ∧
        (potential k s < 0 ∨ CoverageStep target (a t) t) := by
  have hbelow := debtCrossing_post_potential_lt_target hcross hnot hcoord
  by_cases hnegative : potential q r < 0
  · rcases negative_undershoot_cycle htime hcoord hnegative with
      hcoverage | ⟨t, k, s, hnt, htcoord, htresult⟩
    · exact Or.inl hcoverage
    · exact Or.inr ⟨t, k, s, by omega, htcoord, htresult⟩
  · have hnonnegative : 0 ≤ potential q r := by omega
    rcases undershoot_eventually_negative_or_localCoverage
        htime hcoord hnonnegative hbelow with
      ⟨t, k, s, hnt, htcoord, htresult⟩
    exact Or.inr ⟨t, k, s, hnt, htcoord, htresult⟩

/-- Exact semantic outcome of the strict-crossing debt branch.  If the target
was not already present, the formal anchor decrease can be paired with a
`CrossingRecoveryInvariant`; it cannot be mislabeled as a normal invariant. -/
theorem debtCrossing_enters_recovery
    {target horizon anchor value n : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbelow : a n < target) :
    (∃ t, a t = target) ∨
      ∃ q r,
        CrossingRecoveryInvariant target horizon anchor n q r ∧
        PhaseSearchProgress target
          ⟨horizon, a n, .normal, a n⟩
          ⟨horizon, anchor, .debt, n + 1⟩ := by
  by_cases hequal : target = value
  · exact Or.inl ⟨n + 1, by rw [hinv.first.1, hequal]⟩
  · by_cases hseen : target ∈ valuesThrough n
    · rcases mem_valuesThrough_iff.mp hseen with ⟨t, _, ht⟩
      exact Or.inl ⟨t, ht⟩
    · rcases exists_coordinatesAt (n := n + 1) (by omega) with ⟨q, r, hcoord⟩
      have hnext := a_succ_of_not_canSubtract hnot
      have hcross : DebtCrossing target (a (n + 1)) n := by
        refine ⟨hbelow, ?_, hnext⟩
        have hvalue : value = a (n + 1) := hinv.first.1.symm
        rw [← hvalue]
        exact Nat.lt_of_le_of_ne hinv.target_le hequal
      have hanchor : a n < anchor := by
        have hvalue : value = a n + (n + 1) :=
          hinv.first.1.symm.trans hnext
        exact Nat.lt_trans (by omega : a n < value) hinv.value_lt_anchor
      exact Or.inr ⟨q, r, {
        target_missing := hseen
        forced_addition := hnot
        crossing := hcross
        coordinates := hcoord
        crossing_before_horizon := hinv.firstTime_lt_horizon
        predecessor_lt_anchor := hanchor
      }, phaseSearch_exitDebt_of_anchorDrop hanchor⟩

/-- For debt originating at a diagonal target `horizon+1`, every strict
crossing occurs too early to satisfy the time hypothesis used by the current
negative/undershoot epoch theorems.  This is the precise interface obstruction
rather than a missing sign analysis. -/
theorem diagonalDebt_crossing_not_in_epoch_range
    {horizon n : Nat} (htime : n + 1 < horizon) :
    ¬ (horizon + 1 ≤ n + 2) := by
  omega

/-- The first concrete debt crossing enters the negative half-space. -/
theorem crossing_four_negative_example :
    DebtCrossing 4 (a 3) 2 ∧
      ¬ CanSubtract 3 (stateAt 2) ∧
      CoordinatesAt 3 2 0 ∧ potential 2 0 < 0 := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · unfold DebtCrossing
    exact ⟨by decide, by decide, by decide⟩
  exact ⟨by decide, by decide⟩

/-- Negative potential is not forced by crossing: the actual jump `2→7`
across target `4` lands in the nonnegative undershoot strip at level one. -/
theorem crossing_four_nonnegative_example :
    DebtCrossing 4 (a 5) 4 ∧
      ¬ CanSubtract 5 (stateAt 4) ∧
      CoordinatesAt 5 1 2 ∧
      0 ≤ potential 1 2 ∧ potential 1 2 < Int.ofNat 4 := by
  refine ⟨?_, by decide, ?_, by decide, by decide⟩
  · unfold DebtCrossing
    exact ⟨by decide, by decide, by decide⟩
  exact ⟨by decide, by decide⟩

end Recaman
