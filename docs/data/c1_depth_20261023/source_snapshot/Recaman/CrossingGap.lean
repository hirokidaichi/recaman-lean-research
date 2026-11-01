import Recaman.CrossingRecovery
import Recaman.InitialRegion

namespace Recaman

/-- A target-ready state reached after waiting until the absolute clock has
caught the target.  This is the semantic replacement for trying to feed the
small crossing gap itself to an epoch theorem about the absolute target. -/
structure CrossingCatchup
    (target horizon anchor t q r f : Nat) : Prop where
  time_eq : t = target - 1 ∨ t = target
  target_in_epoch_range : target ≤ t + 1
  target_le_value : target ≤ a t
  coordinates : CoordinatesAt t q r
  first_time_le : f ≤ t
  first : FirstAt a (a t) f

/-- A nonnegative coordinate level at or above the target gives coverage as
soon as both time and quotient are positive.  The regular epoch records that
level in history; positive quotient makes the recorded level strictly smaller
than the starting value. -/
theorem positiveQuotient_potential_aboveTarget_gives_coverageStep
    {target n q r : Nat}
    (hn : 0 < n)
    (hq : 0 < q)
    (htime : target ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (habove : Int.ofNat target ≤ potential q r) :
    CoverageStep target (a n) n := by
  have hnonnegative : 0 ≤ potential q r := by
    have htargetNonnegative : 0 ≤ Int.ofNat target :=
      Int.natCast_nonneg target
    omega
  let g := r - upperTri q
  have htri : upperTri q ≤ r :=
    (potential_nonnegative_iff q r).mp hnonnegative
  have hpotential : potential q r = Int.ofNat g := by
    apply (potential_eq_ofNat_iff q r g).mpr
    simp only [g]
    omega
  have htargetg : target ≤ g := by
    rw [hpotential] at habove
    exact Int.ofNat_le.mp habove
  rcases nonnegative_epoch_records_level_or_coverage
      htime hcoord hpotential with hcoverage | ⟨t, _, _, hseen⟩
  · exact hcoverage
  · rcases history_member_has_firstAt hseen with ⟨fg, _, hfirst⟩
    have heq := hcoord.eqn
    have hgler : g ≤ r := by
      simp only [g]
      omega
    have hmulpos : 0 < n * q := Nat.mul_pos hn hq
    have hglt : g < a n := by omega
    exact Or.inr ⟨g, fg, htargetg, hfirst, hglt⟩

/-- Every target-ready state is accepted by the existing epoch machinery.
Above-target nonnegative potential gives immediate coverage; negative and
undershoot potential use their respective finite epoch theorems. -/
theorem crossingCatchup_epoch_frontier
    {target horizon anchor t q r f : Nat}
    (htarget : 0 < target)
    (hcatch : CrossingCatchup target horizon anchor t q r f) :
    CoverageStep target (a t) t ∨
      ∃ u k s,
        t ≤ u ∧ CoordinatesAt u k s ∧
        (potential k s < 0 ∨ CoverageStep target (a u) u) := by
  have htpos : 0 < t := by
    cases t with
    | zero =>
        have hle := hcatch.target_le_value
        have hzero : a 0 = 0 := rfl
        rw [hzero] at hle
        omega
    | succ t => omega
  have hqpos : 0 < q := by
    cases q with
    | zero =>
        have heq := hcatch.coordinates.eqn
        have hrlt := hcatch.coordinates.remainder_lt
        have htargetValue := hcatch.target_le_value
        simp at heq
        rw [heq] at htargetValue
        rcases hcatch.time_eq with htime | htime
        · rw [htime] at hrlt
          omega
        · rw [htime] at hrlt
          omega
    | succ q => omega
  by_cases hnegative : potential q r < 0
  · rcases negative_undershoot_cycle
      hcatch.target_in_epoch_range hcatch.coordinates hnegative with
      hcoverage | ⟨u, k, s, htu, hucoord, hresult⟩
    · exact Or.inl hcoverage
    · exact Or.inr ⟨u, k, s, by omega, hucoord, hresult⟩
  · have hnonnegative : 0 ≤ potential q r := by omega
    by_cases habove : Int.ofNat target ≤ potential q r
    · exact Or.inl
        (positiveQuotient_potential_aboveTarget_gives_coverageStep
          htpos hqpos hcatch.target_in_epoch_range
          hcatch.coordinates habove)
    · have hbelow : potential q r < Int.ofNat target := by omega
      rcases undershoot_eventually_negative_or_localCoverage
          hcatch.target_in_epoch_range hcatch.coordinates
          hnonnegative hbelow with ⟨u, k, s, htu, hucoord, hresult⟩
      exact Or.inr ⟨u, k, s, htu, hucoord, hresult⟩

/-- Finite catch-up theorem for a strict debt crossing.  By time `target-1`
or `target`, one obtains a target-ready state and can invoke the old epoch
API.  The theorem also exposes the two comparisons needed to transport the
result back to the debt search: either the catch-up value is already a
`CoverageStep` child of the debt value, or it has grown to at least that
value; independently, either it lowers the phase anchor or reaches it.

Thus clock catch-up is unconditional and finite.  What remains is precisely
the value/anchor-growth branch, not the old `target ≤ time+1` mismatch. -/
theorem debtCrossing_finite_catchup
    {target horizon anchor value n : Nat}
    (_hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hbelow : a n < target) :
    ∃ t q r f,
      CrossingCatchup target horizon anchor t q r f ∧
      (CoverageStep target value (n + 1) ∨ value ≤ a t) ∧
      (PhaseSearchProgress target
          ⟨horizon, a t, .normal, a t⟩
          ⟨horizon, anchor, .debt, n + 1⟩ ∨
        anchor ≤ a t) ∧
      (CoverageStep target (a t) t ∨
        ∃ u k s,
          t ≤ u ∧ CoordinatesAt u k s ∧
          (potential k s < 0 ∨ CoverageStep target (a u) u)) := by
  have htarget : 0 < target := by omega
  rcases exists_targetReady_state_of_pos htarget with
    ⟨t, q, r, f, htimeEq, htime, htargetValue,
      hcoord, hfle, hfirst⟩
  let hcatch : CrossingCatchup target horizon anchor t q r f := {
    time_eq := htimeEq
    target_in_epoch_range := htime
    target_le_value := htargetValue
    coordinates := hcoord
    first_time_le := hfle
    first := hfirst
  }
  have hvalueOutcome :
      CoverageStep target value (n + 1) ∨ value ≤ a t := by
    by_cases hdrop : a t < value
    · exact Or.inl (Or.inr
        ⟨a t, f, htargetValue, hfirst, hdrop⟩)
    · exact Or.inr (by omega)
  have hanchorOutcome :
      PhaseSearchProgress target
          ⟨horizon, a t, .normal, a t⟩
          ⟨horizon, anchor, .debt, n + 1⟩ ∨
        anchor ≤ a t := by
    by_cases hdrop : a t < anchor
    · exact Or.inl (phaseSearch_exitDebt_of_anchorDrop hdrop)
    · exact Or.inr (by omega)
  exact ⟨t, q, r, f, hcatch, hvalueOutcome, hanchorOutcome,
    crossingCatchup_epoch_frontier htarget hcatch⟩

/-- In the diagonal-origin case the catch-up construction is genuinely
forward: the selected state lies strictly after the crossing and no later
than `horizon+1`.  The small gap is retained as a separate local bound while
the absolute clock catches up. -/
theorem diagonalDebt_strictCrossing_finite_forward
    {horizon anchor value n : Nat}
    (hinv : DebtInvariant (horizon + 1)
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbelow : a n < horizon + 1)
    (hstrict : horizon + 1 < value) :
    (0 < (horizon + 1) - a n ∧
      (horizon + 1) - a n ≤ n + 1) ∧
    ∃ t q r f,
      CrossingCatchup (horizon + 1) horizon anchor t q r f ∧
      n + 1 < t ∧ t ≤ horizon + 1 ∧
      (CoverageStep (horizon + 1) (a t) t ∨
        ∃ u k s,
          t ≤ u ∧ CoordinatesAt u k s ∧
          (potential k s < 0 ∨
            CoverageStep (horizon + 1) (a u) u)) := by
  have hnext := a_succ_of_not_canSubtract hnot
  have hvalue : value = a (n + 1) := hinv.first.1.symm
  have hcross : DebtCrossing (horizon + 1) value n := by
    refine ⟨hbelow, hstrict, ?_⟩
    exact hvalue.trans hnext
  have hgap := debtCrossing_gap_bounds hcross
  rcases debtCrossing_finite_catchup hinv hbelow with
    ⟨t, q, r, f, hcatch, _, _, hfrontier⟩
  have hdebtTime : n + 1 < horizon := by
    simpa using hinv.firstTime_lt_horizon
  have hforward : n + 1 < t := by
    rcases hcatch.time_eq with htime | htime
    · have ht : t = horizon := by omega
      rw [ht]
      exact hdebtTime
    · rw [htime]
      exact Nat.lt_trans hdebtTime (by omega)
  have htbound : t ≤ horizon + 1 := by
    rcases hcatch.time_eq with htime | htime <;> omega
  exact ⟨hgap, t, q, r, f, hcatch, hforward, htbound, hfrontier⟩

/-- The small relative gap does not imply the absolute epoch time bound.
This is an actual Recamán crossing (`3→6`) with diagonal-style horizon
`4`: gap `2` fits in the step, while target `5` is still beyond `n+2`. -/
theorem crossingGap_does_not_imply_absolute_epoch_range :
    DebtInvariant 5 ⟨4, 7, .debt, 3⟩ 6 3 ∧
      DebtCrossing 5 6 2 ∧
      0 < 5 - a 2 ∧ 5 - a 2 ≤ 3 ∧
      ¬ (5 ≤ 2 + 2) := by
  refine ⟨?_, ?_, by decide, by decide, by omega⟩
  · refine {
      phase_eq := rfl
      local_eq := rfl
      target_le := by omega
      first := ?_
      firstTime_lt_horizon := by decide
      value_lt_anchor := by decide
    }
    constructor
    · decide
    · intro u hu
      have hcases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases hcases with h | h | h <;> subst u <;> decide
  · unfold DebtCrossing
    exact ⟨by decide, by decide, by decide⟩

end Recaman
