import Recaman.CrossingGap

namespace Recaman

/-- With a fixed history horizon, returning from debt to a normal node is a
strict phase-search step exactly when the normal node's anchor is smaller.
The phase component cannot break equality in the desired direction: normal
has rank one while debt has rank zero. -/
theorem exitDebt_to_normal_iff_anchorDrop
    {target horizon childAnchor childLocal parentAnchor parentTime : Nat} :
    PhaseSearchProgress target
        ⟨horizon, childAnchor, .normal, childLocal⟩
        ⟨horizon, parentAnchor, .debt, parentTime⟩ ↔
      childAnchor < parentAnchor := by
  constructor
  · intro hprogress
    unfold PhaseSearchProgress phaseSearchRank at hprogress
    cases hprogress with
    | left _ _ hbudget => simp at hbudget
    | right _ hrest =>
        cases hrest with
        | left _ _ hanchor => exact hanchor
        | right _ hphaseLocal =>
            cases hphaseLocal with
            | left _ _ hphase =>
                change 1 < 0 at hphase
                omega
  · exact phaseSearch_exitDebt_of_anchorDrop

/-- The joint value/anchor-growth case left by finite clock catch-up.

It retains all positive information obtained at the catch-up state and its
epoch frontier.  The final field records a theorem, not a missing proof: the
obvious normal node at the catch-up value cannot decrease the original debt
rank when that value is at least the old anchor. -/
structure CrossingGrowthObstructionAt
    (target horizon anchor value debtTime catchTime quotient remainder
      firstTime : Nat) : Prop where
  catchup : CrossingCatchup target horizon anchor catchTime quotient
    remainder firstTime
  value_grows : value ≤ a catchTime
  anchor_grows : anchor ≤ a catchTime
  no_direct_phase_progress : ¬ PhaseSearchProgress target
    ⟨horizon, a catchTime, .normal, a catchTime⟩
    ⟨horizon, anchor, .debt, debtTime⟩
  epoch_frontier :
    CoverageStep target (a catchTime) catchTime ∨
      ∃ u k s,
        catchTime ≤ u ∧ CoordinatesAt u k s ∧
        (potential k s < 0 ∨ CoverageStep target (a u) u)

def CrossingGrowthObstruction
    (target horizon anchor value debtTime : Nat) : Prop :=
  ∃ catchTime quotient remainder firstTime,
    CrossingGrowthObstructionAt target horizon anchor value debtTime
      catchTime quotient remainder firstTime

/-- A coverage step below a strong debt value is already compatible with the
phase rank: either it witnesses the target, or its smaller first-occurring
value supplies a normal child whose anchor is below the debt anchor. -/
theorem debtCoverageStep_target_or_phaseProgress
    {target horizon anchor value debtTime : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, debtTime⟩ value debtTime)
    (hcoverage : CoverageStep target value debtTime) :
    (∃ t, a t = target) ∨
      ∃ y fy,
        target ≤ y ∧ FirstAt a y fy ∧ y < value ∧
        PhaseSearchProgress target
          ⟨horizon, y, .normal, y⟩
          ⟨horizon, anchor, .debt, debtTime⟩ := by
  rcases hcoverage with hoccurs | ⟨y, fy, htargetY, hfirstY, hyValue⟩
  · exact Or.inl hoccurs
  · have hyAnchor : y < anchor :=
      Nat.lt_trans hyValue hinv.value_lt_anchor
    exact Or.inr ⟨y, fy, htargetY, hfirstY, hyValue,
      phaseSearch_exitDebt_of_anchorDrop hyAnchor⟩

/-- Strongest unconditional phase-level refinement of finite catch-up.

Every strict crossing either finds the target, produces an explicit
rank-decreasing normal child (from a coverage blocker or an anchor drop), or
lands in the exact joint-growth obstruction.  Thus the two comparisons in
`debtCrossing_finite_catchup` are not independent residual goals: all mixed
cases close, and only `value ≤ catchupValue` together with
`anchor ≤ catchupValue` remains. -/
theorem debtCrossing_finite_catchup_phaseOutcome
    {target horizon anchor value n : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hbelow : a n < target) :
    (∃ t, a t = target) ∨
      (∃ child : PhaseSearchNode,
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, n + 1⟩) ∨
      CrossingGrowthObstruction target horizon anchor value (n + 1) := by
  rcases debtCrossing_finite_catchup hinv hbelow with
    ⟨t, q, r, f, hcatch, hvalue, hanchor, hfrontier⟩
  rcases hvalue with hcoverage | hvalueGrows
  · rcases debtCoverageStep_target_or_phaseProgress hinv hcoverage with
      hoccurs | ⟨y, fy, _, _, _, hprogress⟩
    · exact Or.inl hoccurs
    · exact Or.inr (Or.inl
        ⟨⟨horizon, y, .normal, y⟩, hprogress⟩)
  · rcases hanchor with hprogress | hanchorGrows
    · exact Or.inr (Or.inl
        ⟨⟨horizon, a t, .normal, a t⟩, hprogress⟩)
    · exact Or.inr (Or.inr ⟨t, q, r, f, {
          catchup := hcatch
          value_grows := hvalueGrows
          anchor_grows := hanchorGrows
          no_direct_phase_progress := by
            rw [exitDebt_to_normal_iff_anchorDrop]
            omega
          epoch_frontier := hfrontier
        }⟩)

/-- The obstruction is realized by the actual strict crossing `3 → 6`
across target five.  Clock catch-up lands at time five with value seven,
equal to the old anchor, so the natural normal node cannot be a phase-rank
child of the debt node. -/
theorem crossingGrowth_actual_example :
    CrossingCatchup 5 4 7 5 1 2 5 ∧
      6 ≤ a 5 ∧ 7 ≤ a 5 ∧
      ¬ PhaseSearchProgress 5
        ⟨4, a 5, .normal, a 5⟩
        ⟨4, 7, .debt, 3⟩ := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · refine {
      time_eq := Or.inr (by decide)
      target_in_epoch_range := by decide
      target_le_value := by decide
      coordinates := ⟨by decide, by decide⟩
      first_time_le := by decide
      first := ?_
    }
    constructor
    · decide
    · intro u hu
      have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by omega
      rcases hcases with h | h | h | h | h <;> subst u <;> decide
  · rw [exitDebt_to_normal_iff_anchorDrop]
    decide

/-- The complete obstruction package is inhabited on the same real orbit
segment; in particular its epoch frontier is not an inconsistent add-on. -/
theorem crossingGrowthObstruction_actual_example :
    CrossingGrowthObstruction 5 4 7 6 3 := by
  have hcatch : CrossingCatchup 5 4 7 5 1 2 5 :=
    crossingGrowth_actual_example.1
  refine ⟨5, 1, 2, 5, {
    catchup := hcatch
    value_grows := crossingGrowth_actual_example.2.1
    anchor_grows := crossingGrowth_actual_example.2.2.1
    no_direct_phase_progress := crossingGrowth_actual_example.2.2.2
    epoch_frontier := crossingCatchup_epoch_frontier (by decide) hcatch
  }⟩

end Recaman
