import Recaman.CrossingGrowth

namespace Recaman

/-- Exact residuals left when the epoch frontier of a joint-growth crossing
is compared with the *original* debt anchor.  A coverage blocker may descend
from its local orbit value while staying above the old anchor; likewise a
negative endpoint may still have value at least the old anchor. -/
inductive CrossingIterationResidual
    (target anchor : Nat) : Prop
  | coverage_growth (sourceTime sourceValue value firstTime : Nat)
      (target_le : target ≤ value)
      (first : FirstAt a value firstTime)
      (below_source : value < sourceValue)
      (anchor_le : anchor ≤ value) :
      CrossingIterationResidual target anchor
  | negative_growth (time quotient remainder : Nat)
      (coordinates : CoordinatesAt time quotient remainder)
      (negative : potential quotient remainder < 0)
      (anchor_le : anchor ≤ a time) :
      CrossingIterationResidual target anchor

/-- The epoch frontier can be refined against the old anchor without any new
hypothesis.  It either finds the target, produces a formal normal child below
the old debt anchor, or returns one of the two literal joint-growth cases.

The child here is deliberately rank-only: a negative endpoint below the
target need not satisfy `NormalSearchInvariant`.  The residual type is the
additional semantic case a final oracle must represent. -/
theorem CrossingGrowthObstructionAt.refine_epoch_frontier
    {target horizon anchor value debtTime catchTime quotient remainder
      firstTime : Nat}
    (h : CrossingGrowthObstructionAt target horizon anchor value debtTime
      catchTime quotient remainder firstTime) :
    (∃ t, a t = target) ∨
      (∃ child : PhaseSearchNode,
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, debtTime⟩) ∨
      CrossingIterationResidual target anchor := by
  rcases h.epoch_frontier with hcoverage |
      ⟨u, k, s, _, hucoord, hresult⟩
  · rcases hcoverage with hoccurs |
        ⟨y, fy, htargetY, hfirstY, hySource⟩
    · exact Or.inl hoccurs
    · by_cases hyAnchor : y < anchor
      · exact Or.inr (Or.inl
          ⟨⟨horizon, y, .normal, y⟩,
            phaseSearch_exitDebt_of_anchorDrop hyAnchor⟩)
      · exact Or.inr (Or.inr
          (.coverage_growth catchTime (a catchTime) y fy htargetY
            hfirstY hySource (Nat.le_of_not_gt hyAnchor)))
  · rcases hresult with hnegative | hcoverage
    · by_cases huAnchor : a u < anchor
      · exact Or.inr (Or.inl
          ⟨⟨horizon, a u, .normal, a u⟩,
            phaseSearch_exitDebt_of_anchorDrop huAnchor⟩)
      · exact Or.inr (Or.inr
          (.negative_growth u k s hucoord hnegative
            (Nat.le_of_not_gt huAnchor)))
    · rcases hcoverage with hoccurs |
          ⟨y, fy, htargetY, hfirstY, hySource⟩
      · exact Or.inl hoccurs
      · by_cases hyAnchor : y < anchor
        · exact Or.inr (Or.inl
            ⟨⟨horizon, y, .normal, y⟩,
              phaseSearch_exitDebt_of_anchorDrop hyAnchor⟩)
        · exact Or.inr (Or.inr
            (.coverage_growth u (a u) y fy htargetY hfirstY hySource
              (Nat.le_of_not_gt hyAnchor)))

/-- The actual growth obstruction at target five admits a frontier witness
whose very next state is negative while its value has grown from seven to
thirteen.  Thus a second simultaneous value/anchor-growth situation is real,
not merely permitted by a weak disjunctive interface. -/
theorem crossingGrowth_negativeContinuation_actual_example :
    CrossingGrowthObstruction 5 4 7 6 3 ∧
      5 ≤ 6 ∧ CoordinatesAt 6 2 1 ∧
      potential 2 1 < 0 ∧
      7 ≤ a 6 ∧ a 5 < a 6 ∧
      ¬ PhaseSearchProgress 5
        ⟨4, a 6, .normal, a 6⟩
        ⟨4, 7, .debt, 3⟩ := by
  refine ⟨crossingGrowthObstruction_actual_example, by decide,
    ⟨by decide, by decide⟩, by decide, by decide, by decide, ?_⟩
  rw [exitDebt_to_normal_iff_anchorDrop]
  decide

/-- The same concrete continuation inhabits the exact residual constructor
required by `refine_epoch_frontier`. -/
theorem crossingIterationResidual_actual_example :
    CrossingIterationResidual 5 7 := by
  exact .negative_growth 6 2 1 ⟨by decide, by decide⟩
    (by decide) (by decide)

/-- None of the three existing numeric escape measures decreases on that
continuation: the below-target history budget is unchanged, and both the
orbit value and the comparison with the old anchor grow. -/
theorem crossingGrowth_negativeContinuation_no_standard_descent_example :
    missingBelowCount 5 6 = missingBelowCount 5 4 ∧
      a 5 < a 6 ∧ 7 ≤ a 6 := by
  exact ⟨by decide, by decide, by decide⟩

/-- In particular, negative potential alone does not turn a joint-growth
frontier into a child of the old debt node.  Any total semantic oracle must
either add `negative_growth` as a proof-carrying state or establish a further
descent theorem from precisely that state. -/
theorem negativeGrowth_not_oldDebtRank_example :
    potential 2 1 < 0 ∧ 7 ≤ a 6 ∧
      ¬ PhaseSearchProgress 5
        ⟨4, a 6, .normal, a 6⟩
        ⟨4, 7, .debt, 3⟩ := by
  exact ⟨by decide, by decide,
    crossingGrowth_negativeContinuation_actual_example.2.2.2.2.2.2⟩

end Recaman
