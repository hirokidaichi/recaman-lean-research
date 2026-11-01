import Recaman.CrossingGrowth
import Recaman.NormalClosure

namespace Recaman

/-! # The epoch frontier of a crossing-growth obstruction

This module separates the sign information at the catch-up point from the
later epoch frontier.  Any first occurrence learned after the debt horizon is
stored at an enlarged child horizon; it is never read through the old one.
-/

/-- The quotient at a target-ready catch-up point is positive. -/
theorem crossingCatchup_quotient_pos
    {target horizon anchor t q r f : Nat}
    (hcatch : CrossingCatchup target horizon anchor t q r f) :
    0 < q := by
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

/-- Exact local sign split at the catch-up point.

The third branch is stated as `CoverageStep`: in the above-target half-space,
the positive quotient and the target-ready clock make coverage a theorem.
Thus the only non-coverage sign regions are negative potential and the
nonnegative undershoot strip. -/
theorem crossingCatchup_potential_trichotomy
    {target horizon anchor t q r f : Nat}
    (hcatch : CrossingCatchup target horizon anchor t q r f) :
    potential q r < 0 ∨
      (0 ≤ potential q r ∧ potential q r < Int.ofNat target) ∨
      CoverageStep target (a t) t := by
  by_cases htargetZero : target = 0
  · subst target
    exact Or.inr (Or.inr (Or.inl ⟨0, rfl⟩))
  have htargetPositive : 0 < target := by omega
  by_cases hnegative : potential q r < 0
  · exact Or.inl hnegative
  · have hnonnegative : 0 ≤ potential q r := by omega
    by_cases habove : Int.ofNat target ≤ potential q r
    · have htpos : 0 < t := by
        cases t with
        | zero =>
            have hle := hcatch.target_le_value
            have hzero : a 0 = 0 := rfl
            rw [hzero] at hle
            exact False.elim (by omega)
        | succ t => omega
      exact Or.inr (Or.inr
        (positiveQuotient_potential_aboveTarget_gives_coverageStep
          htpos (crossingCatchup_quotient_pos hcatch)
          hcatch.target_in_epoch_range hcatch.coordinates habove))
    · exact Or.inr (Or.inl ⟨hnonnegative, by omega⟩)

/-- Associative normal form of the processed epoch frontier: immediate
coverage, a later negative point, or later local coverage.  The undershoot
case from `crossingCatchup_potential_trichotomy` is precisely the case which
the finite undershoot theorem processes before producing this result. -/
theorem CrossingGrowthObstructionAt.frontier_cases
    {target horizon anchor value debtTime catchTime quotient remainder
      firstTime : Nat}
    (h : CrossingGrowthObstructionAt target horizon anchor value debtTime
      catchTime quotient remainder firstTime) :
    CoverageStep target (a catchTime) catchTime ∨
      (∃ u k s,
        catchTime ≤ u ∧ CoordinatesAt u k s ∧ potential k s < 0) ∨
      ∃ u k s,
        catchTime ≤ u ∧ CoordinatesAt u k s ∧
          CoverageStep target (a u) u := by
  rcases h.epoch_frontier with hcoverage |
      ⟨u, k, s, htime, hcoord, hnegative | hcoverage⟩
  · exact Or.inl hcoverage
  · exact Or.inr (Or.inl ⟨u, k, s, htime, hcoord, hnegative⟩)
  · exact Or.inr (Or.inr ⟨u, k, s, htime, hcoord, hcoverage⟩)

/-- Extending the history horizon while lowering the anchor is a valid exit
from debt.  This is the horizon-safe version of
`phaseSearch_exitDebt_of_anchorDrop`. -/
theorem phaseSearch_exitDebt_of_extendedHorizonAndAnchor
    {target childHorizon childAnchor childLocal parentHorizon parentAnchor
      parentTime : Nat}
    (htime : parentHorizon ≤ childHorizon)
    (hanchor : childAnchor < parentAnchor) :
    PhaseSearchProgress target
      ⟨childHorizon, childAnchor, .normal, childLocal⟩
      ⟨parentHorizon, parentAnchor, .debt, parentTime⟩ := by
  have hbudget := missingBelowCount_antitone (m := target) htime
  rcases Nat.eq_or_lt_of_le hbudget with heq | hlt
  · change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (missingBelowCount target childHorizon,
        (childAnchor, (SearchPhase.normal.rank, childLocal)))
      (missingBelowCount target parentHorizon,
        (parentAnchor, (SearchPhase.debt.rank, parentTime)))
    rw [heq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hanchor)
  · exact Prod.Lex.left _ _ hlt

/-- Exact residual left when a frontier first occurrence cannot lower the old
debt anchor.  The negative constructor also records the alternative that the
frontier value is below the target and hence is not a normal-search value.
The coverage constructor exposes the actual blocker rather than hiding it in
`CoverageStep`. -/
inductive CrossingFrontierResidual
    (target horizon anchor catchTime : Nat) : Prop
  | negative
      (u q r : Nat)
      (time : catchTime ≤ u)
      (coordinates : CoordinatesAt u q r)
      (potential_negative : potential q r < 0)
      (normal_failure : a u < target ∨ anchor ≤ a u) :
      CrossingFrontierResidual target horizon anchor catchTime
  | coverage
      (u q r value firstTime : Nat)
      (time : catchTime ≤ u)
      (coordinates : CoordinatesAt u q r)
      (target_le : target ≤ value)
      (first : FirstAt a value firstTime)
      (value_lt_frontier : value < a u)
      (anchor_le : anchor ≤ value) :
      CrossingFrontierResidual target horizon anchor catchTime

/-- Turn a frontier first occurrence below the old anchor into a semantic
normal child.  `max horizon firstTime` is essential: the certificate never
uses a post-horizon occurrence at the old horizon. -/
theorem frontierFirstAt_phaseSemantic
    {target horizon anchor debtTime value firstTime : Nat}
    (htarget : 0 < target)
    (htargetValue : target ≤ value)
    (hfirst : FirstAt a value firstTime)
    (hanchor : value < anchor) :
    let child : PhaseSearchNode :=
      ⟨max horizon firstTime, value, .normal, value⟩
    PhaseSemanticInvariant target child ∧
      PhaseSearchProgress target child
        ⟨horizon, anchor, .debt, debtTime⟩ := by
  let child : PhaseSearchNode :=
    ⟨max horizon firstTime, value, .normal, value⟩
  refine ⟨.normal (firstAt_normalSearchInvariant htarget htargetValue hfirst
    (Nat.le_max_right _ _)), ?_⟩
  exact phaseSearch_exitDebt_of_extendedHorizonAndAnchor
    (Nat.le_max_left _ _) hanchor

/-- Strong frontier classification relative to the original debt parent.

Every processed frontier branch either finds the target, supplies a semantic
rank child, or retains exactly why the frontier cannot do so: its candidate is
below the target or does not lower the old anchor. -/
theorem crossingGrowthObstructionAt_frontier_phaseOutcome
    {target horizon anchor value debtTime catchTime quotient remainder
      firstTime : Nat}
    (htarget : 0 < target)
    (h : CrossingGrowthObstructionAt target horizon anchor value debtTime
      catchTime quotient remainder firstTime) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, debtTime⟩) ∨
      CrossingFrontierResidual target horizon anchor catchTime := by
  rcases h.frontier_cases with hcoverage |
      ⟨u, q, r, htime, hcoord, hnegative⟩ |
      ⟨u, q, r, htime, hcoord, hcoverage⟩
  · have hcoord := h.catchup.coordinates
    rcases hcoverage with hoccurs |
        ⟨y, fy, htargetY, hfirstY, hylt⟩
    · exact Or.inl hoccurs
    · by_cases heq : y = target
      · exact Or.inl ⟨fy, by simpa [heq] using hfirstY.1⟩
      · by_cases hanchorDrop : y < anchor
        · exact Or.inr (Or.inl ⟨_,
            frontierFirstAt_phaseSemantic htarget htargetY hfirstY
              hanchorDrop⟩)
        · exact Or.inr (Or.inr (.coverage catchTime quotient remainder y fy
            (Nat.le_refl _) hcoord htargetY hfirstY hylt (by omega)))
  · rcases history_member_has_firstAt (current_mem_valuesThrough u) with
      ⟨fu, hfu, hfirstU⟩
    by_cases heq : a u = target
    · exact Or.inl ⟨u, heq⟩
    · by_cases htargetValue : target ≤ a u
      · by_cases hanchorDrop : a u < anchor
        · exact Or.inr (Or.inl ⟨_,
            frontierFirstAt_phaseSemantic htarget htargetValue hfirstU
              hanchorDrop⟩)
        · exact Or.inr (Or.inr (.negative u q r htime hcoord hnegative
            (Or.inr (by omega))))
      · exact Or.inr (Or.inr (.negative u q r htime hcoord hnegative
          (Or.inl (by omega))))
  · rcases hcoverage with hoccurs |
        ⟨y, fy, htargetY, hfirstY, hylt⟩
    · exact Or.inl hoccurs
    · by_cases heq : y = target
      · exact Or.inl ⟨fy, by simpa [heq] using hfirstY.1⟩
      · by_cases hanchorDrop : y < anchor
        · exact Or.inr (Or.inl ⟨_,
            frontierFirstAt_phaseSemantic htarget htargetY hfirstY
              hanchorDrop⟩)
        · exact Or.inr (Or.inr (.coverage u q r y fy htime hcoord
            htargetY hfirstY hylt (by omega)))

/-- Strongest unconditional result for the crossing-growth branch in the
current semantic domain.  Frontier-derived children are used when available;
on either explicit frontier residual, the original strong debt certificate
still supplies its horizon-safe self-exit. -/
theorem crossingGrowthObstructionAt_phaseSemanticStep
    {target horizon anchor value debtTime catchTime quotient remainder
      firstTime : Nat}
    (htarget : 0 < target)
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, debtTime⟩ value debtTime)
    (h : CrossingGrowthObstructionAt target horizon anchor value debtTime
      catchTime quotient remainder firstTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, debtTime⟩ := by
  rcases crossingGrowthObstructionAt_frontier_phaseOutcome htarget h with
    hoccurs | hchild | _
  · exact Or.inl hoccurs
  · exact Or.inr hchild
  · exact Or.inr ⟨_, debtInvariant_selfExit_phaseSemantic htarget hinv⟩

/-- Existentially packaged completion theorem for the joint-growth branch.
It uses a frontier-derived child whenever that child lowers the old anchor;
the exact residual cases remain safe because the original strong debt
certificate supplies a semantic self-exit. -/
theorem crossingGrowthObstruction_phaseSemanticStep
    {target horizon anchor value debtTime : Nat}
    (htarget : 0 < target)
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, debtTime⟩ value debtTime)
    (h : CrossingGrowthObstruction target horizon anchor value debtTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, debtTime⟩ := by
  rcases h with ⟨catchTime, quotient, remainder, firstTime, hat⟩
  exact crossingGrowthObstructionAt_phaseSemanticStep htarget hinv hat

end Recaman
