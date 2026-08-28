import Recaman.CanonicalLevelOne
import Recaman.CanonicalLevelTwo

namespace Recaman

/-! # Canonical forced-growth chamber

The quotient-one residuals at levels one and two have the same dynamics.
Their blocked subtraction forces an addition into quotient two, with negative
potential.  The semantic invariant survives, but the current phase rank does
not decrease because both the history budget and the old anchor fail to drop.
-/

/-- Unified proof-carrying state for the two quotient-one forced-growth
residuals. -/
inductive CanonicalForcedGrowthChamber
    (target : Nat) (parent : PhaseSearchNode) : Nat → Prop
  | forced
      (level orbitTime firstTime : Nat)
      (level_cases : level = 1 ∨ level = 2)
      (parent_eq : parent = targetStartNode orbitTime)
      (certificate : TargetStartCertificate target orbitTime)
      (current_first : FirstAt a (a orbitTime) firstTime)
      (firstTime_le : firstTime ≤ orbitTime)
      (current_above_target : target < a orbitTime)
      (current_value_eq : a orbitTime = orbitTime + 1 + level)
      (level_lt_succ_time : level < orbitTime + 1)
      (forced_addition :
        ¬ CanSubtract (orbitTime + 1) (stateAt orbitTime)) :
      CanonicalForcedGrowthChamber target parent level

theorem CanonicalLevelOneForcedQOneResidual.toForcedGrowthChamber
    {target : Nat} {parent : PhaseSearchNode}
    (h : CanonicalLevelOneForcedQOneResidual target parent) :
    CanonicalForcedGrowthChamber target parent 1 := by
  cases h with
  | forced n firstTime hparent hcert hfirst hfirstTime habove _ hvalue
      _ _ _ hnot =>
      exact .forced 1 n firstTime (Or.inl rfl) hparent hcert hfirst
        hfirstTime habove (by omega) (by omega) hnot

theorem CanonicalLevelTwoForcedResidual.toForcedGrowthChamber
    {target : Nat} {parent : PhaseSearchNode}
    (h : CanonicalLevelTwoForcedResidual target parent) :
    CanonicalForcedGrowthChamber target parent 2 := by
  cases h with
  | forced n remainder firstTime hparent hcert _ hfirst hfirstTime _ hnot
      _ hvalue _ _ _ _ =>
      have hnear := hcert.near_target
      exact .forced 2 n firstTime (Or.inr rfl) hparent hcert hfirst
        hfirstTime (by rcases hnear with hnear | hnear <;> omega)
        (by omega) (by omega) hnot

private theorem forcedGrowth_natTripleLex_fst_le
    {x y : Nat × (Nat × Nat)}
    (h : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) x y) :
    x.1 ≤ y.1 := by
  cases h with
  | left _ _ hlt => exact Nat.le_of_lt hlt
  | right _ _ => exact Nat.le_refl _

private theorem forcedGrowth_natQuadLex_tail_of_budgetEq
    {x y : Nat × (Nat × (Nat × Nat))}
    (h : Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) x y)
    (heq : x.1 = y.1) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) x.2 y.2 := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  change xa = ya at heq
  subst ya
  cases h with
  | left _ _ hlt => exact False.elim (Nat.lt_irrefl _ hlt)
  | right _ htail => exact htail

/-- A normal child with unchanged budget and a strictly larger anchor cannot
decrease the current phase rank. -/
theorem normal_anchorGrowth_budgetEq_no_phaseProgress
    {target parentTime childTime parentAnchor childAnchor
      parentLocal childLocal : Nat}
    (hbudget : missingBelowCount target childTime =
      missingBelowCount target parentTime)
    (hanchor : parentAnchor < childAnchor) :
    ¬ PhaseSearchProgress target
      ⟨childTime, childAnchor, .normal, childLocal⟩
      ⟨parentTime, parentAnchor, .normal, parentLocal⟩ := by
  intro hp
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (missingBelowCount target childTime,
      (childAnchor, (SearchPhase.normal.rank, childLocal)))
    (missingBelowCount target parentTime,
      (parentAnchor, (SearchPhase.normal.rank, parentLocal))) at hp
  have htail := forcedGrowth_natQuadLex_tail_of_budgetEq hp hbudget
  have htail' : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
      (childAnchor, (SearchPhase.normal.rank, childLocal))
      (parentAnchor, (SearchPhase.normal.rank, parentLocal)) := by
    simpa using htail
  have hanchorLe := forcedGrowth_natTripleLex_fst_le htail'
  omega

/-- Exact common next-state theorem for levels one and two.

The forced child has coordinates `(2,level)`, hence potential `level-3<0`.
It is a valid ordinary semantic normal node and even satisfies the strong
negative normal invariant when anchored at its own value.  Nevertheless it
cannot be a phase-search child of the old canonical parent: its value/anchor
strictly grows while its below-target history budget is unchanged. -/
theorem CanonicalForcedGrowthChamber.nextState
    {target level : Nat} {parentNode : PhaseSearchNode}
    (htarget : 0 < target)
    (h : CanonicalForcedGrowthChamber target parentNode level) :
    ∃ n child,
      parentNode = targetStartNode n ∧
      child = ⟨n + 1, a (n + 1), .normal, a (n + 1)⟩ ∧
      a (n + 1) = 2 * n + 2 + level ∧
      CoordinatesAt (n + 1) 2 level ∧
      potential 2 level < 0 ∧
      a n < a (n + 1) ∧
      missingBelowCount target (n + 1) = missingBelowCount target n ∧
      PhaseSemanticInvariant target child ∧
      NormalPhaseInvariantAt target child (n + 1) 2 level ∧
      ¬ PhaseSearchProgress target child parentNode := by
  cases h with
  | forced n firstTime hlevels hparent hcert hfirst hfirstTime habove
      hvalue hlevelTime hnot =>
    have hnext := a_succ_of_not_canSubtract hnot
    have hnextValue : a (n + 1) = 2 * n + 2 + level := by omega
    have hcoord : CoordinatesAt (n + 1) 2 level := by
      constructor
      · omega
      · exact hlevelTime
    have hnegative : potential 2 level < 0 := by
      rcases hlevels with hlevel | hlevel <;> subst level <;> decide
    have hgrowth : a n < a (n + 1) := by omega
    have htargetNext : target ≤ a (n + 1) := by
      have hready := hcert.time_ready
      omega
    have hbudget : missingBelowCount target (n + 1) =
        missingBelowCount target n :=
      missingBelowCount_succ_of_new_ge htargetNext
    rcases history_member_has_firstAt
        (current_mem_valuesThrough (n + 1)) with ⟨fn, hfn, hfirstN⟩
    let child : PhaseSearchNode :=
      ⟨n + 1, a (n + 1), .normal, a (n + 1)⟩
    have hsemantic : PhaseSemanticInvariant target child := .normal
      (firstAt_normalSearchInvariant htarget
        htargetNext hfirstN hfn)
    have hstrong : NormalPhaseInvariantAt target child (n + 1) 2 level := {
      node_eq := rfl
      time_ready := by omega
      target_le_value := htargetNext
      value_le_anchor := Nat.le_refl _
      coordinates := hcoord
      negative := hnegative
    }
    have hnoProgress : ¬ PhaseSearchProgress target child parentNode := by
      rw [hparent]
      exact normal_anchorGrowth_budgetEq_no_phaseProgress hbudget hgrowth
    exact ⟨n, child, hparent, rfl, hnextValue, hcoord, hnegative,
      hgrowth, hbudget, hsemantic, hstrong, hnoProgress⟩

/-- Although the immediate forced-growth state cannot lower the phase rank,
one further actual transition always returns to the existing semantic search.

At the forced state the next subtraction candidate is `n+level`.  The
canonical near-target condition makes it at least the target, while the old
value is exactly one larger.  If subtraction is legal the candidate is fresh;
if it is blocked the candidate is already in history.  Either way it is a
`CoverageStep` below the old canonical value, so no new phase or rank
component is required—only this two-step lookahead. -/
theorem CanonicalForcedGrowthChamber.twoStep_phaseSemantic
    {target level : Nat} {parent : PhaseSearchNode}
    (htarget : 0 < target)
    (h : CanonicalForcedGrowthChamber target parent level) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent := by
  cases h with
  | forced n firstTime hlevels hparent hcert hfirst hfirstTime habove
      hvalue hlevelTime hnot =>
    have hnext := a_succ_of_not_canSubtract hnot
    let candidate := n + level
    have hcandidate : a (n + 1) - (n + 2) = candidate := by
      simp only [candidate]
      omega
    have htargetCandidate : target ≤ candidate := by
      have hnear := hcert.near_target
      rcases hnear with hnear | hnear <;>
        rcases hlevels with hlevel | hlevel <;>
        subst level <;> omega
    have hcandidateDrop : candidate < a n := by
      simp only [candidate]
      omega
    have hpositive : n + 2 < a (n + 1) := by
      have hcandidatePositive : 0 < candidate :=
        Nat.lt_of_lt_of_le htarget htargetCandidate
      omega
    have hcoverage : CoverageStep target (a n) n := by
      by_cases hcanNext : CanSubtract (n + 2) (stateAt (n + 1))
      · have hnextNext := a_succ_of_canSubtract hcanNext
        have hvalueNext : a (n + 2) = candidate :=
          hnextNext.trans hcandidate
        have hfirstCandidate := firstAt_succ_of_canSubtract hcanNext
        exact Or.inr ⟨candidate, n + 2, htargetCandidate,
          by simpa [hvalueNext] using hfirstCandidate, hcandidateDrop⟩
      · rcases not_canSubtract_cases hcanNext with hnonpositive | hseen
        · exact False.elim (by omega)
        · have hcandidateSeen : candidate ∈ valuesThrough (n + 1) := by
            simpa only [hcandidate] using hseen
          rcases history_member_has_firstAt hcandidateSeen with
            ⟨fc, _, hfirstCandidate⟩
          exact Or.inr ⟨candidate, fc, htargetCandidate,
            hfirstCandidate, hcandidateDrop⟩
    rcases canonicalCoverage_phaseSemantic htarget hcoverage with
      hoccurs | hchild
    · exact Or.inl hoccurs
    · rw [hparent]
      exact Or.inr hchild

/-- The level-one chamber is not a hypothetical interface artifact.  The
actual canonical target-five state realizes it, and its next semantic state
therefore gives a concrete counterexample to rank closure. -/
theorem canonicalForcedGrowth_five_realized :
    CanonicalForcedGrowthChamber 5 (targetStartNode 5) 1 :=
  canonicalLevelOne_forcedQOne_five.toForcedGrowthChamber

/-- Concrete rank counterexample at the real target-five chamber: the
immediate forced state is semantically valid but is not a child of the old
canonical node. -/
theorem canonicalForcedGrowth_five_immediate_not_progress :
    ∃ child,
      PhaseSemanticInvariant 5 child ∧
      ¬ PhaseSearchProgress 5 child (targetStartNode 5) := by
  rcases canonicalForcedGrowth_five_realized.nextState (by decide) with
    ⟨n, child, _, _, _, _, _, _, _, hsemantic, _, hnoProgress⟩
  exact ⟨child, hsemantic, hnoProgress⟩

end Recaman
