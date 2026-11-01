import Recaman.CanonicalOracle

namespace Recaman

private theorem canonicalLevelTwo_firstAt_two : FirstAt a 2 4 := by
  constructor
  · decide
  · intro u hu
    have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by omega
    rcases hcases with h | h | h | h <;> subst u <;> decide

/-- The exact level-two boundary not closed by the first actual transition.
At quotient one, level two means `a n=n+3`; subtraction aims at the already
seen value two, so forced addition grows to `2n+4`. -/
inductive CanonicalLevelTwoForcedResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | forced
      (orbitTime remainder firstTime : Nat)
      (parent_eq : parent = targetStartNode orbitTime)
      (certificate : TargetStartCertificate target orbitTime)
      (coordinates : CoordinatesAt orbitTime 1 remainder)
      (current_first : FirstAt a (a orbitTime) firstTime)
      (firstTime_le : firstTime ≤ orbitTime)
      (potential_two : potential 1 remainder = Int.ofNat 2)
      (forced_addition : ¬ CanSubtract
        (orbitTime + 1) (stateAt orbitTime))
      (remainder_eq : remainder = 3)
      (current_value_eq : a orbitTime = orbitTime + 3)
      (blocked_candidate_two : 2 ∈ valuesThrough orbitTime)
      (first_two : FirstAt a 2 4)
      (four_le_orbitTime : 4 ≤ orbitTime)
      (target_gt_two : 2 < target) :
      CanonicalLevelTwoForcedResidual target parent

/-- The residual's next actual state is completely rigid: it grows, enters
the negative half-space at `(q,r)=(2,2)`, and consumes no below-target
history budget.  This explains why it cannot be silently treated as an
ordinary decreasing normal child. -/
theorem CanonicalLevelTwoForcedResidual.growth_negative
    {target : Nat} {parent : PhaseSearchNode}
    (h : CanonicalLevelTwoForcedResidual target parent) :
    ∃ n,
      parent = targetStartNode n ∧
      a (n + 1) = 2 * n + 4 ∧
      CoordinatesAt (n + 1) 2 2 ∧
      potential 2 2 < 0 ∧
      a n < a (n + 1) ∧
      missingBelowCount target (n + 1) =
        missingBelowCount target n := by
  cases h with
  | forced n remainder firstTime hparent hcert hcoord hfirst hfirstTime
      hpotential hnot hremainder hvalue hseen hfirstTwo hnFour htarget =>
    have hnext := a_succ_of_not_canSubtract hnot
    have hnextValue : a (n + 1) = 2 * n + 4 := by omega
    have hnextCoord : CoordinatesAt (n + 1) 2 2 := by
      constructor
      · omega
      · omega
    have htargetNext : target ≤ a (n + 1) := by
      have := hcert.time_ready
      omega
    exact ⟨n, hparent, hnextValue, hnextCoord, by decide, by omega,
      missingBelowCount_succ_of_new_ge htargetNext⟩

/-- Complete one-step analysis of a canonical low-level residual at level
two.  Legal subtraction either stays above the target and gives a coverage
blocker, or crosses below and consumes history budget.  Forced addition with
quotient at least two also exposes an above-target blocker.  Only the rigid
quotient-one forced-addition chamber remains. -/
theorem canonicalLevelTwo_phaseSemanticStep_or_forcedQOne
    {target n q r firstTime : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (hparent : parent = targetStartNode n)
    (hcert : TargetStartCertificate target n)
    (hcoord : CoordinatesAt n q r)
    (hfirst : FirstAt a (a n) firstTime)
    (hfirstTime : firstTime ≤ n)
    (hcurrentAbove : target < a n)
    (hqpos : 0 < q)
    (hpotential : potential q r = Int.ofNat 2)
    (hlevelTarget : 2 < target) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      CanonicalLevelTwoForcedResidual target parent := by
    have hr : r = upperTri q + 2 :=
      (potential_eq_ofNat_iff q r 2).mp hpotential
    by_cases hcan : CanSubtract (n + 1) (stateAt n)
    · have hnext := a_succ_of_canSubtract hcan
      have hnextFirst := firstAt_succ_of_canSubtract hcan
      have hnextDrop : a (n + 1) < a n := by
        have hpositive : n + 1 < a n := by simpa [a] using hcan.1
        omega
      by_cases htargetNext : target ≤ a (n + 1)
      · have hcoverage : CoverageStep target (a n) n :=
          Or.inr ⟨a (n + 1), n + 1, htargetNext, hnextFirst,
            hnextDrop⟩
        rcases canonicalCoverage_phaseSemantic htarget hcoverage with
          hoccurs | hchild
        · exact Or.inl hoccurs
        · exact Or.inr (Or.inl (by simpa [hparent] using hchild))
      · have hbelow : a (n + 1) < target := Nat.lt_of_not_ge htargetNext
        rcases orbit_downcrossing_occurs_or_budgetDrop
            (show n ≤ n + 1 by omega) hcert.value_ready hbelow with
          hoccurs | hbudgetDrop
        · rcases hoccurs with ⟨witness, _, _, hvalue⟩
          exact Or.inl ⟨witness, hvalue⟩
        · let child : PhaseSearchNode :=
            ⟨n + 1, a n, .normal, a n⟩
          have hsemantic : PhaseSemanticInvariant target child := .normal
            (firstAt_normalSearchInvariant htarget hcert.value_ready hfirst
              (Nat.le_trans hfirstTime (by omega)))
          have hprogress : PhaseSearchProgress target child parent := by
            rw [hparent]
            exact Prod.Lex.left _ _ hbudgetDrop
          exact Or.inr (Or.inl ⟨child, hsemantic, hprogress⟩)
    · by_cases hqone : q = 1
      · subst q
        have hrthree : r = 3 := by
          simpa [upperTri] using hr
        have hvalue : a n = n + 3 := by
          have heq := hcoord.eqn
          omega
        have hcandidate : a n - (n + 1) = 2 := by omega
        have hseen : 2 ∈ valuesThrough n := by
          rcases not_canSubtract_cases hcan with hnonpositive | hseen
          · omega
          · simpa [hcandidate] using hseen
        have hnFour : 4 ≤ n := by
          rcases mem_valuesThrough_iff.mp hseen with ⟨u, hu, huValue⟩
          have huFour : 4 ≤ u := by
            by_cases hlt : u < 4
            · exact False.elim
                (canonicalLevelTwo_firstAt_two.2 u hlt huValue)
            · omega
          omega
        exact Or.inr (Or.inr (.forced n r firstTime hparent hcert hcoord
          hfirst hfirstTime hpotential hcan hrthree hvalue hseen
          canonicalLevelTwo_firstAt_two hnFour hlevelTarget))
      · have hqtwo : 2 ≤ q := by omega
        let y := a n - (n + 1)
        have heq := hcoord.eqn
        have hyTarget : target ≤ y := by
          have hnTarget : n ≤ target := by
            rcases hcert.near_target with hnear | hnear <;> omega
          have htargetTime := hcert.time_ready
          have htri : 3 ≤ upperTri q := by
            simpa using upperTri_mono hqtwo
          have hrLower : 5 ≤ r := by omega
          have hmul : n * 2 ≤ n * q :=
            Nat.mul_le_mul_left n hqtwo
          have hvalueLower : 2 * n + 5 ≤ a n := by
            rw [heq]
            omega
          have hyEq : y + (n + 1) = a n := by
            simp only [y]
            omega
          have hsum : n + 4 + (n + 1) ≤ a n := by omega
          have hyLower : n + 4 ≤ y := by
            simpa only [y] using Nat.le_sub_of_add_le hsum
          omega
        have hyPositive : n + 1 < a n := by
          simp only [y] at hyTarget
          omega
        have hySeen : y ∈ valuesThrough n := by
          rcases not_canSubtract_cases hcan with hnonpositive | hseen
          · omega
          · simpa only [y] using hseen
        rcases history_member_has_firstAt hySeen with
          ⟨fy, _, hfirstY⟩
        have hyDrop : y < a n := by
          simp only [y]
          omega
        have hcoverage : CoverageStep target (a n) n :=
          Or.inr ⟨y, fy, hyTarget, hfirstY, hyDrop⟩
        rcases canonicalCoverage_phaseSemantic htarget hcoverage with
          hoccurs | hchild
        · exact Or.inl hoccurs
        · exact Or.inr (Or.inl (by simpa [hparent] using hchild))

end Recaman
