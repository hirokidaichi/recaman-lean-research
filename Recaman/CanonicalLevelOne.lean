import Recaman.CanonicalOracle
import Recaman.NonnegativeSemantic

namespace Recaman

/-- Exact state left at canonical potential level one after all immediately
rank-visible branches have been removed. -/
inductive CanonicalLevelOneForcedQOneResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | forced
      (orbitTime firstTime : Nat)
      (parent_eq : parent = targetStartNode orbitTime)
      (certificate : TargetStartCertificate target orbitTime)
      (current_first : FirstAt a (a orbitTime) firstTime)
      (firstTime_le : firstTime ≤ orbitTime)
      (current_above_target : target < a orbitTime)
      (remainder_bound : 2 < orbitTime)
      (current_value_eq : a orbitTime = orbitTime + 2)
      (near_target : orbitTime = target - 1 ∨ orbitTime = target)
      (candidate_eq : a orbitTime - (orbitTime + 1) = 1)
      (one_seen : 1 ∈ valuesThrough orbitTime)
      (subtraction_blocked :
        ¬ CanSubtract (orbitTime + 1) (stateAt orbitTime)) :
      CanonicalLevelOneForcedQOneResidual target parent

/-- A legal next subtraction from a canonical above-target state either hits
the target, produces a smaller semantic normal anchor, or crosses below the
target and thereby consumes history budget. -/
theorem canonical_legalSubtraction_phaseSemantic
    {target n : Nat}
    (htarget : 0 < target)
    (htargetValue : target < a n)
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  have hnext := a_succ_of_canSubtract hcan
  have hnextDrop : a (n + 1) < a n := by
    have hpositive : n + 1 < a n := by simpa [a] using hcan.1
    omega
  by_cases heq : a (n + 1) = target
  · exact Or.inl ⟨n + 1, heq⟩
  by_cases habove : target ≤ a (n + 1)
  · have hfirst := firstAt_succ_of_canSubtract hcan
    let child : PhaseSearchNode :=
      ⟨n + 1, a (n + 1), .normal, a (n + 1)⟩
    have hsemantic : PhaseSemanticInvariant target child := .normal
      (firstAt_normalSearchInvariant htarget habove hfirst (Nat.le_refl _))
    exact Or.inr ⟨child, hsemantic,
      phaseSearchProgress_of_horizonAndAnchor (by omega) hnextDrop⟩
  · have hbelow : a (n + 1) < target := by omega
    rcases orbit_downcrossing_occurs_or_budgetDrop
        (show n ≤ n + 1 by omega) (Nat.le_of_lt htargetValue) hbelow with
      hoccurs | hbudget
    · rcases hoccurs with ⟨u, _, _, hu⟩
      exact Or.inl ⟨u, hu⟩
    · rcases history_member_has_firstAt (current_mem_valuesThrough n) with
        ⟨firstTime, hfirstTime, hfirst⟩
      let child : PhaseSearchNode := ⟨n + 1, a n, .normal, a n⟩
      have hsemantic : PhaseSemanticInvariant target child := .normal
        (firstAt_normalSearchInvariant htarget (Nat.le_of_lt htargetValue)
          hfirst (by omega))
      exact Or.inr ⟨child, hsemantic, Prod.Lex.left _ _ hbudget⟩

/-- The quotient-at-least-two forced-addition frontier has a complete
semantic interpretation at a canonical parent. -/
theorem canonical_forcedAddition_twoQuotient_phaseSemantic
    {target n q r : Nat}
    (htarget : 0 < target)
    (htime : target ≤ n + 1)
    (htargetValue : target < a n)
    (hcoord : CoordinatesAt n q r)
    (hq : 2 ≤ q)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  rcases coordinates_forcedAddition_twoQuotient_historySearchProgress
      htarget htime (Nat.le_refl _) hcoord hq hnot with
    ⟨y, fy, _, htargetY, hfirstY, hyDrop, _⟩ | hraw
  · let child : PhaseSearchNode := ⟨max (n + 2) fy, y, .normal, y⟩
    have hsemantic : PhaseSemanticInvariant target child := .normal
      (firstAt_normalSearchInvariant htarget htargetY hfirstY
        (Nat.le_max_right _ _))
    exact Or.inr ⟨child, hsemantic,
      phaseSearchProgress_of_horizonAndAnchor (by omega) hyDrop⟩
  · have hphase : PhaseSearchProgress target
        ⟨n + 2, a n, .normal, a (n + 2)⟩ (targetStartNode n) :=
      hraw.toNormalPhaseSearchProgress
    by_cases habove : target ≤ a (n + 2)
    · rcases history_member_has_firstAt
          (current_mem_valuesThrough (n + 2)) with ⟨ft, hft, hfirstT⟩
      let child : PhaseSearchNode :=
        ⟨n + 2, a (n + 2), .normal, a (n + 2)⟩
      have hsemantic : PhaseSemanticInvariant target child := .normal
        (firstAt_normalSearchInvariant htarget habove hfirstT hft)
      exact Or.inr ⟨child, hsemantic,
        normalProgress_reanchorAtValue (Nat.le_refl _) hphase⟩
    · have hbelow : a (n + 2) < target := by omega
      rcases orbit_downcrossing_occurs_or_budgetDrop
          (show n ≤ n + 2 by omega) (Nat.le_of_lt htargetValue) hbelow with
        hoccurs | hbudget
      · rcases hoccurs with ⟨u, _, _, hu⟩
        exact Or.inl ⟨u, hu⟩
      · rcases history_member_has_firstAt (current_mem_valuesThrough n) with
          ⟨fn, hfn, hfirstN⟩
        let child : PhaseSearchNode := ⟨n + 2, a n, .normal, a n⟩
        have hsemantic : PhaseSemanticInvariant target child := .normal
          (firstAt_normalSearchInvariant htarget
            (Nat.le_of_lt htargetValue) hfirstN (by omega))
        exact Or.inr ⟨child, hsemantic, Prod.Lex.left _ _ hbudget⟩

/-- Complete level-one boundary from the existing canonical residual.

Legal subtraction closes immediately.  Forced addition with quotient at
least two closes through the two-step history frontier.  The sole remaining
state is quotient one; its arithmetic is forced to `r=2`, `a n=n+2`, and
the subtraction candidate one is already present in history. -/
theorem canonicalLowLevel_levelOne_phaseSemantic_or_forcedQOne
    {target n q r firstTime : Nat} {parent : PhaseSearchNode}
    (htarget : 0 < target)
    (hparent : parent = targetStartNode n)
    (hcert : TargetStartCertificate target n)
    (hcoord : CoordinatesAt n q r)
    (hfirst : FirstAt a (a n) firstTime)
    (hfirstTime : firstTime ≤ n)
    (habove : target < a n)
    (hqpos : 0 < q)
    (hpotential : potential q r = Int.ofNat 1) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      CanonicalLevelOneForcedQOneResidual target parent := by
  subst parent
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · rcases canonical_legalSubtraction_phaseSemantic htarget habove hcan with
      hoccurs | hchild
    · exact Or.inl hoccurs
    · exact Or.inr (Or.inl hchild)
  · by_cases hqTwo : 2 ≤ q
    · rcases canonical_forcedAddition_twoQuotient_phaseSemantic htarget
          hcert.time_ready habove hcoord hqTwo hcan with hoccurs | hchild
      · exact Or.inl hoccurs
      · exact Or.inr (Or.inl hchild)
    · have hqOne : q = 1 := by omega
      subst q
      have hr : r = 2 := by
        have := (potential_eq_ofNat_iff 1 r 1).mp hpotential
        simpa [upperTri] using this
      have hn : 2 < n := by
        have := hcoord.remainder_lt
        omega
      have hvalue : a n = n + 2 := by
        have := hcoord.eqn
        omega
      have hcandidate : a n - (n + 1) = 1 := by omega
      have honeSeen : 1 ∈ valuesThrough n := by
        apply mem_valuesThrough_iff.mpr
        exact ⟨1, by omega, by decide⟩
      exact Or.inr (Or.inr (.forced n firstTime rfl hcert hfirst
        hfirstTime habove hn hvalue hcert.near_target hcandidate honeSeen
        hcan))

/-- The remaining state is genuinely reachable: target five's canonical
start is time five with `a 5=7`, quotient one, remainder two and level one.
The subtraction candidate is one, already in the history, so step six is a
forced addition. -/
theorem canonicalLevelOne_forcedQOne_five :
    CanonicalLevelOneForcedQOneResidual 5 (targetStartNode 5) := by
  have hfirst : FirstAt a 7 5 := by
    constructor
    · decide
    · intro u hu
      have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by omega
      rcases hcases with h | h | h | h | h <;> subst u <;> decide
  have hcert : TargetStartCertificate 5 5 := {
    near_target := Or.inr rfl
    time_ready := by decide
    value_ready := by decide
    witnesses := ⟨1, 2, 5, ⟨by decide, by decide⟩,
      by decide, hfirst⟩
  }
  exact .forced 5 5 rfl hcert hfirst (by decide) (by decide)
    (by decide) (by decide) (Or.inr rfl) (by decide)
    (by decide) (by decide)

end Recaman
