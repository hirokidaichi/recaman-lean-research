import Recaman.CanonicalOracle

namespace Recaman

/-! # Canonical potential level zero

The regular nonnegative funnel reduces a canonical level-zero state either to
coverage, a smaller semantic normal anchor, or the exact quotient-one
successor boundary `a target = target + 1`.
-/

/-- Proof-relevant refinement of a canonical low-level residual to level
zero.  The constructor repeats the evidence because the residual is
`Prop`-valued and therefore cannot expose its natural-number witnesses by a
computational projection. -/
inductive CanonicalLowLevelResidual.IsZero
    {target : Nat} {parent : PhaseSearchNode}
    (h : CanonicalLowLevelResidual target parent) : Prop
  | intro
      (orbitTime quotient remainder firstTime : Nat)
      (parent_eq : parent = targetStartNode orbitTime)
      (certificate : TargetStartCertificate target orbitTime)
      (coordinates : CoordinatesAt orbitTime quotient remainder)
      (current_first : FirstAt a (a orbitTime) firstTime)
      (firstTime_le : firstTime ≤ orbitTime)
      (current_above_target : target < a orbitTime)
      (quotient_positive : 0 < quotient)
      (potential_zero : potential quotient remainder = 0)
      (target_positive : 0 < target)
      (source_eq : h = .low orbitTime quotient remainder firstTime 0
        parent_eq certificate coordinates current_first firstTime_le
        current_above_target quotient_positive (by simpa using potential_zero)
        (by omega) target_positive) :
      IsZero h

/-- Minimal unresolved form of canonical level zero.  The target-ready time
is forced to equal the target itself, and the coordinates are forced to
`(1,1)`, equivalently `a target = target+1`. -/
inductive CanonicalSuccessorResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | successor
      (firstTime : Nat)
      (parent_eq : parent = targetStartNode target)
      (certificate : TargetStartCertificate target target)
      (coordinates : CoordinatesAt target 1 1)
      (current_first : FirstAt a (a target) firstTime)
      (firstTime_le : firstTime ≤ target)
      (successor_value : a target = target + 1) :
      CanonicalSuccessorResidual target parent

/-- A canonical low-level residual at level zero either closes semantically
or is exactly the successor boundary above.  The quotient descent uses only
actual future states.  A resulting first occurrence is certified at its own
horizon, never at the old canonical horizon. -/
theorem canonicalLowLevel_zero_phaseSemanticStep_or_successor
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (hres : CanonicalLowLevelResidual target parent)
    (hzero : hres.IsZero) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      CanonicalSuccessorResidual target parent := by
  cases hzero with
  | intro n q r firstTime hparent hcert hcoord hfirst hfirstTime
      hcurrent hqpos hpotentialZero _ _ =>
      have hnonnegative : 0 ≤ potential q r := by
        rw [hpotentialZero]
        omega
      rcases nonnegative_epoch_lowQuotient_or_coverage_with_value
          hcert.time_ready hcoord hnonnegative with
        ⟨t, k, s, hnt, _, htvalue, hstrict, hsame, htcoord,
          htpotential, hlow | hcoverage⟩
      · have htpotentialZero : potential k s = 0 := by
          rw [htpotential, hpotentialZero]
        have hnpos : 0 < n := by
          have hrlt := hcoord.remainder_lt
          omega
        have htpos : 0 < t := Nat.lt_of_lt_of_le hnpos hnt
        have hk : k = 1 := by
          have hkCases : k = 0 ∨ k = 1 := by omega
          rcases hkCases with hkzero | hkone
          · subst k
            have hs : s = 0 := by
              simpa [potential, upperTri] using htpotentialZero
            have heq := htcoord.eqn
            subst s
            simp at heq
            have hapos := a_pos_of_pos_time htpos
            omega
          · exact hkone
        subst k
        have hs : s = 1 := by
          have hsCast : Int.ofNat s - 1 = 0 := by
            simpa [potential, upperTri] using htpotentialZero
          have hsCast' : Int.ofNat s = Int.ofNat 1 := by
            have hliteral : Int.ofNat s = (1 : Int) := by omega
            exact hliteral
          exact Int.ofNat_inj.mp hsCast'
        subst s
        rcases hstrict with htimeEq | hvalueDrop
        · subst t
          have hq : q = 1 := (hsame rfl).symm
          subst q
          have hr : r = 1 := by
            have hrCast : Int.ofNat r - 1 = 0 := by
              simpa [potential, upperTri] using hpotentialZero
            have hrCast' : Int.ofNat r = Int.ofNat 1 := by
              have hliteral : Int.ofNat r = (1 : Int) := by omega
              exact hliteral
            exact Int.ofNat_inj.mp hrCast'
          subst r
          have hvalue : a n = n + 1 := by
            have heq := hcoord.eqn
            omega
          have htimeTarget : n = target := by
            rcases hcert.near_target with hnear | hnear
            · have hn : n = target - 1 := hnear
              have htargetValue : a n = target := by omega
              exact False.elim (Nat.ne_of_gt hcurrent htargetValue)
            · exact hnear
          subst n
          exact Or.inr (Or.inr (.successor firstTime hparent hcert hcoord
            hfirst hfirstTime hvalue))
        · have htargetChild : target ≤ a t := by
            have heq := htcoord.eqn
            exact Nat.le_trans hcert.time_ready (by omega)
          rcases history_member_has_firstAt (current_mem_valuesThrough t) with
            ⟨ft, hft, hfirstT⟩
          let child : PhaseSearchNode := ⟨t, a t, .normal, a t⟩
          have hsemantic : PhaseSemanticInvariant target child := .normal
            (firstAt_normalSearchInvariant htarget htargetChild hfirstT hft)
          have hprogress : PhaseSearchProgress target child
              (targetStartNode n) :=
            phaseSearchProgress_of_horizonAndAnchor hnt hvalueDrop
          rw [hparent]
          exact Or.inr (Or.inl ⟨child, hsemantic, hprogress⟩)
      · rcases canonicalCoverage_phaseSemantic htarget hcoverage with
          hoccurs | hchild
        · exact Or.inl hoccurs
        · rw [hparent]
          exact Or.inr (Or.inl hchild)

/-- The concrete target-two low-level example reduces to the successor
boundary `a 2 = 3`; this confirms that the final residual is inhabited. -/
theorem canonicalSuccessorResidual_two :
    CanonicalSuccessorResidual 2 (targetStartNode 2) := by
  have hfirst : FirstAt a 3 2 := by
    constructor
    · decide
    · intro u hu
      have hcases : u = 0 ∨ u = 1 := by omega
      rcases hcases with h | h <;> subst u <;> decide
  have hcert : TargetStartCertificate 2 2 := {
    near_target := Or.inr rfl
    time_ready := by decide
    value_ready := by decide
    witnesses := ⟨1, 1, 2, ⟨by decide, by decide⟩, by decide, hfirst⟩
  }
  exact .successor 2 rfl hcert ⟨by decide, by decide⟩ hfirst
    (by decide) (by decide)

/-- The apparent successor residual is actually successful within two orbit
steps.  From `a target = target+1`, subtraction by `target+1` is blocked by
the already-seen zero, so the next value is `2*target+2`.  Subtracting
`target+2` then either lands on the target or is blocked because the target
has already occurred. -/
theorem CanonicalSuccessorResidual.target_occurs
    {target : Nat} {parent : PhaseSearchNode}
    (htarget : 0 < target)
    (h : CanonicalSuccessorResidual target parent) :
    ∃ witness, a witness = target := by
  cases h with
  | successor firstTime parent_eq certificate coordinates current_first
      firstTime_le successor_value =>
      have hzeroSeen : 0 ∈ valuesThrough target :=
        mem_valuesThrough_iff.mpr ⟨0, Nat.zero_le _, rfl⟩
      have hnotFirst : ¬ CanSubtract (target + 1) (stateAt target) := by
        intro hcan
        have hcandidate : a target - (target + 1) = 0 := by omega
        have hnotSeen : a target - (target + 1) ∉ valuesThrough target := by
          simpa [a, valuesThrough] using hcan.2
        exact hnotSeen (by simpa [hcandidate] using hzeroSeen)
      have hnext := a_succ_of_not_canSubtract hnotFirst
      have hnextValue : a (target + 1) = 2 * target + 2 := by
        rw [successor_value] at hnext
        omega
      by_cases hcanSecond :
          CanSubtract (target + 2) (stateAt (target + 1))
      · have hlanding := a_succ_of_canSubtract hcanSecond
        refine ⟨target + 2, ?_⟩
        rw [hnextValue] at hlanding
        rw [show target + 1 + 1 = target + 2 by omega] at hlanding
        omega
      · have hpositive : target + 2 < (stateAt (target + 1)).value := by
          change target + 2 < a (target + 1)
          rw [hnextValue]
          omega
        have hseen :
            (stateAt (target + 1)).value - (target + 2) ∈
              (stateAt (target + 1)).seen := by
          by_cases hmem :
              (stateAt (target + 1)).value - (target + 2) ∈
                (stateAt (target + 1)).seen
          · exact hmem
          · exact False.elim (hcanSecond ⟨hpositive, hmem⟩)
        have hcandidate :
            (stateAt (target + 1)).value - (target + 2) = target := by
          change a (target + 1) - (target + 2) = target
          rw [hnextValue]
          omega
        have hseenTarget : target ∈ valuesThrough (target + 1) := by
          change a (target + 1) - (target + 2) ∈
            valuesThrough (target + 1) at hseen
          have hcandidate' :
              a (target + 1) - (target + 2) = target := by
            simpa [a] using hcandidate
          rwa [hcandidate'] at hseen
        rcases mem_valuesThrough_iff.mp hseenTarget with
          ⟨witness, _, hvalue⟩
        exact ⟨witness, hvalue⟩

end Recaman
