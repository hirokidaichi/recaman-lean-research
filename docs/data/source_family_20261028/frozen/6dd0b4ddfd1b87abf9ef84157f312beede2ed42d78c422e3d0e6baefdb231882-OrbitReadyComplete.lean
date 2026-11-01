import Recaman.NormalSemanticBoundary
import Recaman.NonnegativeSemantic
import Recaman.CanonicalLevelOne

namespace Recaman

/-! # Orbit-ready normal local closure

`OrbitReadyNormalCertificate` restores the actual current orbit state and
the absolute-time precondition missing from the broad ordinary-normal
certificate.  This module classifies every potential sign at such a state.

Negative potential uses the complete negative-normal theorem.  Nonnegative
potential at or above the target gives coverage, including the quotient-zero
case after its forced addition.  A nonnegative undershoot first reduces to
the literal level band zero, one, and two.  The final theorems below discharge
that band as well, yielding total local closure on orbit-ready normal nodes.
-/

/-- Exact low-level boundary for an orbit-ready normal node.  The residual
retains both the strengthened node certificate and the complete numeric
boundary returned by the nonnegative epoch analysis. -/
inductive OrbitReadyLowLevelResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | low
      (time quotient remainder level : Nat)
      (ready : OrbitReadyNormalCertificate target parent
        time quotient remainder)
      (lowLevel : NonnegativeLowLevelResidualAt target (a time)
        time quotient remainder level) :
      OrbitReadyLowLevelResidual target parent

/-- A quotient-zero state whose nonnegative potential is at least the target
also closes semantically.  Equality is already an occurrence.  Under strict
inequality, the forced addition gives coordinates `(1,r)`; the next
low-quotient transition records `r-1`, which lies between the target and the
old anchor `r`. -/
theorem zeroQuotient_potential_aboveTarget_phaseSemanticStep
    {target n r : Nat}
    (htarget : 0 < target)
    (hcoord : CoordinatesAt n 0 r)
    (habove : Int.ofNat target ≤ potential 0 r) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  have hvalue : a n = r := by
    simpa [potential, upperTri] using hcoord.eqn
  by_cases hcurrent : a n = target
  · exact Or.inl ⟨n, hcurrent⟩
  have hstrict : target < r := by
    have htargetR : target ≤ r := by
      simpa [potential, upperTri] using habove
    omega
  rcases coordinates_zeroQuotient_next hcoord with
    ⟨_, hnextCoord, _⟩
  let level := r - 1
  have hpotential : potential 1 r = Int.ofNat level := by
    apply (potential_eq_ofNat_iff 1 r level).mpr
    simp only [level, upperTri]
    omega
  have hseen : level ∈ valuesThrough (n + 2) := by
    simpa only [Nat.add_assoc] using
      (lowQuotient_level_seen_next hnextCoord (by omega) hpotential)
  rcases history_member_has_firstAt hseen with
    ⟨firstTime, _, hfirst⟩
  have hcoverage : CoverageStep target (a n) n := by
    exact Or.inr ⟨level, firstTime, (by simp only [level]; omega), hfirst,
      (by simp only [level]; omega)⟩
  exact canonicalCoverage_phaseSemantic htarget hcoverage

/-- A forced addition at quotient one exposes coverage one transition later.

On potential level `level`, quotient-one coordinates say
`a n = n+1+level`.  The forced child is `2n+2+level`, whose next subtraction
candidate is `n+level`.  Target/time readiness, together with strictness of
the old value when `level=0`, puts this candidate at or above the target; it
is exactly one below the old anchor.  Legal subtraction makes it fresh and
blocked subtraction says it was already seen. -/
theorem quotientOne_forcedAddition_phaseSemanticStep
    {target n r level : Nat}
    (htarget : 0 < target)
    (_htimeReady : target ≤ n + 1)
    (htargetValue : target < a n)
    (hcoord : CoordinatesAt n 1 r)
    (hpotential : potential 1 r = Int.ofNat level)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  have hr : r = 1 + level := by
    simpa [upperTri] using
      (potential_eq_ofNat_iff 1 r level).mp hpotential
  have hvalue : a n = n + 1 + level := by
    have heq := hcoord.eqn
    omega
  have hnext := a_succ_of_not_canSubtract hnot
  have hnextValue : a (n + 1) = 2 * n + 2 + level := by omega
  let candidate := n + level
  have hcandidate : a (n + 1) - (n + 2) = candidate := by
    simp only [candidate]
    omega
  have htargetCandidate : target ≤ candidate := by
    simp only [candidate]
    by_cases hlevelZero : level = 0
    · subst level
      omega
    · omega
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
          ⟨firstTime, _, hfirst⟩
        exact Or.inr ⟨candidate, firstTime, htargetCandidate, hfirst,
          hcandidateDrop⟩
  exact canonicalCoverage_phaseSemantic htarget hcoverage

/-- The low-level boundary is itself locally complete.  Legal subtraction
closes directly; a blocked state with quotient at least two uses the general
two-quotient history frontier; quotient one uses the forced-addition
lookahead above. -/
theorem OrbitReadyLowLevelResidual.phaseSemanticStep
    {target : Nat} {parent : PhaseSearchNode}
    (h : OrbitReadyLowLevelResidual target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent := by
  cases h with
  | low n q r level hready hlow =>
      rw [hready.node_eq]
      by_cases hcurrent : a n = target
      · exact Or.inl ⟨n, hcurrent⟩
      have habove : target < a n := by
        exact Nat.lt_of_le_of_ne hlow.target_le_value (Ne.symm hcurrent)
      by_cases hcan : CanSubtract (n + 1) (stateAt n)
      · exact canonical_legalSubtraction_phaseSemantic
          hready.target_positive habove hcan
      · by_cases hqOne : q = 1
        · subst q
          exact quotientOne_forcedAddition_phaseSemanticStep
            hready.target_positive hlow.time_ready habove hlow.coordinates
            hlow.potential_eq hcan
        · have hqPositive : 0 < q := hlow.quotient_positive
          have hqTwo : 2 ≤ q := by omega
          exact canonical_forcedAddition_twoQuotient_phaseSemantic
            hready.target_positive hlow.time_ready habove hlow.coordinates
            hqTwo hcan

/-- Complete sign classification for one orbit-ready certificate.  The only
unclosed outcome is an explicit nonnegative potential level at most two. -/
theorem OrbitReadyNormalCertificate.phaseSemanticStep_or_lowLevel
    {target : Nat} {parent : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target parent time q r) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      OrbitReadyLowLevelResidual target parent := by
  by_cases hnegative : potential q r < 0
  · rcases h.negative_phaseSemanticStep hnegative with hoccurs | hchild
    · exact Or.inl hoccurs
    · exact Or.inr (Or.inl hchild)
  have hnonnegative : 0 ≤ potential q r := by omega
  by_cases habove : Int.ofNat target ≤ potential q r
  · cases q with
    | zero =>
        rw [h.node_eq]
        rcases zeroQuotient_potential_aboveTarget_phaseSemanticStep
            h.target_positive h.coordinates habove with hoccurs | hchild
        · exact Or.inl hoccurs
        · exact Or.inr (Or.inl hchild)
    | succ q =>
        have htimePositive : 0 < time := by
          by_cases hzero : time = 0
          · subst time
            have htargetZero : target ≤ 0 := by
              simpa [a, stateAt, initial] using h.target_le_value
            exact False.elim ((Nat.not_lt_of_ge htargetZero)
              h.target_positive)
          · omega
        have hcoverage :=
          positiveQuotient_potential_aboveTarget_gives_coverageStep
            htimePositive (by omega) h.time_ready h.coordinates habove
        rw [h.node_eq]
        rcases canonicalCoverage_phaseSemantic h.target_positive
            hcoverage with hoccurs | hchild
        · exact Or.inl hoccurs
        · exact Or.inr (Or.inl hchild)
  · have hbelow : potential q r < Int.ofNat target := by omega
    rcases nonnegative_epoch_phaseSemanticStep_or_lowLevel
        h.target_positive h.time_ready h.target_le_value (Nat.le_refl _)
        h.coordinates hnonnegative hbelow with
      hoccurs | hchild | ⟨level, hlow⟩
    · exact Or.inl hoccurs
    · rw [h.node_eq]
      exact Or.inr (Or.inl hchild)
    · exact Or.inr (Or.inr (.low time q r level h hlow))

/-- Existential wrapper: every orbit-ready normal node has the same complete
local classification, independently of which current coordinates witness
readiness. -/
theorem OrbitReadyNormalInvariant.phaseSemanticStep_or_lowLevel
    {target : Nat} {parent : PhaseSearchNode}
    (h : OrbitReadyNormalInvariant target parent) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      OrbitReadyLowLevelResidual target parent := by
  rcases h with ⟨time, q, r, hready⟩
  exact hready.phaseSemanticStep_or_lowLevel

/-- Certificate-level total closure, obtained by discharging the exact
low-level boundary from the sign classification. -/
theorem OrbitReadyNormalCertificate.phaseSemanticStep
    {target : Nat} {parent : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target parent time q r) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent := by
  rcases h.phaseSemanticStep_or_lowLevel with
    hoccurs | hchild | hlow
  · exact Or.inl hoccurs
  · exact Or.inr hchild
  · exact hlow.phaseSemanticStep

/-- Complete current-state local semantic step for orbit-ready normal nodes.
All potential signs, quotient zero, and the low levels zero through two are
discharged in the existing semantic domain and phase rank. -/
theorem OrbitReadyNormalInvariant.phaseSemanticStep
    {target : Nat} {parent : PhaseSearchNode}
    (h : OrbitReadyNormalInvariant target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent := by
  rcases h with ⟨time, q, r, hready⟩
  exact hready.phaseSemanticStep

end Recaman
