import Recaman.Coverage
import Recaman.CoordinateDynamics
import Recaman.Gate
import Recaman.Oracle

namespace Recaman

/-- The abstract two-step gate, specialized to an actual stateAt time, gives
an actual occurrence witness for m. -/
theorem exactGate_at_occurs {u m : Nat}
    (hmpos : 0 < m)
    (hvalue : (stateAt u).value = 2 * u + m + 3)
    (hintermediate : gateIntermediate u m ∉ (stateAt u).seen)
    (hmfresh : m ∉ (stateAt u).seen) :
    ∃ t, a t = m := by
  have hgate := exactGate_sufficient
    (state := stateAt u) hmpos hvalue hintermediate hmfresh
  have hstate : stateAt (u + 2) =
      step (u + 2) (step (u + 1) (stateAt u)) := by
    rw [show u + 2 = (u + 1) + 1 by omega]
    rw [stateAt_succ, stateAt_succ]
  refine ⟨u + 2, ?_⟩
  change (stateAt (u + 2)).value = m
  rw [hstate]
  exact hgate

/-- The local +--- escape family, specialized to the actual orbit, also gives
an occurrence witness for m. -/
theorem localEscape_at_occurs {s m : Nat}
    (h : EscapeAssumptions s m (stateAt (s - 1))) :
    ∃ t, a t = m := by
  have hlocal := localEscape_lands h
  cases s with
  | zero =>
      have hlarge := h.s_large
      omega
  | succ u =>
      refine ⟨(u + 1) + 3, ?_⟩
      simpa [a, stateAt, Nat.add_assoc] using hlocal

/-- A valid direct target equation supplies one CoverageStep: landing is the
terminal branch, while obstruction is the double-descent branch. -/
theorem targetEquation_gives_coverageStep {m v f k : Nat}
    (hm : 0 < m) (hfirst : FirstAt a v f)
    (hequation : TargetEquation f v m k) :
    CoverageStep m v f := by
  rcases targetDescent_lands_or_doubleDescent
    hfirst hm hequation with hlanding |
      ⟨length, y, fy, _, hmle, hylt, hfirstY, hfy⟩
  · exact Or.inl ⟨f + k, hlanding⟩
  · exact Or.inr ⟨y, fy, hmle, hfirstY, hylt⟩

/-- Every legal subtraction lands on a new, strictly smaller value.  Thus if
the landing value remains above the target, the transition itself is already
a `CoverageStep`; no blocker is required. -/
theorem subtraction_gives_coverageStep {m n : Nat}
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hmnext : m ≤ a (n + 1)) :
    CoverageStep m (a n) n := by
  have hfirstNext := firstAt_succ_of_canSubtract hcan
  have hnext := a_succ_of_canSubtract hcan
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hlt : a (n + 1) < a n := by omega
  exact Or.inr ⟨a (n + 1), n + 1, hmnext, hfirstNext, hlt⟩

/-- Either local landing mechanism immediately discharges a CoverageStep,
regardless of the current proof-search node. -/
theorem occurrence_gives_coverageStep {m v f : Nat}
    (hmOccurs : ∃ t, a t = m) : CoverageStep m v f :=
  Or.inl hmOccurs

/-- The level surface G=m is exactly a target equation: q planned
subtractions from value v at time f have arithmetic endpoint m. -/
theorem targetEquation_of_quotRem_potential {f v q r m : Nat}
    (hqr : QuotRem f v q r)
    (hpotential : potential q r = Int.ofNat m) :
    TargetEquation f v m q := by
  rcases hqr with ⟨heq, _⟩
  have hr : r = upperTri q + m :=
    (potential_eq_ofNat_iff q r m).mp hpotential
  unfold TargetEquation descentDrop
  rw [Nat.mul_comm q f, heq, hr]
  omega

/-- At a first occurrence, membership in the target surface G=m directly
supplies the descent branch of CoverageStep. -/
theorem targetSurface_gives_coverageStep {f v q r m : Nat}
    (hm : 0 < m) (hfirst : FirstAt a v f)
    (hcoord : CoordinatesAt f q r)
    (hpotential : potential q r = Int.ofNat m) :
    CoverageStep m v f := by
  unfold CoordinatesAt at hcoord
  rw [hfirst.1] at hcoord
  exact targetEquation_gives_coverageStep hm hfirst
    (targetEquation_of_quotRem_potential hcoord hpotential)

/-- At quotient zero, membership in `G=m` is already the occurrence `aᵤ=m`. -/
theorem targetSurface_zero_occurs {u r m : Nat}
    (hcoord : CoordinatesAt u 0 r)
    (hpotential : potential 0 r = Int.ofNat m) :
    ∃ t, a t = m := by
  have hr : r = m := by
    simpa [upperTri] using
      (potential_eq_ofNat_iff 0 r m).mp hpotential
  have heq := hcoord.eqn
  refine ⟨u, ?_⟩
  simp at heq
  omega

/-- Quotient one needs no freshness hypothesis: if `m` is old it has already
occurred, and if it is fresh the next legal subtraction lands exactly on `m`. -/
theorem targetSurface_one_occurs {u r m : Nat}
    (hcoord : CoordinatesAt u 1 r)
    (hpotential : potential 1 r = Int.ofNat m) :
    ∃ t, a t = m := by
  have hr : r = m + 1 := by
    have hr' := (potential_eq_ofNat_iff 1 r m).mp hpotential
    simp [upperTri] at hr'
    omega
  have heq := hcoord.eqn
  have hvalue : a u = u + m + 1 := by
    simp at heq
    omega
  by_cases hmzero : m = 0
  · subst m
    exact ⟨0, by decide⟩
  · by_cases hseen : m ∈ (stateAt u).seen
    · have hmem : m ∈ valuesThrough u := by
        simpa [valuesThrough] using hseen
      rcases mem_valuesThrough_iff.mp hmem with ⟨t, _, ht⟩
      exact ⟨t, ht⟩
    · have hcan : CanSubtract (u + 1) (stateAt u) := by
        constructor
        · change u + 1 < a u
          omega
        · have hcand : (stateAt u).value - (u + 1) = m := by
            change a u - (u + 1) = m
            omega
          rw [hcand]
          exact hseen
      have hnext := a_succ_of_canSubtract hcan
      refine ⟨u + 1, ?_⟩
      omega

/-- Thus every target-surface point of quotient at most one discharges the
target unconditionally. -/
theorem targetSurface_lowQuotient_occurs {u q r m : Nat}
    (hq : q ≤ 1) (hcoord : CoordinatesAt u q r)
    (hpotential : potential q r = Int.ofNat m) :
    ∃ t, a t = m := by
  have hcases : q = 0 ∨ q = 1 := by omega
  rcases hcases with hzero | hone
  · subst q
    exact targetSurface_zero_occurs hcoord hpotential
  · subst q
    exact targetSurface_one_occurs hcoord hpotential

/-- Exact-gate values are precisely the q=2 part of the target surface G=m. -/
theorem exactGate_targetSurface {u m : Nat} (hlarge : m + 3 < u) :
    QuotRem u (2 * u + m + 3) 2 (m + 3) ∧
      potential 2 (m + 3) = Int.ofNat m := by
  constructor
  · constructor <;> omega
  · simp [potential]

theorem exactGate_targetEquation {u m : Nat} (hlarge : m + 3 < u) :
    TargetEquation u (2 * u + m + 3) m 2 := by
  rcases exactGate_targetSurface hlarge with ⟨hqr, hpotential⟩
  exact targetEquation_of_quotRem_potential hqr hpotential

/-- The post-addition state of the +--- family lies on the q=3 target
surface, so its remaining three subtractions are exactly the target descent. -/
theorem localEscape_postAddition_targetEquation {s m : Nat}
    (hlarge : m + 9 < s) :
    TargetEquation s (escapeAfterAddition s m) m 3 := by
  exact targetEquation_of_quotRem_potential
    (postAddition_quotRem hlarge) (postAddition_potential m)

/-- A forced regular addition from G=m+(2q+1) enters the target surface G=m. -/
theorem regularAddition_enters_targetSurface {n q r m : Nat}
    (hcoord : CoordinatesAt n q r) (hregular : q ≤ r)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hpotential : potential q r = Int.ofNat (m + (2 * q + 1))) :
    CoordinatesAt (n + 1) (q + 1) (r - q) ∧
      potential (q + 1) (r - q) = Int.ofNat m := by
  rcases coordinates_add_regular hcoord hregular hnot with
    ⟨hnextCoord, hnextPotential⟩
  constructor
  · exact hnextCoord
  · rw [hpotential] at hnextPotential
    have hcast : Int.ofNat (m + (2 * q + 1)) =
        Int.ofNat m + Int.ofNat (2 * q + 1) := rfl
    rw [hcast] at hnextPotential
    omega

end Recaman
