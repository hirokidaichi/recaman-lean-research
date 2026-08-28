import Recaman.LandingSurfaces

namespace Recaman

/-- A subtraction-side borrow chart already supplies a target equation at the
pre-state.  The borrow count cancels completely: landing at quotient `k` on
`G=m` is equivalent to planning `k+1` subtractions from the old value. -/
theorem sub_borrowTarget_prestate_targetEquation {n q r b s k m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hquotient : q = b + k + 1)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    TargetEquation n (a n) m (k + 1) := by
  have heq := hcoord.eqn
  unfold BorrowTargetPreimage at hpreimage
  subst q
  have hnq : n * (b + k + 1) = b * n + k * n + n := by
    simp [Nat.mul_add, Nat.mul_comm]
  have hbn : b * (n + 1) = b * n + b := by
    simp [Nat.mul_add]
  have hkn : (k + 1) * n = k * n + n := by
    simp [Nat.add_mul]
  have htri : upperTri (k + 1) = upperTri k + k + 1 := by
    simp [upperTri]
  unfold TargetEquation descentDrop
  rw [heq]
  rw [hnq, hkn, htri]
  rw [hbn] at hpreimage
  omega

/-- Addition-side landing at positive quotient `k` gives an exact formula for
the pre-state value. -/
theorem add_borrowTarget_prestate_value {n q r b s k m : Nat}
    (hcoord : CoordinatesAt n q r)
    (_hborrow : BorrowData n q r b s)
    (hk : 0 < k) (hquotient : q + 1 = b + k)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    a n = (k - 1) * (n + 1) + upperTri k + m := by
  cases k with
  | zero => omega
  | succ p =>
      have hq : q = b + p := by omega
      have heq := hcoord.eqn
      unfold BorrowTargetPreimage at hpreimage
      subst q
      have hnq : n * (b + p) = b * n + p * n := by
        simp [Nat.mul_add, Nat.mul_comm]
      have hbn : b * (n + 1) = b * n + b := by
        simp [Nat.mul_add]
      have hpn : p * (n + 1) = p * n + p := by
        simp [Nat.mul_add]
      rw [heq, hnq]
      rw [hbn] at hpreimage
      simp only [Nat.add_sub_cancel]
      rw [hpn]
      omega

/-- If an actual addition lands on `(p+2,G=m)`, the blocked subtraction at the
pre-state is a concrete `ActualBlocker` whose value is at least `m`. -/
theorem add_borrowTarget_prestate_blocker {n q r b s p m : Nat}
    (hfirst : FirstAt a (a n) n)
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hquotient : q + 1 = b + (p + 2))
    (hpreimage : BorrowTargetPreimage n q r b (p + 2) m) :
    ∃ y, m ≤ y ∧ ActualBlocker n (a n) 0 y := by
  let y := p * (n + 1) + upperTri (p + 2) + m
  have hvalue := add_borrowTarget_prestate_value hcoord hborrow
    (k := p + 2) (by omega) hquotient hpreimage
  have hsplit : (p + 2 - 1) * (n + 1) = p * (n + 1) + (n + 1) := by
    simp [Nat.add_mul]
  have htri : 3 ≤ upperTri (p + 2) := by
    have hmono := upperTri_mono (show 2 ≤ p + 2 by omega)
    simpa using hmono
  have hpositive : n + 1 < a n := by
    rw [hvalue, hsplit]
    omega
  have hcandidate : a n - (n + 1) = y := by
    rw [hvalue, hsplit]
    simp only [y]
    omega
  have hseen : y ∈ valuesThrough n := by
    by_cases hyseen : y ∈ valuesThrough n
    · exact hyseen
    · have hcan : CanSubtract (n + 1) (stateAt n) := by
        constructor
        · simpa [a] using hpositive
        · change a n - (n + 1) ∉ valuesThrough n
          rw [hcandidate]
          exact hyseen
      exact False.elim (hnot hcan)
  have hrun : DescentRun n (a n) 0 := by
    constructor
    · rfl
    · intro i hi
      omega
  let blocker : ActualBlocker n (a n) 0 y := {
    first_v := hfirst
    run := hrun
    blocker_positive := by simpa using hpositive
    blocker_candidate := by simpa using hcandidate
    blocker_seen := hseen
  }
  refine ⟨y, ?_, blocker⟩
  simp only [y]
  omega

/-- At a first occurrence, an addition-side borrow chart gives a CoverageStep. -/
theorem add_borrowTarget_gives_coverageStep {n q r b s k m : Nat}
    (hm : 0 < m) (hfirst : FirstAt a (a (n + 1)) (n + 1))
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hquotient : q + 1 = b + k)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    CoverageStep m (a (n + 1)) (n + 1) := by
  exact targetEquation_gives_coverageStep hm hfirst
    (add_borrowTarget_gives_targetEquation hcoord hborrow hnot
      hquotient hpreimage)

/-- At a first occurrence, a subtraction-side borrow chart gives a CoverageStep. -/
theorem sub_borrowTarget_gives_coverageStep {n q r b s k m : Nat}
    (hm : 0 < m) (hfirst : FirstAt a (a (n + 1)) (n + 1))
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hquotient : q = b + k + 1)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    CoverageStep m (a (n + 1)) (n + 1) := by
  exact targetEquation_gives_coverageStep hm hfirst
    (sub_borrowTarget_gives_targetEquation hcoord hborrow hcan
      hquotient hpreimage)

/-- Stronger pre-state coverage connection for subtraction charts.  Unlike the
next-state theorem above, this needs neither subtraction legality nor a first
occurrence hypothesis at time `n+1`. -/
theorem sub_borrowTarget_prestate_gives_coverageStep {n q r b s k m : Nat}
    (hfirst : FirstAt a (a n) n)
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hquotient : q = b + k + 1)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    CoverageStep m (a n) n := by
  cases m with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m =>
      exact targetEquation_gives_coverageStep (by omega) hfirst
        (sub_borrowTarget_prestate_targetEquation hcoord hborrow
          hquotient hpreimage)

/-- Addition charts of destination quotient at least two also supply a
pre-state `CoverageStep`: failure of subtraction is itself the required
history blocker, so no gate-freshness assumption is needed. -/
theorem add_borrowTarget_prestate_gives_coverageStep_high
    {n q r b s p m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hquotient : q + 1 = b + (p + 2))
    (hpreimage : BorrowTargetPreimage n q r b (p + 2) m) :
    CoverageStep m (a n) n := by
  let y := p * (n + 1) + upperTri (p + 2) + m
  have hvalue := add_borrowTarget_prestate_value hcoord hborrow
    (k := p + 2) (by omega) hquotient hpreimage
  have hsplit : (p + 2 - 1) * (n + 1) = p * (n + 1) + (n + 1) := by
    simp [Nat.add_mul]
  have hpositive : n + 1 < a n := by
    rw [hvalue, hsplit]
    have htri : 3 ≤ upperTri (p + 2) := by
      have hmono := upperTri_mono (show 2 ≤ p + 2 by omega)
      simpa using hmono
    omega
  have hcandidate : a n - (n + 1) = y := by
    rw [hvalue, hsplit]
    simp only [y]
    omega
  have hseen : y ∈ valuesThrough n := by
    by_cases hyseen : y ∈ valuesThrough n
    · exact hyseen
    · have hcan : CanSubtract (n + 1) (stateAt n) := by
        constructor
        · simpa [a] using hpositive
        · change a n - (n + 1) ∉ valuesThrough n
          rw [hcandidate]
          exact hyseen
      exact False.elim (hnot hcan)
  rcases history_member_has_firstAt hseen with ⟨fy, _, hfirstY⟩
  have hylt : y < a n := by omega
  have hmy : m ≤ y := by
    simp only [y]
    omega
  exact Or.inr ⟨y, fy, hmy, hfirstY, hylt⟩

/-- Complete addition-side pre-state connection.  Low destination quotients
`0,1` give an unconditional occurrence after the actual addition; every
higher destination quotient gives the blocker branch above. -/
theorem add_borrowTarget_prestate_gives_coverageStep
    {n q r b s k m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hquotient : q + 1 = b + k)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    CoverageStep m (a n) n := by
  cases k with
  | zero =>
      rcases coordinates_add_enters_borrowTarget hcoord hborrow hnot
        hquotient hpreimage with ⟨hnext, hpotential⟩
      exact occurrence_gives_coverageStep
        (targetSurface_zero_occurs hnext hpotential)
  | succ k =>
      cases k with
      | zero =>
          rcases coordinates_add_enters_borrowTarget hcoord hborrow hnot
            hquotient hpreimage with ⟨hnext, hpotential⟩
          exact occurrence_gives_coverageStep
            (targetSurface_one_occurs hnext hpotential)
      | succ p =>
          exact add_borrowTarget_prestate_gives_coverageStep_high
            hcoord hborrow hnot hquotient hpreimage

/-- User-facing addition theorem: any actual addition transition whose borrow
coordinates land on `G=m` supplies a `CoverageStep` from the pre-state. -/
theorem coordinates_add_target_prestate_gives_coverageStep
    {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (htarget : potential (q + 1 - b) s = Int.ofNat m) :
    CoverageStep m (a n) n := by
  have hbq : b ≤ q + 1 := hborrow.le_q_add_one
  have hquotient : q + 1 = b + (q + 1 - b) :=
    (add_borrowQuotient_eq_iff hbq).mp rfl
  have hpreimage :
      BorrowTargetPreimage n q r b (q + 1 - b) m :=
    (potential_eq_iff_borrowTargetPreimage hborrow).mp htarget
  exact add_borrowTarget_prestate_gives_coverageStep
    hcoord hborrow hnot hquotient hpreimage

/-- User-facing subtraction theorem: any legal subtraction transition whose
borrow coordinates land on `G=m` already supplies a pre-state `CoverageStep`. -/
theorem coordinates_sub_target_prestate_gives_coverageStep
    {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (htarget : potential (q - 1 - b) s = Int.ofNat m) :
    CoverageStep m (a n) n := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  have hnext := coordinates_sub_borrowData hcoord hborrow hbq hcan
  have hs : s = upperTri (q - 1 - b) + m :=
    (potential_eq_ofNat_iff (q - 1 - b) s m).mp htarget
  have hvalueNext := hnext.1.eqn
  have hmnext : m ≤ a (n + 1) := by omega
  exact subtraction_gives_coverageStep hcan hmnext

/-- A forced addition from quotient at least three has a positive blocked
subtraction candidate which is at least the current time.  At a first
occurrence this is a length-zero actual blocker. -/
theorem add_highQuotient_prestate_blocker
    {n q r : Nat}
    (hfirst : FirstAt a (a n) n)
    (hcoord : CoordinatesAt n q r)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hq : 3 ≤ q) :
    ∃ y, n ≤ y ∧ ActualBlocker n (a n) 0 y := by
  have hn : 0 < n := by
    have hrlt := hcoord.remainder_lt
    omega
  have hmul : n * 3 ≤ n * q := Nat.mul_le_mul_left n hq
  have heq := hcoord.eqn
  have hvalueLower : n * 3 ≤ a n := by
    omega
  have hpositive : n + 1 < a n := by
    omega
  let y := a n - (n + 1)
  have hny : n ≤ y := by
    simp only [y]
    omega
  have hseen : y ∈ valuesThrough n := by
    by_cases hyseen : y ∈ valuesThrough n
    · exact hyseen
    · have hcan : CanSubtract (n + 1) (stateAt n) := by
        constructor
        · simpa [a] using hpositive
        · change a n - (n + 1) ∉ valuesThrough n
          simpa only [y] using hyseen
      exact False.elim (hnot hcan)
  have hrun : DescentRun n (a n) 0 := by
    constructor
    · rfl
    · intro i hi
      omega
  let blocker : ActualBlocker n (a n) 0 y := {
    first_v := hfirst
    run := hrun
    blocker_positive := by simpa using hpositive
    blocker_candidate := by simp [y]
    blocker_seen := hseen
  }
  exact ⟨y, hny, blocker⟩

/-- A forced addition from a one-borrow destination quotient at least four
discharges every target below the current time by the blocker branch. -/
theorem coordinates_add_oneBorrow_highQuotient_gives_coverageStep_below_time
    {n q r b m : Nat}
    (hfirst : FirstAt a (a n) n)
    (hcoord : CoordinatesAt n q r)
    (hb : b = 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hdestination : 4 ≤ q + 1 - b)
    (hmn : m ≤ n) :
    CoverageStep m (a n) n := by
  have hq : 3 ≤ q := by omega
  rcases add_highQuotient_prestate_blocker hfirst hcoord hnot hq with
    ⟨y, hny, hblocker⟩
  rcases hblocker.doubleDescent with ⟨hylt, fy, hfirstY, hfy⟩
  exact Or.inr
    ⟨y, fy, Nat.le_trans hmn hny, hfirstY, hylt⟩

end Recaman
