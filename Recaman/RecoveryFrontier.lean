import Recaman.RecoveryBudget
import Recaman.PrestateCoverage

namespace Recaman

/-- On the actual addition branch, one borrow into quotient at most three
always reaches the nonnegative half-space. -/
theorem coordinates_add_oneBorrow_lowQuotient_nonnegative
    {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hq : q ≤ 3)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    0 ≤ potential (q + 1 - b) s := by
  rw [add_oneBorrow_nonnegative_iff hborrow hb]
  have hbound := hcoord.twice_quotient_le
  have hqpos : 0 < q := by
    have hchamber := hborrow.eq_one_iff.mp hb
    omega
  have hcases : q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hcases with hone | htwo | hthree
  · subst q
    simp [upperTri]
    omega
  · subst q
    by_cases hthreshold : upperTri 2 + 2 ≤ n + 1 + r
    · exact hthreshold
    · simp at hthreshold
      have hn : n = 3 := by omega
      have hr : r = 0 := by omega
      subst n
      subst r
      have hcan : CanSubtract 4 (stateAt 3) := by decide
      exact False.elim (hnot hcan)
  · subst q
    by_cases hthreshold : upperTri 3 + 3 ≤ n + 1 + r
    · exact hthreshold
    · simp [upperTri] at hthreshold
      have heq := hcoord.eqn
      have hnCases : n = 5 ∨ n = 6 ∨ n = 7 := by omega
      rcases hnCases with hfive | hsix | hseven
      · subst n
        have ha : a 5 = 7 := by decide
        rw [ha] at heq
        omega
      · subst n
        have ha : a 6 = 13 := by decide
        rw [ha] at heq
        omega
      · subst n
        have ha : a 7 = 20 := by decide
        rw [ha] at heq
        omega

/-- On the legal subtraction branch, destination quotient at most three
(equivalently old quotient at most five) also guarantees recovery. -/
theorem coordinates_sub_oneBorrow_lowQuotient_nonnegative
    {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hcan : CanSubtract (n + 1) (stateAt n))
    (hdestination : q - 1 - b ≤ 3) :
    0 ≤ potential (q - 1 - b) s := by
  rw [sub_oneBorrow_nonnegative_iff hborrow hb]
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  have hbound := hcoord.twice_quotient_le
  have hqle : q ≤ 5 := by omega
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hcases with htwo | hthree | hfour | hfive
  · subst q
    simp [upperTri]
    omega
  · subst q
    simp [upperTri]
    omega
  · subst q
    simp
    omega
  · subst q
    by_cases hthreshold : upperTri (5 - 2) + 5 ≤ n + 1 + r
    · exact hthreshold
    · simp at hthreshold
      have hn : n = 9 := by omega
      have hr : r = 0 := by omega
      have heq := hcoord.eqn
      subst n
      subst r
      have ha : a 9 = 21 := by decide
      rw [ha] at heq
      omega

/-- Therefore a failed one-borrow addition recovery must land at quotient at
least four. -/
theorem coordinates_add_oneBorrow_negative_highQuotient
    {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hnegative : potential (q + 1 - b) s < 0) :
    4 ≤ q + 1 - b := by
  by_cases hlow : q ≤ 3
  · have hnonnegative :=
      coordinates_add_oneBorrow_lowQuotient_nonnegative
        hcoord hborrow hb hlow hnot
    omega
  · omega

/-- Target-independent blocker data exposed by a failed high-quotient
one-borrow addition.  The blocked candidate was first seen strictly earlier,
is strictly smaller than the pre-state value, and is at least `2(n+1)`.
No first-occurrence hypothesis on the pre-state is needed. -/
theorem coordinates_add_oneBorrow_negative_blocker_data
    {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r)
    (hborrow : BorrowData n q r b s)
    (hb : b = 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hnegative : potential (q + 1 - b) s < 0) :
    ∃ y fy,
      y = a n - (n + 1) ∧ 2 * (n + 1) ≤ y ∧
      FirstAt a y fy ∧ EarlierSmaller ⟨y, fy⟩ ⟨a n, n⟩ := by
  have hk : 4 ≤ q + 1 - b :=
    coordinates_add_oneBorrow_negative_highQuotient
      hcoord hborrow hb hnot hnegative
  subst b
  simp only [Nat.add_sub_cancel] at hk hnegative
  rcases Nat.exists_eq_add_of_le' hk with ⟨p, hp⟩
  subst q
  let y := a n - (n + 1)
  have hn : 0 < n := by
    have hrlt := hcoord.remainder_lt
    omega
  have heq := hcoord.eqn
  have hbal := hborrow.balance
  simp only [Nat.one_mul] at hbal
  have hpositive : n + 1 < a n := by
    simp [Nat.mul_add] at heq
    omega
  have hyLower : 2 * (n + 1) ≤ y := by
    simp only [y]
    simp [Nat.mul_add] at heq
    omega
  have hylt : y < a n := by
    simp only [y]
    omega
  have hseen : y ∈ valuesThrough n := by
    by_cases hySeen : y ∈ valuesThrough n
    · exact hySeen
    · have hcan : CanSubtract (n + 1) (stateAt n) := by
        constructor
        · simpa [a] using hpositive
        · change a n - (n + 1) ∉ valuesThrough n
          simpa only [y] using hySeen
      exact False.elim (hnot hcan)
  rcases history_member_has_firstAt hseen with ⟨fy, hfyLe, hfirstY⟩
  have hfy : fy < n := by
    by_cases hlt : fy < n
    · exact hlt
    · have hfyeq : fy = n := by omega
      subst fy
      rw [hfirstY.1] at hylt
      exact False.elim ((Nat.lt_irrefl y) hylt)
  exact ⟨y, fy, rfl, hyLower, hfirstY, hylt, hfy⟩

/-- Exact target condition turning the preceding blocked candidate into a
`CoverageStep`. -/
theorem coordinates_add_oneBorrow_negative_gives_coverageStep_exact
    {n q r b s m : Nat}
    (hm : m ≤ a n - (n + 1))
    (hcoord : CoordinatesAt n q r)
    (hborrow : BorrowData n q r b s)
    (hb : b = 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hnegative : potential (q + 1 - b) s < 0) :
    CoverageStep m (a n) n := by
  rcases coordinates_add_oneBorrow_negative_blocker_data
    hcoord hborrow hb hnot hnegative with
    ⟨y, fy, hy, _, hfirstY, hedge⟩
  have hmy : m ≤ y := by simpa only [hy] using hm
  exact Or.inr ⟨y, fy, hmy, hfirstY, hedge.1⟩

/-- Coarse but time-local form: every target below `2(n+1)` is discharged by
a failed high-quotient one-borrow addition. -/
theorem coordinates_add_oneBorrow_negative_gives_coverageStep_below_doubleTime
    {n q r b s m : Nat}
    (hm : m ≤ 2 * (n + 1))
    (hcoord : CoordinatesAt n q r)
    (hborrow : BorrowData n q r b s)
    (hb : b = 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hnegative : potential (q + 1 - b) s < 0) :
    CoverageStep m (a n) n := by
  rcases coordinates_add_oneBorrow_negative_blocker_data
    hcoord hborrow hb hnot hnegative with
    ⟨y, fy, _, hyLower, hfirstY, hedge⟩
  exact Or.inr ⟨y, fy, Nat.le_trans hm hyLower, hfirstY, hedge.1⟩

/-- Backward-compatible first-occurrence form under the smaller bound `m≤n`. -/
theorem coordinates_add_oneBorrow_negative_gives_coverageStep_below_time
    {n q r b s m : Nat}
    (_hfirst : FirstAt a (a n) n)
    (hcoord : CoordinatesAt n q r)
    (hborrow : BorrowData n q r b s)
    (hb : b = 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hnegative : potential (q + 1 - b) s < 0)
    (hmn : m ≤ n) :
    CoverageStep m (a n) n := by
  apply coordinates_add_oneBorrow_negative_gives_coverageStep_below_doubleTime
    (hcoord := hcoord) (hborrow := hborrow) (hb := hb)
    (hnot := hnot) (hnegative := hnegative)
  omega

/-- And a failed legal subtraction recovery must also land at quotient at
least four. -/
theorem coordinates_sub_oneBorrow_negative_highQuotient
    {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hcan : CanSubtract (n + 1) (stateAt n))
    (hnegative : potential (q - 1 - b) s < 0) :
    4 ≤ q - 1 - b := by
  by_cases hlow : q - 1 - b ≤ 3
  · have hnonnegative :=
      coordinates_sub_oneBorrow_lowQuotient_nonnegative
        hcoord hborrow hb hcan hlow
    omega
  · omega

end Recaman
