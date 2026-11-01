import Recaman.LandingSurfaces

namespace Recaman

/-- The upper triangular number dominates its index. -/
theorem self_le_upperTri (k : Nat) : k ≤ upperTri k := by
  induction k with
  | zero => simp [upperTri]
  | succ k ih =>
      simp [upperTri]

/-- From index three onward, the upper triangular number dominates twice its
index. -/
theorem two_mul_le_upperTri {k : Nat} (hk : 3 ≤ k) :
    2 * k ≤ upperTri k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hkprev : 3 ≤ k
      · have hprev := ih hkprev
        simp [upperTri]
        omega
      · have hkbase : k = 2 := by omega
        subst k
        decide

/-- A genuine multi-borrow addition always has corrected remainder below the
triangular threshold of its destination quotient. -/
theorem add_multi_remainder_lt_upperTri {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : 2 ≤ b) :
    s < upperTri (q + 1 - b) := by
  let k := q + 1 - b
  have hbq : b ≤ q + 1 := hborrow.le_q_add_one
  have hquotient : q + 1 = b + k :=
    (add_borrowQuotient_eq_iff hbq).mp rfl
  have hmul := Nat.mul_le_mul_right n hb
  have hbal := hborrow.balance
  have hslt := hborrow.remainder_lt
  have hbn : b * (n + 1) = b * n + b := by
    rw [Nat.mul_add]
    simp
  rw [hbn] at hbal
  have hnk : n < k := by omega
  have htri := self_le_upperTri k
  change s < upperTri k
  omega

/-- Consequently, every genuine multi-borrow addition lands at negative
potential. -/
theorem add_multi_potential_neg {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : 2 ≤ b) :
    potential (q + 1 - b) s < 0 := by
  have hs := add_multi_remainder_lt_upperTri hborrow hb
  have hcast :
      (Int.ofNat s : Int) < Int.ofNat (upperTri (q + 1 - b)) :=
    Int.ofNat_lt.mpr hs
  change Int.ofNat s - Int.ofNat (upperTri (q + 1 - b)) < 0
  omega

/-- For subtraction, the same negativity holds from time four onward. -/
theorem sub_multi_remainder_lt_upperTri {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : 2 ≤ b)
    (hbq : b + 1 ≤ q) (hn : 4 ≤ n) :
    s < upperTri (q - 1 - b) := by
  let k := q - 1 - b
  have hquotient : q = b + k + 1 :=
    (sub_borrowQuotient_eq_iff hbq).mp rfl
  have hmul := Nat.mul_le_mul_right n hb
  have hbal := hborrow.balance
  have hslt := hborrow.remainder_lt
  have hbn : b * (n + 1) = b * n + b := by
    rw [Nat.mul_add]
    simp
  rw [hbn] at hbal
  have hnk : n ≤ k + 1 := by omega
  have hk : 3 ≤ k := by omega
  have htri := two_mul_le_upperTri hk
  change s < upperTri k
  omega

theorem sub_multi_potential_neg {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : 2 ≤ b)
    (hbq : b + 1 ≤ q) (hn : 4 ≤ n) :
    potential (q - 1 - b) s < 0 := by
  have hs := sub_multi_remainder_lt_upperTri hborrow hb hbq hn
  have hcast :
      (Int.ofNat s : Int) < Int.ofNat (upperTri (q - 1 - b)) :=
    Int.ofNat_lt.mpr hs
  change Int.ofNat s - Int.ofNat (upperTri (q - 1 - b)) < 0
  omega

/-- On the actual Recamán orbit, genuine multi-borrow coordinates cannot occur
before time four. -/
theorem actual_multi_time_ge_four {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : 2 ≤ b) :
    4 ≤ n := by
  have hfar : n + 1 + r < q := hborrow.two_le_iff.mp hb
  have heq := hcoord.eqn
  have hrlt := hcoord.remainder_lt
  by_cases hn : 4 ≤ n
  · exact hn
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with hzero | hone | htwo | hthree
    · subst n
      omega
    · subst n
      have ha : a 1 = 1 := by decide
      rw [ha] at heq
      simp at heq
      omega
    · subst n
      have ha : a 2 = 3 := by decide
      rw [ha] at heq
      omega
    · subst n
      have ha : a 3 = 6 := by decide
      rw [ha] at heq
      omega

/-- Therefore an actual legal multi-borrow subtraction also lands at negative
potential. -/
theorem coordinates_sub_multi_potential_neg {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : 2 ≤ b) (hcan : CanSubtract (n + 1) (stateAt n)) :
    potential (q - 1 - b) s < 0 := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  exact sub_multi_potential_neg hborrow hb hbq
    (actual_multi_time_ge_four hcoord hborrow hb)

/-- A multi-borrow addition cannot directly hit any nonnegative target level. -/
theorem add_multi_ne_targetSurface {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s) (hb : 2 ≤ b) :
    potential (q + 1 - b) s ≠ Int.ofNat m := by
  have hneg := add_multi_potential_neg hborrow hb
  intro heq
  have hmneg : Int.ofNat m < 0 := by
    rw [← heq]
    exact hneg
  have hnonneg : (0 : Int) ≤ Int.ofNat m := by
    rw [Int.ofNat_eq_natCast]
    exact Int.natCast_nonneg m
  omega

/-- Nor can an actual multi-borrow subtraction directly hit a nonnegative
target level. -/
theorem coordinates_sub_multi_ne_targetSurface {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : 2 ≤ b) (hcan : CanSubtract (n + 1) (stateAt n)) :
    potential (q - 1 - b) s ≠ Int.ofNat m := by
  have hneg := coordinates_sub_multi_potential_neg hcoord hborrow hb hcan
  intro heq
  have hmneg : Int.ofNat m < 0 := by
    rw [← heq]
    exact hneg
  have hnonneg : (0 : Int) ≤ Int.ofNat m := by
    rw [Int.ofNat_eq_natCast]
    exact Int.natCast_nonneg m
  omega

end Recaman
