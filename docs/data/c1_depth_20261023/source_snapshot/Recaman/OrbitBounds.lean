import Recaman.MultiBorrow

namespace Recaman

/-- The Recamán value never exceeds the sum of all step sizes seen so far. -/
theorem a_le_upperTri (n : Nat) : a n ≤ upperTri n := by
  induction n with
  | zero => simp [a, stateAt, initial, upperTri]
  | succ n ih =>
      rw [recurrence]
      split
      · simp [upperTri]
        omega
      · simp [upperTri]
        omega

/-- Division-free closed form for the upper triangular number. -/
theorem two_mul_upperTri (n : Nat) :
    2 * upperTri n = n * (n + 1) := by
  induction n with
  | zero => simp [upperTri]
  | succ n ih =>
      rw [upperTri]
      calc
        2 * (upperTri n + n + 1) =
            2 * upperTri n + 2 * n + 2 := by omega
        _ = n * (n + 1) + 2 * n + 2 := by rw [ih]
        _ = (n + 1) * (n + 1 + 1) := by
          simp [Nat.add_mul, Nat.mul_add]
          omega

/-- The quotient of an actual coordinate point satisfies the sharp bound
`2q ≤ n+1`. -/
theorem CoordinatesAt.twice_quotient_le {n q r : Nat}
    (hcoord : CoordinatesAt n q r) :
    2 * q ≤ n + 1 := by
  have hn : 0 < n := by
    have hrlt := hcoord.remainder_lt
    omega
  have hvalue := a_le_upperTri n
  have heq := hcoord.eqn
  have hnq : n * q ≤ upperTri n := by omega
  have htwice := Nat.mul_le_mul_left 2 hnq
  rw [two_mul_upperTri] at htwice
  have hnormalized : n * (2 * q) ≤ n * (n + 1) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htwice
  exact (Nat.mul_le_mul_left_iff hn).mp hnormalized

/-- In particular, the actual quotient never exceeds the current time. -/
theorem CoordinatesAt.quotient_le_time {n q r : Nat}
    (hcoord : CoordinatesAt n q r) : q ≤ n := by
  have hbound := hcoord.twice_quotient_le
  omega

/-- Genuine multi-borrow data cannot occur at an actual Recamán coordinate
point.  Thus every actual borrow count is zero or one. -/
theorem BorrowData.le_one_of_coordinatesAt {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s) :
    b ≤ 1 := by
  have hq := hcoord.quotient_le_time
  by_cases hle : b ≤ 1
  · exact hle
  · have hmulti : 2 ≤ b := by omega
    have hfar : n + 1 + r < q := hborrow.two_le_iff.mp hmulti
    omega

/-- Exact actual-orbit dichotomy for the borrow count. -/
theorem BorrowData.eq_zero_or_one_of_coordinatesAt {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s) :
    b = 0 ∨ b = 1 := by
  have hle := hborrow.le_one_of_coordinatesAt hcoord
  omega

/-- The formerly possible far chamber is empty on the actual orbit. -/
theorem not_far_chamber_of_coordinatesAt {n q r : Nat}
    (hcoord : CoordinatesAt n q r) :
    ¬ n + 1 + r < q := by
  have hq := hcoord.quotient_le_time
  omega

end Recaman
