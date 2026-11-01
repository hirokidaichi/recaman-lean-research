import Recaman.ActualDescent

namespace Recaman

/-- Quotient/remainder coordinates of the actual value a_n. -/
def CoordinatesAt (n q r : Nat) : Prop := QuotRem n (a n) q r

/-- Every positive-time actual state has its canonical quotient/remainder
coordinates. -/
theorem exists_coordinatesAt {n : Nat} (hn : 0 < n) :
    ∃ q r, CoordinatesAt n q r := by
  refine ⟨a n / n, a n % n, ?_⟩
  constructor
  · exact (Nat.div_add_mod (a n) n).symm
  · exact Nat.mod_lt _ hn

theorem upperTri_pred {q : Nat} (hq : 0 < q) :
    upperTri q = upperTri (q - 1) + q := by
  cases q with
  | zero => omega
  | succ q =>
      simp [upperTri]
      omega

theorem upperTri_pred_pred {q : Nat} (hq : 2 ≤ q) :
    upperTri q = upperTri (q - 2) + (q - 1) + q := by
  cases q with
  | zero => omega
  | succ q =>
      cases q with
      | zero => omega
      | succ q =>
          simp [upperTri]
          omega

/-- In the regular chamber q≤r, subtraction lowers q and preserves G. -/
theorem potential_sub_regular {q r : Nat} (hq : 0 < q) (hregular : q ≤ r) :
    potential (q - 1) (r - q) = potential q r := by
  have htri := upperTri_pred hq
  simp [potential]
  omega

/-- In the regular chamber q≤r, addition raises q and lowers G by 2q+1. -/
theorem potential_add_regular {q r : Nat} (hregular : q ≤ r) :
    potential (q + 1) (r - q) =
      potential q r - Int.ofNat (2 * q + 1) := by
  simp [potential, upperTri]
  omega

/-- In the one-borrow chamber r<q≤n+1+r, subtraction lowers q by two and
raises G by n+q. -/
theorem potential_sub_borrow {n q r : Nat}
    (hq : 2 ≤ q) (hborrow : q ≤ n + 1 + r) :
    potential (q - 2) (n + 1 + r - q) =
      potential q r + Int.ofNat (n + q) := by
  have htri := upperTri_pred_pred hq
  simp [potential]
  omega

/-- In the one-borrow chamber, addition keeps q and changes G by n+1-q. -/
theorem potential_add_borrow {n q r : Nat}
    (hborrow : q ≤ n + 1 + r) :
    potential q (n + 1 + r - q) =
      potential q r + (Int.ofNat n + 1 - Int.ofNat q) := by
  simp [potential]
  omega

/-- Pure arithmetic transition for regular-chamber addition. -/
theorem quotRem_add_regular {n value q r : Nat}
    (hqr : QuotRem n value q r) (hregular : q ≤ r) :
    QuotRem (n + 1) (value + (n + 1)) (q + 1) (r - q) := by
  rcases hqr with ⟨heq, hrlt⟩
  constructor
  · rw [heq]
    simp [Nat.add_mul, Nat.mul_add]
    omega
  · omega

/-- Pure arithmetic transition for regular-chamber subtraction. -/
theorem quotRem_sub_regular {n value q r : Nat}
    (hqr : QuotRem n value q r) (hq : 0 < q) (hregular : q ≤ r)
    (_hpositive : n + 1 < value) :
    QuotRem (n + 1) (value - (n + 1)) (q - 1) (r - q) := by
  rcases hqr with ⟨heq, hrlt⟩
  cases q with
  | zero => omega
  | succ q =>
      constructor
      · rw [heq]
        simp [Nat.add_mul, Nat.mul_add]
        omega
      · omega

/-- Pure arithmetic transition for one-borrow addition. -/
theorem quotRem_add_borrow {n value q r : Nat}
    (hqr : QuotRem n value q r) (hlow : r < q)
    (hborrow : q ≤ n + 1 + r) :
    QuotRem (n + 1) (value + (n + 1)) q (n + 1 + r - q) := by
  rcases hqr with ⟨heq, hrlt⟩
  constructor
  · rw [heq]
    simp [Nat.add_mul]
    omega
  · omega

/-- Pure arithmetic transition for one-borrow subtraction. -/
theorem quotRem_sub_borrow {n value q r : Nat}
    (hqr : QuotRem n value q r) (hq : 2 ≤ q) (hlow : r < q)
    (hborrow : q ≤ n + 1 + r) (_hpositive : n + 1 < value) :
    QuotRem (n + 1) (value - (n + 1)) (q - 2) (n + 1 + r - q) := by
  rcases hqr with ⟨heq, hrlt⟩
  cases q with
  | zero => omega
  | succ q =>
      cases q with
      | zero => omega
      | succ q =>
          constructor
          · rw [heq]
            simp [Nat.add_mul, Nat.mul_add]
            omega
          · omega

theorem a_succ_of_not_canSubtract {n : Nat}
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    a (n + 1) = a n + (n + 1) := by
  simp [a, stateAt, step, nextValue, hnot]

/-- An addition immediately repaid by the next legal subtraction lowers the
pre-addition value by exactly one. -/
theorem a_add_then_sub_eq_pred {n : Nat}
    (hadd : ¬ CanSubtract (n + 1) (stateAt n))
    (hsub : CanSubtract (n + 2) (stateAt (n + 1))) :
    a (n + 2) + 1 = a n := by
  have haddValue := a_succ_of_not_canSubtract hadd
  have hsubValue := a_succ_of_canSubtract hsub
  have hsubValue' : a (n + 2) = a (n + 1) - (n + 2) := by
    simpa [Nat.add_assoc] using hsubValue
  have hpositive : n + 2 < a (n + 1) := by
    simpa [a] using hsub.1
  omega

/-- Conversely, a legal subtraction immediately followed by a forced
addition raises the pre-subtraction value by exactly one. -/
theorem a_sub_then_add_eq_succ {n : Nat}
    (hsub : CanSubtract (n + 1) (stateAt n))
    (hadd : ¬ CanSubtract (n + 2) (stateAt (n + 1))) :
    a (n + 2) = a n + 1 := by
  have hsubValue := a_succ_of_canSubtract hsub
  have haddValue := a_succ_of_not_canSubtract hadd
  have haddValue' : a (n + 2) = a (n + 1) + (n + 2) := by
    simpa [Nat.add_assoc] using haddValue
  have hpositive : n + 1 < a n := by
    simpa [a] using hsub.1
  omega

/-- Every positive-time Recamán value is positive: legal subtraction is
required to stay positive, while the alternative adds a positive step. -/
theorem a_pos_of_pos_time {n : Nat} (hn : 0 < n) :
    0 < a n := by
  cases n with
  | zero => omega
  | succ u =>
      by_cases hcan : CanSubtract (u + 1) (stateAt u)
      · have hvalue := a_succ_of_canSubtract hcan
        have hpositive : u + 1 < a u := by
          simpa [a] using hcan.1
        omega
      · have hvalue := a_succ_of_not_canSubtract hcan
        omega

/-- Actual regular subtraction: q decreases by one and G is invariant. -/
theorem coordinates_sub_regular {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hq : 0 < q) (hregular : q ≤ r)
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    CoordinatesAt (n + 1) (q - 1) (r - q) ∧
      potential (q - 1) (r - q) = potential q r := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hnext := a_succ_of_canSubtract hcan
  constructor
  · unfold CoordinatesAt at hcoord ⊢
    rw [hnext]
    exact quotRem_sub_regular hcoord hq hregular hpositive
  · exact potential_sub_regular hq hregular

/-- Actual regular addition: q increases by one and G decreases by 2q+1. -/
theorem coordinates_add_regular {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hregular : q ≤ r)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    CoordinatesAt (n + 1) (q + 1) (r - q) ∧
      potential (q + 1) (r - q) =
        potential q r - Int.ofNat (2 * q + 1) := by
  have hnext := a_succ_of_not_canSubtract hnot
  constructor
  · unfold CoordinatesAt at hcoord ⊢
    rw [hnext]
    exact quotRem_add_regular hcoord hregular
  · exact potential_add_regular hregular

/-- Actual one-borrow subtraction. -/
theorem coordinates_sub_borrow {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hq : 2 ≤ q) (hlow : r < q)
    (hborrow : q ≤ n + 1 + r)
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    CoordinatesAt (n + 1) (q - 2) (n + 1 + r - q) ∧
      potential (q - 2) (n + 1 + r - q) =
        potential q r + Int.ofNat (n + q) := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hnext := a_succ_of_canSubtract hcan
  constructor
  · unfold CoordinatesAt at hcoord ⊢
    rw [hnext]
    exact quotRem_sub_borrow hcoord hq hlow hborrow hpositive
  · exact potential_sub_borrow hq hborrow

/-- Actual one-borrow addition. -/
theorem coordinates_add_borrow {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hlow : r < q)
    (hborrow : q ≤ n + 1 + r)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    CoordinatesAt (n + 1) q (n + 1 + r - q) ∧
      potential q (n + 1 + r - q) =
        potential q r + (Int.ofNat n + 1 - Int.ofNat q) := by
  have hnext := a_succ_of_not_canSubtract hnot
  constructor
  · unfold CoordinatesAt at hcoord ⊢
    rw [hnext]
    exact quotRem_add_borrow hcoord hlow hborrow
  · exact potential_add_borrow hborrow

end Recaman
