import Recaman.CoordinateDynamics

namespace Recaman

/-- A borrow certificate for changing the modulus from `n` to `n+1`.

The equation says that after borrowing `b` copies of `n+1`, the corrected
remainder is `s`; the strict bound makes `s` the genuine new remainder. -/
structure BorrowData (n q r b s : Nat) : Prop where
  balance : b * (n + 1) + r = q + s
  remainder_lt : s < n + 1

/-- Canonical borrow data in the regular chamber. -/
theorem BorrowData.zero_of_le {n q r : Nat} (hr : r < n) (hregular : q ≤ r) :
    BorrowData n q r 0 (r - q) := by
  constructor
  · simp
    omega
  · omega

/-- Canonical borrow data in the one-borrow chamber. -/
theorem BorrowData.one_of_chamber {n q r : Nat}
    (hlow : r < q) (hupper : q ≤ n + 1 + r) :
    BorrowData n q r 1 (n + 1 + r - q) := by
  constructor
  · simp
    omega
  · omega

/-- The corrected remainder of zero borrow is the regular remainder `r-q`. -/
theorem BorrowData.remainder_eq_of_eq_zero {n q r b s : Nat}
    (h : BorrowData n q r b s) (hb : b = 0) :
    s = r - q := by
  subst b
  have hbal := h.balance
  simp at hbal
  omega

/-- The corrected remainder of one borrow is `n+1+r-q`. -/
theorem BorrowData.remainder_eq_of_eq_one {n q r b s : Nat}
    (h : BorrowData n q r b s) (hb : b = 1) :
    s = n + 1 + r - q := by
  subst b
  have hbal := h.balance
  simp at hbal
  omega

/-- Every old remainder `r<n` admits borrow data.  This is the ceiling-division
decomposition of `q-r` by `n+1`, but stated without exposing division in the
resulting transition rules. -/
theorem exists_borrowData {n q r : Nat} (hr : r < n) :
    ∃ b s, BorrowData n q r b s := by
  by_cases hregular : q ≤ r
  · exact ⟨0, r - q, BorrowData.zero_of_le hr hregular⟩
  · have hlower : r < q := by omega
    have hdiv := Nat.div_add_mod (q - r) (n + 1)
    have hmod : (q - r) % (n + 1) < n + 1 :=
      Nat.mod_lt _ (by omega)
    by_cases hzero : (q - r) % (n + 1) = 0
    · refine ⟨(q - r) / (n + 1), 0, ?_⟩
      constructor
      · rw [hzero] at hdiv
        simp [Nat.mul_comm]
        omega
      · omega
    · refine ⟨(q - r) / (n + 1) + 1,
          n + 1 - (q - r) % (n + 1), ?_⟩
      constructor
      · simp only [Nat.add_mul]
        rw [Nat.mul_comm ((q - r) / (n + 1)) (n + 1)]
        omega
      · omega

/-- The borrow count is unique; in fact the remainder is unique as well. -/
theorem BorrowData.unique {n q r b s c t : Nat}
    (h₁ : BorrowData n q r b s) (h₂ : BorrowData n q r c t) :
    b = c ∧ s = t := by
  rcases h₁ with ⟨hbal₁, hslt⟩
  rcases h₂ with ⟨hbal₂, htlt⟩
  have hbc : b = c := by
    by_cases heq : b = c
    · exact heq
    · have hcases : b < c ∨ c < b := by omega
      rcases hcases with hlt | hgt
      · have hstep : b + 1 ≤ c := by omega
        have hmul := Nat.mul_le_mul_right (n + 1) hstep
        simp only [Nat.add_mul] at hmul
        omega
      · have hstep : c + 1 ≤ b := by omega
        have hmul := Nat.mul_le_mul_right (n + 1) hstep
        simp only [Nat.add_mul] at hmul
        omega
  constructor
  · exact hbc
  · subst c
    omega

/-- Zero borrow is exactly the regular chamber `q≤r`. -/
theorem BorrowData.eq_zero_iff {n q r b s : Nat}
    (hr : r < n) (h : BorrowData n q r b s) :
    b = 0 ↔ q ≤ r := by
  constructor
  · intro hb
    subst b
    have hbal := h.balance
    simp at hbal
    omega
  · intro hregular
    have hzero := BorrowData.zero_of_le hr hregular
    exact (h.unique hzero).1

/-- One borrow is exactly the old one-borrow chamber. -/
theorem BorrowData.eq_one_iff {n q r b s : Nat}
    (h : BorrowData n q r b s) :
    b = 1 ↔ r < q ∧ q ≤ n + 1 + r := by
  constructor
  · intro hb
    subst b
    have hbal := h.balance
    have hslt := h.remainder_lt
    simp at hbal
    constructor <;> omega
  · rintro ⟨hlow, hupper⟩
    have hone := BorrowData.one_of_chamber hlow hupper
    exact (h.unique hone).1

/-- Two or more borrows occur exactly in the previously untreated chamber
`q>n+1+r`. -/
theorem BorrowData.two_le_iff {n q r b s : Nat}
    (h : BorrowData n q r b s) :
    2 ≤ b ↔ n + 1 + r < q := by
  have hbal := h.balance
  have hslt := h.remainder_lt
  constructor
  · intro hb
    have hmul := Nat.mul_le_mul_right (n + 1) hb
    omega
  · intro hfar
    cases b with
    | zero =>
        simp at hbal
        omega
    | succ b =>
        cases b with
        | zero =>
            simp at hbal
            omega
        | succ b => omega

/-- Any valid borrow count for addition fits in the available quotient. -/
theorem BorrowData.le_q_add_one {n q r b s : Nat}
    (h : BorrowData n q r b s) :
    b ≤ q + 1 := by
  by_cases hbound : b ≤ q + 1
  · exact hbound
  · have hlarge : q + 2 ≤ b := by omega
    have hmul := Nat.mul_le_mul_right (n + 1) hlarge
    have hqmul : q ≤ q * (n + 1) := by
      have hone : 1 ≤ n + 1 := by omega
      have := Nat.mul_le_mul_left q hone
      simpa using this
    have hbal := h.balance
    have hslt := h.remainder_lt
    simp only [Nat.add_mul] at hmul
    omega

/-- If subtraction is numerically legal, the borrow count also fits in the
decremented quotient. -/
theorem BorrowData.add_one_le_q_of_positive {n value q r b s : Nat}
    (hqr : QuotRem n value q r) (h : BorrowData n q r b s)
    (hpositive : n + 1 < value) :
    b + 1 ≤ q := by
  rcases hqr with ⟨heq, hrlt⟩
  by_cases hbound : b + 1 ≤ q
  · exact hbound
  · have hqb : q ≤ b := by omega
    have hmul := Nat.mul_le_mul_right (n + 1) hqb
    have hNq : (n + 1) * q = n * q + q := by
      rw [Nat.add_mul]
      simp
    have hcommQ : q * (n + 1) = (n + 1) * q := Nat.mul_comm _ _
    have hcommB : b * (n + 1) = (n + 1) * b := Nat.mul_comm _ _
    have hbal := h.balance
    have hslt := h.remainder_lt
    omega

/-- General arithmetic transition for addition with any borrow count. -/
theorem quotRem_add_borrowData {n value q r b s : Nat}
    (hqr : QuotRem n value q r) (hborrow : BorrowData n q r b s)
    (hbq : b ≤ q + 1) :
    QuotRem (n + 1) (value + (n + 1)) (q + 1 - b) s := by
  rcases hqr with ⟨heq, hrlt⟩
  have hbal := hborrow.balance
  constructor
  · have hsplit : q + 1 = (q + 1 - b) + b := by omega
    have hmul :
        (n + 1) * (q + 1) =
          (n + 1) * (q + 1 - b) + (n + 1) * b := by
      calc
        (n + 1) * (q + 1) =
            (n + 1) * ((q + 1 - b) + b) :=
          congrArg (fun x => (n + 1) * x) hsplit
        _ = (n + 1) * (q + 1 - b) + (n + 1) * b := by
          rw [Nat.mul_add]
    have hNq : (n + 1) * q = n * q + q := by
      rw [Nat.add_mul]
      simp
    have hNsucc : (n + 1) * (q + 1) = (n + 1) * q + (n + 1) := by
      rw [Nat.mul_add]
      simp
    have hcomm : b * (n + 1) = (n + 1) * b := Nat.mul_comm _ _
    rw [heq]
    omega
  · exact hborrow.remainder_lt

/-- General arithmetic transition for subtraction with any borrow count. -/
theorem quotRem_sub_borrowData {n value q r b s : Nat}
    (hqr : QuotRem n value q r) (hborrow : BorrowData n q r b s)
    (hbq : b + 1 ≤ q) (hpositive : n + 1 < value) :
    QuotRem (n + 1) (value - (n + 1)) (q - 1 - b) s := by
  rcases hqr with ⟨heq, hrlt⟩
  have hbal := hborrow.balance
  constructor
  · have hsplit : q = (q - 1 - b) + b + 1 := by omega
    have hmul :
        (n + 1) * q =
          (n + 1) * (q - 1 - b) + (n + 1) * b + (n + 1) := by
      calc
        (n + 1) * q =
            (n + 1) * ((q - 1 - b) + b + 1) :=
          congrArg (fun x => (n + 1) * x) hsplit
        _ = (n + 1) * (q - 1 - b) + (n + 1) * b + (n + 1) := by
          simp [Nat.mul_add]
    have hNq : (n + 1) * q = n * q + q := by
      rw [Nat.add_mul]
      simp
    have hcomm : b * (n + 1) = (n + 1) * b := Nat.mul_comm _ _
    rw [heq]
    omega
  · exact hborrow.remainder_lt

/-- Exact signed potential drift for an arbitrary borrow correction. -/
theorem potential_borrowData {n q r b s q' : Nat}
    (hborrow : BorrowData n q r b s) :
    potential q' s =
      potential q r + Int.ofNat (b * (n + 1)) - Int.ofNat q +
        Int.ofNat (upperTri q) - Int.ofNat (upperTri q') := by
  have hbal := hborrow.balance
  have hcast :
      Int.ofNat (b * (n + 1)) + Int.ofNat r =
        Int.ofNat q + Int.ofNat s :=
    congrArg Int.ofNat hbal
  simp only [potential]
  calc
    Int.ofNat s - Int.ofNat (upperTri q') =
        (Int.ofNat q + Int.ofNat s) - Int.ofNat q -
          Int.ofNat (upperTri q') := by omega
    _ = (Int.ofNat (b * (n + 1)) + Int.ofNat r) - Int.ofNat q -
          Int.ofNat (upperTri q') := by rw [hcast]
    _ = (Int.ofNat r - Int.ofNat (upperTri q)) +
          Int.ofNat (b * (n + 1)) - Int.ofNat q +
            Int.ofNat (upperTri q) - Int.ofNat (upperTri q') := by omega

/-- Moving the quotient down by two at fixed remainder raises the potential by
the odd number `2p+3`. -/
theorem potential_two_quotient_gap (p s : Nat) :
    potential p s =
      potential (p + 2) s + Int.ofNat (2 * p + 3) := by
  simp [potential, upperTri]
  omega

/-- With the same borrow data, subtraction and addition land two quotient
levels apart, hence their destination potentials differ by one exact odd gap.
This simultaneously generalizes the regular gap `2q+1` and the one-borrow gap
`2q-1`. -/
theorem potential_borrow_branch_gap {q b s : Nat} (hbq : b + 1 ≤ q) :
    potential (q - 1 - b) s =
      potential (q + 1 - b) s +
        Int.ofNat (2 * (q - 1 - b) + 3) := by
  have hquot : q + 1 - b = (q - 1 - b) + 2 := by omega
  rw [hquot]
  exact potential_two_quotient_gap (q - 1 - b) s

/-- Actual addition transition with an arbitrary borrow count. -/
theorem coordinates_add_borrowData {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hbq : b ≤ q + 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    CoordinatesAt (n + 1) (q + 1 - b) s ∧
      potential (q + 1 - b) s =
        potential q r + Int.ofNat (b * (n + 1)) - Int.ofNat q +
          Int.ofNat (upperTri q) -
            Int.ofNat (upperTri (q + 1 - b)) := by
  have hnext := a_succ_of_not_canSubtract hnot
  constructor
  · unfold CoordinatesAt at hcoord ⊢
    rw [hnext]
    exact quotRem_add_borrowData hcoord hborrow hbq
  · exact potential_borrowData hborrow

/-- Actual subtraction transition with an arbitrary borrow count. -/
theorem coordinates_sub_borrowData {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hbq : b + 1 ≤ q)
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    CoordinatesAt (n + 1) (q - 1 - b) s ∧
      potential (q - 1 - b) s =
        potential q r + Int.ofNat (b * (n + 1)) - Int.ofNat q +
          Int.ofNat (upperTri q) -
            Int.ofNat (upperTri (q - 1 - b)) := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hnext := a_succ_of_canSubtract hcan
  constructor
  · unfold CoordinatesAt at hcoord ⊢
    rw [hnext]
    exact quotRem_sub_borrowData hcoord hborrow hbq hpositive
  · exact potential_borrowData hborrow

/-- Addition is total in the quotient/remainder coordinates: the unique borrow
data exists and satisfies the quotient-side bound required by the transition. -/
theorem coordinates_add_total {n q r : Nat}
    (hcoord : CoordinatesAt n q r)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    ∃ b s, BorrowData n q r b s ∧
      CoordinatesAt (n + 1) (q + 1 - b) s ∧
      potential (q + 1 - b) s =
        potential q r + Int.ofNat (b * (n + 1)) - Int.ofNat q +
          Int.ofNat (upperTri q) -
            Int.ofNat (upperTri (q + 1 - b)) := by
  have hr : r < n := hcoord.remainder_lt
  rcases exists_borrowData hr with ⟨b, s, hborrow⟩
  have hbq : b ≤ q + 1 := hborrow.le_q_add_one
  rcases coordinates_add_borrowData hcoord hborrow hbq hnot with
    ⟨hnext, hpotential⟩
  exact ⟨b, s, hborrow, hnext, hpotential⟩

/-- Legal subtraction is likewise total in the quotient/remainder coordinates. -/
theorem coordinates_sub_total {n q r : Nat}
    (hcoord : CoordinatesAt n q r)
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    ∃ b s, BorrowData n q r b s ∧
      CoordinatesAt (n + 1) (q - 1 - b) s ∧
      potential (q - 1 - b) s =
        potential q r + Int.ofNat (b * (n + 1)) - Int.ofNat q +
          Int.ofNat (upperTri q) -
            Int.ofNat (upperTri (q - 1 - b)) := by
  have hr : r < n := hcoord.remainder_lt
  rcases exists_borrowData hr with ⟨b, s, hborrow⟩
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  rcases coordinates_sub_borrowData hcoord hborrow hbq hcan with
    ⟨hnext, hpotential⟩
  exact ⟨b, s, hborrow, hnext, hpotential⟩

/-- In the far chamber, an actual addition necessarily uses at least two
borrows; this closes the former multi-borrow gap for the addition branch. -/
theorem coordinates_add_multi {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hfar : n + 1 + r < q)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    ∃ b s, 2 ≤ b ∧ BorrowData n q r b s ∧
      CoordinatesAt (n + 1) (q + 1 - b) s ∧
      potential (q + 1 - b) s =
        potential q r + Int.ofNat (b * (n + 1)) - Int.ofNat q +
          Int.ofNat (upperTri q) -
            Int.ofNat (upperTri (q + 1 - b)) := by
  rcases coordinates_add_total hcoord hnot with
    ⟨b, s, hborrow, hnext, hpotential⟩
  exact ⟨b, s, hborrow.two_le_iff.mpr hfar, hborrow, hnext, hpotential⟩

/-- In the far chamber, an actual legal subtraction necessarily uses at least
two borrows; this closes the former multi-borrow gap for the subtraction branch. -/
theorem coordinates_sub_multi {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hfar : n + 1 + r < q)
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    ∃ b s, 2 ≤ b ∧ BorrowData n q r b s ∧
      CoordinatesAt (n + 1) (q - 1 - b) s ∧
      potential (q - 1 - b) s =
        potential q r + Int.ofNat (b * (n + 1)) - Int.ofNat q +
          Int.ofNat (upperTri q) -
            Int.ofNat (upperTri (q - 1 - b)) := by
  rcases coordinates_sub_total hcoord hcan with
    ⟨b, s, hborrow, hnext, hpotential⟩
  exact ⟨b, s, hborrow.two_le_iff.mpr hfar, hborrow, hnext, hpotential⟩

end Recaman
