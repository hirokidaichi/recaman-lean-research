import Recaman.NegativeRegion
import Recaman.OrbitBounds

namespace Recaman

/-- Exact potential update for a zero-borrow addition. -/
theorem add_zeroBorrow_potential_eq {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 0) :
    potential (q + 1 - b) s =
      potential q r - Int.ofNat (2 * q + 1) := by
  have hregular : q ≤ r := by
    have hbal := hborrow.balance
    subst b
    simp at hbal
    omega
  have hs := hborrow.remainder_eq_of_eq_zero hb
  subst b
  subst s
  simpa using potential_add_regular hregular

/-- Exact potential update for a zero-borrow subtraction. -/
theorem sub_zeroBorrow_potential_eq {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 0)
    (hbq : b + 1 ≤ q) :
    potential (q - 1 - b) s = potential q r := by
  have hregular : q ≤ r := by
    have hbal := hborrow.balance
    subst b
    simp at hbal
    omega
  have hs := hborrow.remainder_eq_of_eq_zero hb
  subst b
  have hq : 0 < q := by omega
  subst s
  simpa using potential_sub_regular hq hregular

/-- A zero-borrow addition cannot escape the negative-potential half-space. -/
theorem add_zeroBorrow_preserves_negative {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 0)
    (hnegative : potential q r < 0) :
    potential (q + 1 - b) s < 0 := by
  have hstep := add_zeroBorrow_potential_eq hborrow hb
  have hdrop : (0 : Int) ≤ Int.ofNat (2 * q + 1) := by
    rw [Int.ofNat_eq_natCast]
    exact Int.natCast_nonneg _
  rw [hstep]
  omega

/-- A zero-borrow subtraction preserves `G`, hence also preserves negativity. -/
theorem sub_zeroBorrow_preserves_negative {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 0)
    (hbq : b + 1 ≤ q) (hnegative : potential q r < 0) :
    potential (q - 1 - b) s < 0 := by
  rw [sub_zeroBorrow_potential_eq hborrow hb hbq]
  exact hnegative

/-- In the negative half-space, a zero-borrow chamber has quotient at least
two.  The cases `q=0,1` are incompatible with both `q≤r` and `r<U(q)`. -/
theorem two_le_quotient_of_negative_zeroBorrow {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 0)
    (hnegative : potential q r < 0) :
    2 ≤ q := by
  have hregular : q ≤ r := by
    have hbal := hborrow.balance
    subst b
    simp at hbal
    omega
  by_cases hq : 2 ≤ q
  · exact hq
  · have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with hzero | hone
    · subst q
      simp [potential, upperTri] at hnegative
      omega
    · subst q
      simp [potential, upperTri] at hnegative
      omega

/-- Consequently the corrected remainder drops by at least two at every
negative zero-borrow step. -/
theorem zeroBorrow_remainder_drop {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 0)
    (hnegative : potential q r < 0) :
    s + 2 ≤ r := by
  have hq := two_le_quotient_of_negative_zeroBorrow hborrow hb hnegative
  have hs := hborrow.remainder_eq_of_eq_zero hb
  have hregular : q ≤ r := by
    have hbal := hborrow.balance
    subst b
    simp at hbal
    omega
  omega

/-- Starting at any actual negative-potential coordinate point, a one-borrow
event must occur within at most `⌊r/2⌋` further steps.  This is an
unconditional finite-time result: every intervening zero-borrow step lowers
the natural-valued remainder by at least two. -/
theorem eventually_oneBorrow_of_negative_halfRemainder {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hnegative : potential q r < 0) :
    ∃ t q' r' s,
      n ≤ t ∧ t ≤ n + r / 2 ∧
      CoordinatesAt t q' r' ∧ BorrowData t q' r' 1 s := by
  induction r using Nat.strongRecOn generalizing n q with
  | ind r ih =>
      rcases exists_borrowData hcoord.remainder_lt with ⟨b, s, hborrow⟩
      rcases hborrow.eq_zero_or_one_of_coordinatesAt hcoord with hb | hb
      · have hsdrop := zeroBorrow_remainder_drop hborrow hb hnegative
        have hslt : s < r := by omega
        by_cases hcan : CanSubtract (n + 1) (stateAt n)
        · have hpositive : n + 1 < a n := by simpa [a] using hcan.1
          have hbq : b + 1 ≤ q :=
            hborrow.add_one_le_q_of_positive hcoord hpositive
          have hnext := coordinates_sub_borrowData hcoord hborrow hbq hcan
          have hnextNegative :=
            sub_zeroBorrow_preserves_negative hborrow hb hbq hnegative
          rcases ih s hslt hnext.1 hnextNegative with
            ⟨t, q', r', u, hnt, htbound, htcoord, htborrow⟩
          refine ⟨t, q', r', u, ?_, ?_, htcoord, htborrow⟩
          · omega
          · omega
        · have hbq : b ≤ q + 1 := hborrow.le_q_add_one
          have hnext := coordinates_add_borrowData hcoord hborrow hbq hcan
          have hnextNegative :=
            add_zeroBorrow_preserves_negative hborrow hb hnegative
          rcases ih s hslt hnext.1 hnextNegative with
            ⟨t, q', r', u, hnt, htbound, htcoord, htborrow⟩
          refine ⟨t, q', r', u, ?_, ?_, htcoord, htborrow⟩
          · omega
          · omega
      · subst b
        exact ⟨n, q, r, s, by omega, by omega, hcoord, hborrow⟩

/-- Convenient weaker form of the sharp half-remainder bound. -/
theorem eventually_oneBorrow_of_negative {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hnegative : potential q r < 0) :
    ∃ t q' r' s,
      n ≤ t ∧ t ≤ n + r ∧
      CoordinatesAt t q' r' ∧ BorrowData t q' r' 1 s := by
  rcases eventually_oneBorrow_of_negative_halfRemainder hcoord hnegative with
    ⟨t, q', r', s, hnt, htbound, htcoord, htborrow⟩
  exact ⟨t, q', r', s, hnt, by omega, htcoord, htborrow⟩

/-- If addition crosses from `G<0` into `G≥0`, its unique borrow count must be
exactly one.  Zero borrow moves downward, while two or more borrows land
strictly negative. -/
theorem add_crosses_nonnegative_only_oneBorrow {n q r b s : Nat}
    (hborrow : BorrowData n q r b s)
    (hnegative : potential q r < 0)
    (hnext : 0 ≤ potential (q + 1 - b) s) :
    b = 1 := by
  cases b with
  | zero =>
      have hstill := add_zeroBorrow_preserves_negative hborrow rfl hnegative
      omega
  | succ b =>
      cases b with
      | zero => rfl
      | succ b =>
          have hmulti : 2 ≤ Nat.succ (Nat.succ b) := by omega
          have hstill := add_multi_potential_neg hborrow hmulti
          omega

/-- The subtraction analogue on the actual orbit. -/
theorem sub_crosses_nonnegative_only_oneBorrow {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hnegative : potential q r < 0)
    (hnext : 0 ≤ potential (q - 1 - b) s) :
    b = 1 := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  cases b with
  | zero =>
      have hstill :=
        sub_zeroBorrow_preserves_negative hborrow rfl hbq hnegative
      omega
  | succ b =>
      cases b with
      | zero => rfl
      | succ b =>
          have hmulti : 2 ≤ Nat.succ (Nat.succ b) := by omega
          have hstill :=
            coordinates_sub_multi_potential_neg hcoord hborrow hmulti hcan
          omega

/-- Therefore every addition-side crossing of zero occurs in exactly the old
one-borrow chamber. -/
theorem add_crossing_oneBorrow_chamber {n q r b s : Nat}
    (hborrow : BorrowData n q r b s)
    (hnegative : potential q r < 0)
    (hnext : 0 ≤ potential (q + 1 - b) s) :
    b = 1 ∧ r < q ∧ q ≤ n + 1 + r := by
  have hb := add_crosses_nonnegative_only_oneBorrow
    hborrow hnegative hnext
  exact ⟨hb, hborrow.eq_one_iff.mp hb⟩

/-- And the same is true for actual subtraction-side crossings. -/
theorem sub_crossing_oneBorrow_chamber {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hnegative : potential q r < 0)
    (hnext : 0 ≤ potential (q - 1 - b) s) :
    b = 1 ∧ r < q ∧ q ≤ n + 1 + r := by
  have hb := sub_crosses_nonnegative_only_oneBorrow
    hcoord hborrow hcan hnegative hnext
  exact ⟨hb, hborrow.eq_one_iff.mp hb⟩

/-- In particular, a direct addition from negative potential to any target
surface `G=m` must use exactly one borrow. -/
theorem add_negative_to_target_only_oneBorrow {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s)
    (hnegative : potential q r < 0)
    (htarget : potential (q + 1 - b) s = Int.ofNat m) :
    b = 1 := by
  have hnext : 0 ≤ potential (q + 1 - b) s := by
    rw [htarget]
    change (0 : Int) ≤ (m : Int)
    exact Int.natCast_nonneg m
  exact add_crosses_nonnegative_only_oneBorrow hborrow hnegative hnext

/-- The corresponding direct subtraction-to-target statement. -/
theorem sub_negative_to_target_only_oneBorrow {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hnegative : potential q r < 0)
    (htarget : potential (q - 1 - b) s = Int.ofNat m) :
    b = 1 := by
  have hnext : 0 ≤ potential (q - 1 - b) s := by
    rw [htarget]
    change (0 : Int) ≤ (m : Int)
    exact Int.natCast_nonneg m
  exact sub_crosses_nonnegative_only_oneBorrow
    hcoord hborrow hcan hnegative hnext

end Recaman
