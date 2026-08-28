import Recaman.Recovery

namespace Recaman

/-- Potential gain of a one-borrow addition. -/
def addOneBorrowBudget (n q : Nat) : Int :=
  Int.ofNat n + 1 - Int.ofNat q

/-- Potential gain of a one-borrow subtraction. -/
def subOneBorrowBudget (n q : Nat) : Int :=
  Int.ofNat (n + q)

/-- Defect from the one-borrow chamber wall. -/
def oneBorrowDefect (q r : Nat) : Nat := q - r

/-- Branch-independent normal form for one borrow.  The defect is positive,
splits the old quotient as `r+δ=q`, and complements the new remainder to the
new modulus as `s+δ=n+1`. -/
theorem BorrowData.one_defect_spec {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    0 < oneBorrowDefect q r ∧
      oneBorrowDefect q r ≤ q ∧
      r + oneBorrowDefect q r = q ∧
      s + oneBorrowDefect q r = n + 1 := by
  have hchamber := hborrow.eq_one_iff.mp hb
  have hbal := hborrow.balance
  subst b
  unfold oneBorrowDefect
  simp at hbal
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- The negative depth immediately before one borrow is exactly the lower
triangular number plus the chamber defect. -/
theorem oneBorrow_prePotential {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    potential q r =
      -Int.ofNat (lowerTri q + oneBorrowDefect q r) := by
  have hspec := hborrow.one_defect_spec hb
  have htri := upperTri_eq_lowerTri_add q
  have hcastOld :
      Int.ofNat r + Int.ofNat (oneBorrowDefect q r) = Int.ofNat q :=
    congrArg Int.ofNat hspec.2.2.1
  have hcastTri :
      Int.ofNat (upperTri q) =
        Int.ofNat (lowerTri q) + Int.ofNat q := by
    rw [htri]
    rfl
  have hcastDepth :
      Int.ofNat (lowerTri q + oneBorrowDefect q r) =
        Int.ofNat (lowerTri q) + Int.ofNat (oneBorrowDefect q r) := rfl
  unfold potential
  rw [hcastTri, hcastDepth]
  omega

/-- Unified nonnegative-landing criterion for one borrow, independent of the
actual addition/subtraction branch. -/
theorem oneBorrow_destination_nonnegative_iff {n q r b s k : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    0 ≤ potential k s ↔
      upperTri k + oneBorrowDefect q r ≤ n + 1 := by
  have hspec := hborrow.one_defect_spec hb
  rw [potential_nonnegative_iff]
  omega

/-- Unified target clock for one borrow. -/
theorem oneBorrow_destination_target_iff {n q r b s k m : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    potential k s = Int.ofNat m ↔
      n + 1 = upperTri k + m + oneBorrowDefect q r := by
  have hspec := hborrow.one_defect_spec hb
  rw [potential_eq_ofNat_iff]
  omega

/-- Exact one-borrow addition budget, expressed through general borrow data. -/
theorem add_oneBorrow_potential_eq {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    potential (q + 1 - b) s =
      potential q r + addOneBorrowBudget n q := by
  have hchamber := hborrow.eq_one_iff.mp hb
  have hs := hborrow.remainder_eq_of_eq_one hb
  subst b
  subst s
  simpa [addOneBorrowBudget] using potential_add_borrow hchamber.2

/-- Exact one-borrow subtraction budget. -/
theorem sub_oneBorrow_potential_eq {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) (hq : 2 ≤ q) :
    potential (q - 1 - b) s =
      potential q r + subOneBorrowBudget n q := by
  have hchamber := hborrow.eq_one_iff.mp hb
  have hs := hborrow.remainder_eq_of_eq_one hb
  subst b
  subst s
  have hquotient : q - 1 - 1 = q - 2 := by omega
  rw [hquotient]
  simpa [subOneBorrowBudget] using potential_sub_borrow hq hchamber.2

/-- The sharp actual-orbit quotient bound makes the addition budget at least
the old quotient. -/
theorem CoordinatesAt.quotient_le_addOneBorrowBudget {n q r : Nat}
    (hcoord : CoordinatesAt n q r) :
    Int.ofNat q ≤ addOneBorrowBudget n q := by
  have hbound := hcoord.twice_quotient_le
  have hqle : q ≤ n + 1 := by omega
  have hnat : q ≤ n + 1 - q := by omega
  calc
    Int.ofNat q ≤ Int.ofNat (n + 1 - q) := Int.ofNat_le.mpr hnat
    _ = Int.ofNat (n + 1) - Int.ofNat q := Int.ofNat_sub hqle
    _ = addOneBorrowBudget n q := by rfl

/-- Hence every actual one-borrow addition strictly increases the potential. -/
theorem coordinates_add_oneBorrow_potential_lt {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) :
    potential q r < potential (q + 1 - b) s := by
  have hbudget := hcoord.quotient_le_addOneBorrowBudget
  have hqpos : 0 < q := by
    have hchamber := hborrow.eq_one_iff.mp hb
    omega
  have hqInt : (0 : Int) < Int.ofNat q := Int.ofNat_lt.mpr hqpos
  rw [add_oneBorrow_potential_eq hborrow hb]
  omega

/-- Every legal actual one-borrow subtraction also strictly increases `G`. -/
theorem coordinates_sub_oneBorrow_potential_lt {n q r b s : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hcan : CanSubtract (n + 1) (stateAt n)) :
    potential q r < potential (q - 1 - b) s := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  have hq : 2 ≤ q := by omega
  rw [sub_oneBorrow_potential_eq hborrow hb hq]
  have hn : 0 < n := by
    have hrlt := hcoord.remainder_lt
    omega
  unfold subOneBorrowBudget
  have hnatPositive : 0 < n + q := by omega
  have hbudgetPositive : (0 : Int) < Int.ofNat (n + q) := by
    exact Int.ofNat_lt.mpr hnatPositive
  omega

/-- Exact Nat threshold for a one-borrow addition to reach `G≥0`. -/
theorem add_oneBorrow_nonnegative_iff {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    0 ≤ potential (q + 1 - b) s ↔
      upperTri q + q ≤ n + 1 + r := by
  have hs := hborrow.remainder_eq_of_eq_one hb
  have hqle := (hborrow.eq_one_iff.mp hb).2
  subst b
  subst s
  have hquotient : q + 1 - 1 = q := by omega
  rw [hquotient]
  rw [potential_nonnegative_iff]
  omega

/-- Exact Nat threshold for a one-borrow subtraction to reach `G≥0`. -/
theorem sub_oneBorrow_nonnegative_iff {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    0 ≤ potential (q - 1 - b) s ↔
      upperTri (q - 2) + q ≤ n + 1 + r := by
  have hs := hborrow.remainder_eq_of_eq_one hb
  have hqle := (hborrow.eq_one_iff.mp hb).2
  subst b
  subst s
  have hquotient : q - 1 - 1 = q - 2 := by omega
  rw [hquotient]
  rw [potential_nonnegative_iff]
  omega

/-- Failure of a one-borrow addition to recover is possible only beyond its
exact triangular threshold. -/
theorem add_oneBorrow_negative_iff {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    potential (q + 1 - b) s < 0 ↔
      n + 1 + r < upperTri q + q := by
  rw [← Int.not_le, add_oneBorrow_nonnegative_iff hborrow hb]
  omega

/-- The corresponding high-quotient barrier for subtraction. -/
theorem sub_oneBorrow_negative_iff {n q r b s : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    potential (q - 1 - b) s < 0 ↔
      n + 1 + r < upperTri (q - 2) + q := by
  rw [← Int.not_le, sub_oneBorrow_nonnegative_iff hborrow hb]
  omega

/-- Exact pre-state equation for one-borrow addition to land on `G=m`. -/
theorem add_oneBorrow_target_iff {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    potential (q + 1 - b) s = Int.ofNat m ↔
      n + 1 + r = q + upperTri q + m := by
  subst b
  simpa [BorrowTargetPreimage] using
    (potential_eq_iff_borrowTargetPreimage
      (k := q) (m := m) hborrow)

/-- Exact pre-state equation for one-borrow subtraction to land on `G=m`. -/
theorem sub_oneBorrow_target_iff {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1) :
    potential (q - 1 - b) s = Int.ofNat m ↔
      n + 1 + r = q + upperTri (q - 2) + m := by
  subst b
  have hquotient : q - 1 - 1 = q - 2 := by omega
  rw [hquotient]
  simpa [BorrowTargetPreimage] using
    (potential_eq_iff_borrowTargetPreimage
      (k := q - 2) (m := m) hborrow)

/-- Exact clock identity for any one-borrow landing on `(k,G=m)`.  The positive
slack `q-r` records the precise position inside the target time window. -/
theorem oneBorrow_target_time_eq {n q r b s k m : Nat}
    (hborrow : BorrowData n q r b s) (hb : b = 1)
    (htarget : potential k s = Int.ofNat m) :
    n + 1 = upperTri k + m + (q - r) ∧
      0 < q - r ∧ q - r ≤ q := by
  have hs : s = upperTri k + m :=
    (potential_eq_ofNat_iff k s m).mp htarget
  have hchamber := hborrow.eq_one_iff.mp hb
  have hbal := hborrow.balance
  subst b
  simp at hbal
  constructor
  · omega
  constructor <;> omega

/-- A one-borrow addition can hit a fixed target surface only inside a time
window of width `q`. -/
theorem add_oneBorrow_target_time_window {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1)
    (htarget : potential (q + 1 - b) s = Int.ofNat m) :
    upperTri q + m ≤ n ∧ n < upperTri q + m + q := by
  have heq := (add_oneBorrow_target_iff hborrow hb).mp htarget
  have hchamber := hborrow.eq_one_iff.mp hb
  have hrlt := hcoord.remainder_lt
  constructor <;> omega

/-- The subtraction target window has the same width, based at `U(q-2)+m`. -/
theorem sub_oneBorrow_target_time_window {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1)
    (htarget : potential (q - 1 - b) s = Int.ofNat m) :
    upperTri (q - 2) + m ≤ n ∧
      n < upperTri (q - 2) + m + q := by
  have heq := (sub_oneBorrow_target_iff hborrow hb).mp htarget
  have hchamber := hborrow.eq_one_iff.mp hb
  have hrlt := hcoord.remainder_lt
  constructor <;> omega

end Recaman
