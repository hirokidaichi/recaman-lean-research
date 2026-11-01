import Recaman.RecoveryBudget

namespace Recaman

/-- A one-borrow addition into the exact-gate quotient `2` can occur on
`G=m` only at times `m+3` or `m+4`. -/
theorem add_oneBorrow_exactGate_time_window {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hquotient : q + 1 - b = 2)
    (htarget : potential 2 s = Int.ofNat m) :
    m + 3 ≤ n ∧ n < m + 5 := by
  have hq : q = 2 := by omega
  have htarget' : potential (q + 1 - b) s = Int.ofNat m := by
    simpa [hquotient] using htarget
  have hwindow :=
    add_oneBorrow_target_time_window hcoord hborrow hb htarget'
  simp [hq] at hwindow
  omega

/-- The one-borrow addition window for the local-escape quotient `3`. -/
theorem add_oneBorrow_localEscape_time_window {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hquotient : q + 1 - b = 3)
    (htarget : potential 3 s = Int.ofNat m) :
    m + 6 ≤ n ∧ n < m + 9 := by
  have hq : q = 3 := by omega
  have htarget' : potential (q + 1 - b) s = Int.ofNat m := by
    simpa [hquotient] using htarget
  have hwindow :=
    add_oneBorrow_target_time_window hcoord hborrow hb htarget'
  simp [hq] at hwindow
  omega

/-- A one-borrow subtraction into quotient `2` has a four-time target window. -/
theorem sub_oneBorrow_exactGate_time_window {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hquotient : q - 1 - b = 2)
    (htarget : potential 2 s = Int.ofNat m) :
    m + 3 ≤ n ∧ n < m + 7 := by
  have hq : q = 4 := by omega
  have htarget' : potential (q - 1 - b) s = Int.ofNat m := by
    simpa [hquotient] using htarget
  have hwindow :=
    sub_oneBorrow_target_time_window hcoord hborrow hb htarget'
  simp [hq] at hwindow
  omega

/-- The one-borrow subtraction window for quotient `3`. -/
theorem sub_oneBorrow_localEscape_time_window {n q r b s m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hb : b = 1) (hquotient : q - 1 - b = 3)
    (htarget : potential 3 s = Int.ofNat m) :
    m + 6 ≤ n ∧ n < m + 11 := by
  have hq : q = 5 := by omega
  have htarget' : potential (q - 1 - b) s = Int.ofNat m := by
    simpa [hquotient] using htarget
  have hwindow :=
    sub_oneBorrow_target_time_window hcoord hborrow hb htarget'
  simp [hq] at hwindow
  omega

end Recaman
