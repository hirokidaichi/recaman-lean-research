import Recaman.MultiBorrow
import Recaman.Mechanisms

namespace Recaman

/-- The pre-state equation for borrow data `(b,s)` to land at quotient `k`
on the target surface `G=m`.  It eliminates the corrected remainder `s`. -/
def BorrowTargetPreimage (n q r b k m : Nat) : Prop :=
  b * (n + 1) + r = q + upperTri k + m

/-- Under valid borrow data, the target-preimage equation is exactly the
statement that the corrected remainder lies on `G=m` at quotient `k`. -/
theorem potential_eq_iff_borrowTargetPreimage {n q r b s k m : Nat}
    (hborrow : BorrowData n q r b s) :
    potential k s = Int.ofNat m ↔ BorrowTargetPreimage n q r b k m := by
  rw [potential_eq_ofNat_iff]
  unfold BorrowTargetPreimage
  have hbal := hborrow.balance
  constructor <;> intro h <;> omega

/-- Landing on a nonnegative target surface forces the triangular remainder
to fit below the new modulus. -/
theorem BorrowData.targetPreimage_bound {n q r b s k m : Nat}
    (hborrow : BorrowData n q r b s)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    upperTri k + m < n + 1 := by
  have hs : s = upperTri k + m :=
    (potential_eq_ofNat_iff k s m).mp
      ((potential_eq_iff_borrowTargetPreimage hborrow).mpr hpreimage)
  have hslt := hborrow.remainder_lt
  omega

/-- Addition lands at quotient `k` exactly when `q+1=b+k`. -/
theorem add_borrowQuotient_eq_iff {q b k : Nat} (hbq : b ≤ q + 1) :
    q + 1 - b = k ↔ q + 1 = b + k := by
  omega

/-- Legal subtraction lands at quotient `k` exactly when `q=b+k+1`. -/
theorem sub_borrowQuotient_eq_iff {q b k : Nat} (hbq : b + 1 ≤ q) :
    q - 1 - b = k ↔ q = b + k + 1 := by
  omega

/-- Complete inverse chart for the addition branch landing on `(k,G=m)`. -/
theorem add_borrowTarget_chart {n q r b s k m : Nat}
    (hborrow : BorrowData n q r b s) (hbq : b ≤ q + 1) :
    (q + 1 - b = k ∧ potential k s = Int.ofNat m) ↔
      (q + 1 = b + k ∧ BorrowTargetPreimage n q r b k m) := by
  constructor
  · rintro ⟨hquotient, hpotential⟩
    exact ⟨(add_borrowQuotient_eq_iff hbq).mp hquotient,
      (potential_eq_iff_borrowTargetPreimage hborrow).mp hpotential⟩
  · rintro ⟨hquotient, hpreimage⟩
    exact ⟨(add_borrowQuotient_eq_iff hbq).mpr hquotient,
      (potential_eq_iff_borrowTargetPreimage hborrow).mpr hpreimage⟩

/-- Complete inverse chart for the subtraction branch landing on `(k,G=m)`. -/
theorem sub_borrowTarget_chart {n q r b s k m : Nat}
    (hborrow : BorrowData n q r b s) (hbq : b + 1 ≤ q) :
    (q - 1 - b = k ∧ potential k s = Int.ofNat m) ↔
      (q = b + k + 1 ∧ BorrowTargetPreimage n q r b k m) := by
  constructor
  · rintro ⟨hquotient, hpotential⟩
    exact ⟨(sub_borrowQuotient_eq_iff hbq).mp hquotient,
      (potential_eq_iff_borrowTargetPreimage hborrow).mp hpotential⟩
  · rintro ⟨hquotient, hpreimage⟩
    exact ⟨(sub_borrowQuotient_eq_iff hbq).mpr hquotient,
      (potential_eq_iff_borrowTargetPreimage hborrow).mpr hpreimage⟩

/-- At zero borrow, the general preimage equation is precisely the previously
known regular-addition surface `G=m+(2q+1)`. -/
theorem zeroBorrow_targetPreimage_iff {n q r m : Nat} :
    BorrowTargetPreimage n q r 0 (q + 1) m ↔
      potential q r = Int.ofNat (m + (2 * q + 1)) := by
  simp [BorrowTargetPreimage, potential, upperTri]
  omega

/-- Addition-side inverse chart for the exact-gate quotient `k=2`. -/
theorem add_exactGate_chart {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s) (hbq : b ≤ q + 1) :
    (q + 1 - b = 2 ∧ potential 2 s = Int.ofNat m) ↔
      (q = b + 1 ∧ b * (n + 1) + r = q + m + 3) := by
  rw [add_borrowTarget_chart hborrow hbq]
  simp [BorrowTargetPreimage]
  omega

/-- Addition-side inverse chart for the local-escape quotient `k=3`. -/
theorem add_localEscape_chart {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s) (hbq : b ≤ q + 1) :
    (q + 1 - b = 3 ∧ potential 3 s = Int.ofNat m) ↔
      (q = b + 2 ∧ b * (n + 1) + r = q + m + 6) := by
  rw [add_borrowTarget_chart hborrow hbq]
  simp [BorrowTargetPreimage]
  omega

/-- Subtraction-side inverse chart for the exact-gate quotient `k=2`. -/
theorem sub_exactGate_chart {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s) (hbq : b + 1 ≤ q) :
    (q - 1 - b = 2 ∧ potential 2 s = Int.ofNat m) ↔
      (q = b + 3 ∧ b * (n + 1) + r = q + m + 3) := by
  rw [sub_borrowTarget_chart hborrow hbq]
  simp [BorrowTargetPreimage]
  omega

/-- Subtraction-side inverse chart for the local-escape quotient `k=3`. -/
theorem sub_localEscape_chart {n q r b s m : Nat}
    (hborrow : BorrowData n q r b s) (hbq : b + 1 ≤ q) :
    (q - 1 - b = 3 ∧ potential 3 s = Int.ofNat m) ↔
      (q = b + 4 ∧ b * (n + 1) + r = q + m + 6) := by
  rw [sub_borrowTarget_chart hborrow hbq]
  simp [BorrowTargetPreimage]
  omega

/-- An actual addition satisfying the inverse chart enters `(k,G=m)`. -/
theorem coordinates_add_enters_borrowTarget {n q r b s k m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hquotient : q + 1 = b + k)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    CoordinatesAt (n + 1) k s ∧ potential k s = Int.ofNat m := by
  have hbq : b ≤ q + 1 := hborrow.le_q_add_one
  have hq : q + 1 - b = k :=
    (add_borrowQuotient_eq_iff hbq).mpr hquotient
  have hstep := coordinates_add_borrowData hcoord hborrow hbq hnot
  constructor
  · simpa only [hq] using hstep.1
  · exact (potential_eq_iff_borrowTargetPreimage hborrow).mpr hpreimage

/-- An actual legal subtraction satisfying the inverse chart enters `(k,G=m)`. -/
theorem coordinates_sub_enters_borrowTarget {n q r b s k m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hquotient : q = b + k + 1)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    CoordinatesAt (n + 1) k s ∧ potential k s = Int.ofNat m := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  have hq : q - 1 - b = k :=
    (sub_borrowQuotient_eq_iff hbq).mpr hquotient
  have hstep := coordinates_sub_borrowData hcoord hborrow hbq hcan
  constructor
  · simpa only [hq] using hstep.1
  · exact (potential_eq_iff_borrowTargetPreimage hborrow).mpr hpreimage

/-- Addition through a borrow-target chart supplies the next target equation. -/
theorem add_borrowTarget_gives_targetEquation {n q r b s k m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hquotient : q + 1 = b + k)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    TargetEquation (n + 1) (a (n + 1)) m k := by
  rcases coordinates_add_enters_borrowTarget hcoord hborrow hnot
    hquotient hpreimage with ⟨hnext, hpotential⟩
  exact targetEquation_of_quotRem_potential hnext hpotential

/-- Subtraction through a borrow-target chart supplies the next target equation. -/
theorem sub_borrowTarget_gives_targetEquation {n q r b s k m : Nat}
    (hcoord : CoordinatesAt n q r) (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hquotient : q = b + k + 1)
    (hpreimage : BorrowTargetPreimage n q r b k m) :
    TargetEquation (n + 1) (a (n + 1)) m k := by
  rcases coordinates_sub_enters_borrowTarget hcoord hborrow hcan
    hquotient hpreimage with ⟨hnext, hpotential⟩
  exact targetEquation_of_quotRem_potential hnext hpotential

/-- Every actual point on `G=m` satisfies the sharp time bound
`U(k)+m<f`. -/
theorem targetSurface_time_bound {f k r m : Nat}
    (hcoord : CoordinatesAt f k r)
    (hpotential : potential k r = Int.ofNat m) :
    upperTri k + m < f := by
  have hr : r = upperTri k + m :=
    (potential_eq_ofNat_iff k r m).mp hpotential
  have hrlt : r < f := hcoord.remainder_lt
  omega

/-- The `k=2` target surface is not only a target equation: it has exactly the
value shape required by the two-step exact gate, together with its size bound. -/
theorem targetSurface_two_value {u r m : Nat}
    (hcoord : CoordinatesAt u 2 r)
    (hpotential : potential 2 r = Int.ofNat m) :
    (stateAt u).value = 2 * u + m + 3 ∧ m + 3 < u := by
  have hr : r = upperTri 2 + m :=
    (potential_eq_ofNat_iff 2 r m).mp hpotential
  have heq := hcoord.eqn
  change (stateAt u).value = u * 2 + r at heq
  have hbound := targetSurface_time_bound hcoord hpotential
  constructor <;> simp at hr hbound ⊢ <;> omega

/-- Freshness upgrades a `k=2,G=m` target-surface point to an actual occurrence
of `m` via the exact gate. -/
theorem targetSurface_two_occurs {u r m : Nat}
    (hm : 0 < m) (hcoord : CoordinatesAt u 2 r)
    (hpotential : potential 2 r = Int.ofNat m)
    (hintermediate : gateIntermediate u m ∉ (stateAt u).seen)
    (hmfresh : m ∉ (stateAt u).seen) :
    ∃ t, a t = m := by
  have hvalue := (targetSurface_two_value hcoord hpotential).1
  exact exactGate_at_occurs hm hvalue hintermediate hmfresh

/-- The `k=3` target surface has the exact post-addition value shape of the
local `+---` family, although its extra history-freshness assumptions remain
separate. -/
theorem targetSurface_three_value {u r m : Nat}
    (hcoord : CoordinatesAt u 3 r)
    (hpotential : potential 3 r = Int.ofNat m) :
    (stateAt u).value = 3 * u + m + 6 ∧ m + 6 < u := by
  have hr : r = upperTri 3 + m :=
    (potential_eq_ofNat_iff 3 r m).mp hpotential
  have heq := hcoord.eqn
  change (stateAt u).value = u * 3 + r at heq
  have hbound := targetSurface_time_bound hcoord hpotential
  constructor <;> simp at hr hbound ⊢ <;> omega

end Recaman
