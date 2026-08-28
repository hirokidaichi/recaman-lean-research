import Std

namespace Recaman

/-- Lower triangular number T(q) = q(q-1)/2, defined without division. -/
def lowerTri : Nat → Nat
  | 0 => 0
  | q + 1 => lowerTri q + q

/-- Upper triangular number U(q) = q(q+1)/2, defined without division. -/
def upperTri : Nat → Nat
  | 0 => 0
  | q + 1 => upperTri q + q + 1

/-- The two triangular conventions differ by exactly their index. -/
theorem upperTri_eq_lowerTri_add (q : Nat) :
    upperTri q = lowerTri q + q := by
  induction q with
  | zero => simp [upperTri, lowerTri]
  | succ q ih =>
      simp [upperTri, lowerTri, ih]
      omega

/-- Signed coordinate G = r - U(q). -/
def potential (q r : Nat) : Int :=
  Int.ofNat r - Int.ofNat (upperTri q)

/-- A nonnegative potential level is equivalent to an ordinary remainder
equation.  This centralizes the bridge from signed `G`-coordinates to Nat
arithmetic. -/
theorem potential_eq_ofNat_iff (q r m : Nat) :
    potential q r = Int.ofNat m ↔ r = upperTri q + m := by
  constructor
  · intro hpotential
    change Int.ofNat r - Int.ofNat (upperTri q) = Int.ofNat m at hpotential
    have hrInt : Int.ofNat r = Int.ofNat (upperTri q + m) := by
      have hcast : Int.ofNat (upperTri q + m) =
          Int.ofNat (upperTri q) + Int.ofNat m := rfl
      rw [hcast]
      omega
    exact Int.ofNat.inj hrInt
  · intro hr
    rw [hr]
    simp [potential]
    omega

/-- Nonnegativity of the signed potential is exactly the triangular remainder
bound. -/
theorem potential_nonnegative_iff (q r : Nat) :
    0 ≤ potential q r ↔ upperTri q ≤ r := by
  unfold potential
  constructor
  · intro h
    have hcast : Int.ofNat (upperTri q) ≤ Int.ofNat r := by omega
    exact Int.ofNat_le.mp hcast
  · intro h
    have hcast : Int.ofNat (upperTri q) ≤ Int.ofNat r :=
      Int.ofNat_le.mpr h
    omega

/-- Comparing a nonnegative target level with the signed potential is exactly
the corresponding natural-number remainder inequality. -/
theorem ofNat_le_potential_iff (q r m : Nat) :
    Int.ofNat m ≤ potential q r ↔ upperTri q + m ≤ r := by
  unfold potential
  constructor
  · intro h
    have hcast : Int.ofNat (upperTri q + m) ≤ Int.ofNat r := by
      change Int.ofNat (upperTri q) + Int.ofNat m ≤ Int.ofNat r
      omega
    exact Int.ofNat_le.mp hcast
  · intro h
    have hcast : Int.ofNat (upperTri q + m) ≤ Int.ofNat r :=
      Int.ofNat_le.mpr h
    change Int.ofNat (upperTri q) + Int.ofNat m ≤ Int.ofNat r at hcast
    omega

/-- A proof-carrying quotient and remainder representation a = nq + r. -/
structure QuotRem (n a q r : Nat) : Prop where
  eqn : a = n * q + r
  remainder_lt : r < n

@[simp] theorem lowerTri_two : lowerTri 2 = 1 := by
  decide

@[simp] theorem upperTri_two : upperTri 2 = 3 := by
  decide

@[simp] theorem upperTri_three : upperTri 3 = 6 := by
  decide

/-- The pre-escape value 2s+m+6 has coordinates q=2, r=m+8
when s is sufficiently larger than m. -/
theorem preEscape_quotRem {s m : Nat} (hlarge : m + 9 < s) :
    QuotRem (s - 1) (2 * s + m + 6) 2 (m + 8) := by
  constructor <;> omega

/-- Its signed potential is m+5. -/
theorem preEscape_potential (m : Nat) :
    potential 2 (m + 8) = Int.ofNat (m + 5) := by
  simp [potential]
  omega

/-- After the forced addition, 3s+m+6 has coordinates q=3, r=m+6. -/
theorem postAddition_quotRem {s m : Nat} (hlarge : m + 9 < s) :
    QuotRem s (3 * s + m + 6) 3 (m + 6) := by
  constructor <;> omega

/-- The forced addition changes the signed potential from m+5 to m. -/
theorem postAddition_potential (m : Nat) :
    potential 3 (m + 6) = Int.ofNat m := by
  simp [potential]

end Recaman
