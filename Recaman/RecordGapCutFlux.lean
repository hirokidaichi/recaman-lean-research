import Std

namespace Recaman

/-! # Finite cut flux for record gaps

This module is deliberately independent of the Recamán orbit.  It isolates
the finite integer telescoping statement needed to turn a record gap into a
signed first-occurrence ancestry flux.
-/

/-- Projection of an integer onto the closed interval `[lower, upper]`. -/
def cutClip (lower upper value : Int) : Int :=
  if value ≤ lower then lower
  else if upper ≤ value then upper
  else value

@[simp] theorem cutClip_of_le_lower
    {lower upper value : Int}
    (_hbound : lower ≤ upper)
    (hvalue : value ≤ lower) :
    cutClip lower upper value = lower := by
  simp [cutClip, hvalue]

@[simp] theorem cutClip_of_upper_le
    {lower upper value : Int}
    (hbound : lower ≤ upper)
    (hvalue : upper ≤ value) :
    cutClip lower upper value = upper := by
  by_cases hlower : value ≤ lower
  · rw [cutClip, if_pos hlower]
    omega
  · simp [cutClip, hlower, hvalue]

/-- Projection to a cut is monotone and one-Lipschitz.  Thus the clipped
part of one addition-origin edge never exceeds its clock-sized edge. -/
theorem cutClip_monotone_lipschitz
    {lower upper first second : Int}
    (hbound : lower ≤ upper)
    (horder : first ≤ second) :
    0 ≤ cutClip lower upper second - cutClip lower upper first ∧
      cutClip lower upper second - cutClip lower upper first ≤ second - first := by
  by_cases hsecondLower : second ≤ lower <;>
    by_cases hupperSecond : upper ≤ second <;>
    by_cases hfirstLower : first ≤ lower <;>
    by_cases hupperFirst : upper ≤ first <;>
    simp [cutClip, hsecondLower, hupperSecond, hfirstLower, hupperFirst] <;>
    omega

/-- Recursive sum of the adjacent signed displacements of a path. -/
def pathSignedFlux (path : Nat → Int) : Nat → Int
  | 0 => 0
  | length + 1 =>
      pathSignedFlux path length + (path length - path (length + 1))

theorem pathSignedFlux_eq
    (path : Nat → Int) (length : Nat) :
    pathSignedFlux path length = path 0 - path length := by
  induction length with
  | zero => simp [pathSignedFlux]
  | succ length ih =>
      simp only [pathSignedFlux, ih]
      omega

/-- Signed displacement after projecting every path vertex onto a cut. -/
def pathCutFlux (lower upper : Int) (path : Nat → Int) (length : Nat) : Int :=
  pathSignedFlux (fun index => cutClip lower upper (path index)) length

/-- A path which starts at or above the upper side of a cut and ends at or
below its lower side has signed clipped displacement exactly equal to the
cut width.  Positive summands are downward crossings and negative summands
are upward crossings when the path is read from child to first-occurrence
predecessor. -/
theorem path_cut_balance
    (path : Nat → Int) (length : Nat) {lower upper : Int}
    (hbound : lower ≤ upper)
    (hstart : upper ≤ path 0)
    (hfinish : path length ≤ lower) :
    pathCutFlux lower upper path length = upper - lower := by
  simp only [pathCutFlux, pathSignedFlux_eq]
  rw [cutClip_of_upper_le hbound hstart]
  rw [cutClip_of_le_lower hbound hfinish]

/-- The nonnegative part of a signed displacement. -/
def positivePart (value : Int) : Int :=
  if 0 ≤ value then value else 0

@[simp] theorem positivePart_nonnegative (value : Int) :
    0 ≤ positivePart value := by
  simp only [positivePart]
  split <;> omega

theorem self_eq_positivePart_sub_reverse (value : Int) :
    value = positivePart value - positivePart (-value) := by
  simp only [positivePart]
  split <;> split <;> omega

/-- Total downward clipped crossing mass of a finite path. -/
def pathPositiveCutFlux (lower upper : Int) (path : Nat → Int) : Nat → Int
  | 0 => 0
  | length + 1 =>
      pathPositiveCutFlux lower upper path length +
        positivePart
          (cutClip lower upper (path length) -
            cutClip lower upper (path (length + 1)))

/-- Total upward clipped crossing mass of a finite path. -/
def pathNegativeCutFlux (lower upper : Int) (path : Nat → Int) : Nat → Int
  | 0 => 0
  | length + 1 =>
      pathNegativeCutFlux lower upper path length +
        positivePart
          (cutClip lower upper (path (length + 1)) -
            cutClip lower upper (path length))

@[simp] theorem pathNegativeCutFlux_nonnegative
    (lower upper : Int) (path : Nat → Int) (length : Nat) :
    0 ≤ pathNegativeCutFlux lower upper path length := by
  induction length with
  | zero => simp [pathNegativeCutFlux]
  | succ length ih =>
      simp only [pathNegativeCutFlux]
      have hpart := positivePart_nonnegative
        (cutClip lower upper (path (length + 1)) -
          cutClip lower upper (path length))
      omega

theorem pathCutFlux_eq_positive_sub_negative
    (lower upper : Int) (path : Nat → Int) (length : Nat) :
    pathCutFlux lower upper path length =
      pathPositiveCutFlux lower upper path length -
        pathNegativeCutFlux lower upper path length := by
  induction length with
  | zero => simp [pathCutFlux, pathSignedFlux, pathPositiveCutFlux,
      pathNegativeCutFlux]
  | succ length ih =>
      simp only [pathCutFlux, pathSignedFlux, pathPositiveCutFlux,
        pathNegativeCutFlux] at ih ⊢
      have hpart := self_eq_positivePart_sub_reverse
        (cutClip lower upper (path length) -
          cutClip lower upper (path (length + 1)))
      have hreverse :
          -(cutClip lower upper (path length) -
              cutClip lower upper (path (length + 1))) =
            cutClip lower upper (path (length + 1)) -
              cutClip lower upper (path length) := by omega
      rw [hreverse] at hpart
      omega

/-- Addition-oriented clipped crossing mass minus subtraction-oriented
clipped crossing mass is the record-gap width. -/
theorem path_cut_positive_negative_balance
    (path : Nat → Int) (length : Nat) {lower upper : Int}
    (hbound : lower ≤ upper)
    (hstart : upper ≤ path 0)
    (hfinish : path length ≤ lower) :
    pathPositiveCutFlux lower upper path length -
        pathNegativeCutFlux lower upper path length = upper - lower := by
  rw [← pathCutFlux_eq_positive_sub_negative]
  exact path_cut_balance path length hbound hstart hfinish

/-- In particular, the record-gap width is at most the total downward
clipped crossing mass. -/
theorem path_cut_le_positive_crossing
    (path : Nat → Int) (length : Nat) {lower upper : Int}
    (hbound : lower ≤ upper)
    (hstart : upper ≤ path 0)
    (hfinish : path length ≤ lower) :
    upper - lower ≤ pathPositiveCutFlux lower upper path length := by
  have hbalance :=
    path_cut_positive_negative_balance path length hbound hstart hfinish
  have hnonnegative :=
    pathNegativeCutFlux_nonnegative lower upper path length
  omega

/-- If both endpoints stay on the upper side of a cut, its signed flux is
zero.  Internal excursions across the cut cannot create endpoint progress. -/
theorem path_cut_zero_of_endpoints_above
    (path : Nat → Int) (length : Nat) {lower upper : Int}
    (hbound : lower ≤ upper)
    (hstart : upper ≤ path 0)
    (hfinish : upper ≤ path length) :
    pathCutFlux lower upper path length = 0 := by
  simp only [pathCutFlux, pathSignedFlux_eq]
  rw [cutClip_of_upper_le hbound hstart]
  rw [cutClip_of_upper_le hbound hfinish]
  omega

/-- Consequently every downward crossing of such a cut is paid by an equal
upward crossing.  This is the algebraic obstruction to extracting a strict
anchor drop from a path whose pre-tail root remains above the active anchor. -/
theorem path_positive_eq_negative_of_endpoints_above
    (path : Nat → Int) (length : Nat) {lower upper : Int}
    (hbound : lower ≤ upper)
    (hstart : upper ≤ path 0)
    (hfinish : upper ≤ path length) :
    pathPositiveCutFlux lower upper path length =
      pathNegativeCutFlux lower upper path length := by
  have hzero :=
    path_cut_zero_of_endpoints_above path length hbound hstart hfinish
  rw [pathCutFlux_eq_positive_sub_negative] at hzero
  omega

/-- If every vertex stays above the cut, not only the signed flux but each
one-sided crossing mass vanishes.  This is the form used by an ancestry
search which stops before its first strict anchor crossing. -/
theorem path_positive_negative_zero_of_all_above
    (path : Nat → Int) (length : Nat) {lower upper : Int}
    (hbound : lower ≤ upper)
    (hall : ∀ index, index ≤ length → upper ≤ path index) :
    pathPositiveCutFlux lower upper path length = 0 ∧
      pathNegativeCutFlux lower upper path length = 0 := by
  induction length with
  | zero =>
      simp [pathPositiveCutFlux, pathNegativeCutFlux]
  | succ length ih =>
      have ihall : ∀ index, index ≤ length → upper ≤ path index := by
        intro index hindex
        exact hall index (Nat.le_trans hindex (Nat.le_succ length))
      rcases ih ihall with ⟨hpositive, hnegative⟩
      have hleft : cutClip lower upper (path length) = upper :=
        cutClip_of_upper_le hbound (hall length (by omega))
      have hright : cutClip lower upper (path (length + 1)) = upper :=
        cutClip_of_upper_le hbound (hall (length + 1) (by omega))
      simp [pathPositiveCutFlux, pathNegativeCutFlux,
        hpositive, hnegative, hleft, hright, positivePart]

end Recaman
