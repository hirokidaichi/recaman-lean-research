import Recaman.DebtBackward

namespace Recaman

/-- The length-one equality boundary has a rigid two-step shape.  The orbit is
at `anchor = y+1`, is forced up by `start`, and immediately subtracts
`start+1` to land at the new value `y`.

This isolates the boundary as a single forced-addition obstruction rather
than an unconstrained legal-subtraction case. -/
theorem anchorBoundary_exact_local_shape
    {anchor y start : Nat}
    (hanchor : anchor = y + 1)
    (hstart : 0 < start)
    (hrun : DescentRun start (a start) 1)
    (hnot : ¬ CanSubtract start (stateAt (start - 1)))
    (hstartValue : a start = y + descentDrop start 1) :
    a (start - 1) = anchor ∧
      a start = anchor + start ∧
      a (start + 1) = y := by
  cases start with
  | zero => omega
  | succ u =>
      have hnot' : ¬ CanSubtract (u + 1) (stateAt u) := by
        simpa using hnot
      have hadd := a_succ_of_not_canSubtract hnot'
      have hstartValue' : a (u + 1) = y + (u + 2) := by
        simpa [descentDrop, upperTri] using hstartValue
      have hpre : a u = anchor := by
        rw [hadd] at hstartValue'
        omega
      have hsubtract := hrun.subtracts 0 (by omega)
      have hnext := a_succ_of_canSubtract hsubtract
      refine ⟨by simpa using hpre, ?_, ?_⟩
      · omega
      · rw [hstartValue'] at hnext
        simpa using (show a (u + 1 + 1) = y by omega)

/-- At the equality boundary, the landing value itself supplies the strict
anchor decrease that the predecessor `y+1` cannot supply.  Thus the equality
alternative in `legalSubtraction_maximalBackward_trichotomy` is not a rank
obstruction once a normal node is allowed to restart from the first-occurring
landing value. -/
theorem anchorBoundary_exitNormal_at_landing
    {m horizon anchor y fy : Nat}
    (hmy : m ≤ y)
    (hfirst : FirstAt a y fy)
    (hanchor : anchor = y + 1) :
    m ≤ y ∧ FirstAt a y fy ∧
      PhaseSearchProgress m
        ⟨horizon, y, .normal, y⟩
        ⟨horizon, anchor, .debt, fy⟩ := by
  refine ⟨hmy, hfirst, phaseSearch_exitDebt_of_anchorDrop ?_⟩
  omega

/-- If the target equals the length-one landing, it has already occurred;
otherwise restarting normal search at the landing strictly lowers the anchor.
This is the semantic closure of the arithmetic equality boundary. -/
theorem anchorBoundary_target_or_exitNormal
    {m horizon anchor y fy : Nat}
    (hmy : m ≤ y)
    (hfirst : FirstAt a y fy)
    (hanchor : anchor = y + 1) :
    (∃ t, a t = m) ∨
      (m < y ∧ FirstAt a y fy ∧
        PhaseSearchProgress m
          ⟨horizon, y, .normal, y⟩
          ⟨horizon, anchor, .debt, fy⟩) := by
  rcases Nat.eq_or_lt_of_le hmy with heq | hlt
  · subst y
    exact Or.inl ⟨fy, hfirst.1⟩
  · exact Or.inr ⟨hlt, hfirst,
      phaseSearch_exitDebt_of_anchorDrop (by omega)⟩

/-- In the nonpositive-candidate wedge `anchor ≤ start`, the coordinate
geometry is completely explicit.  The landing has quotient zero.  At the
intermediate spike the quotient is one, except on the sharp diagonal
`anchor = start`, where it is two with zero remainder. -/
theorem anchorBoundary_nonpositive_coordinates
    {anchor y start : Nat}
    (hanchor : anchor = y + 1)
    (hstart : 0 < start)
    (hrun : DescentRun start (a start) 1)
    (hnot : ¬ CanSubtract start (stateAt (start - 1)))
    (hstartValue : a start = y + descentDrop start 1)
    (hnonpositive : anchor ≤ start) :
    CoordinatesAt (start + 1) 0 y ∧
      ((anchor < start ∧ CoordinatesAt start 1 anchor) ∨
        (anchor = start ∧ CoordinatesAt start 2 0)) := by
  have hshape := anchorBoundary_exact_local_shape
    hanchor hstart hrun hnot hstartValue
  constructor
  · constructor
    · simp [hshape.2.2]
    · omega
  · rcases Nat.eq_or_lt_of_le hnonpositive with heq | hlt
    · right
      refine ⟨heq, ?_⟩
      constructor
      · rw [hshape.2.1, heq]
        omega
      · exact hstart
    · left
      refine ⟨hlt, ?_⟩
      constructor
      · rw [hshape.2.1]
        omega
      · exact hlt

/-- The forced addition at the boundary has one of three useful meanings.

* its subtraction candidate is nonpositive (`anchor ≤ start`);
* its positive blocker is below the target and is already in the fixed
  history horizon;
* or that blocker is at least the target, in which case its first occurrence
  gives a strict anchor-decreasing normal child.

Consequently the forced-addition reason reduces to the nonpositive wedge
`anchor ≤ start`, together with already-consumed history below the target. -/
theorem anchorBoundary_forced_reason
    {m horizon anchor y start fy : Nat}
    (_hmy : m ≤ y)
    (hanchor : anchor = y + 1)
    (hfy : fy = start + 1)
    (hhorizon : start ≤ horizon)
    (hstart : 0 < start)
    (hrun : DescentRun start (a start) 1)
    (hnot : ¬ CanSubtract start (stateAt (start - 1)))
    (hstartValue : a start = y + descentDrop start 1) :
    anchor ≤ start ∨
      (∃ x fx,
        x = anchor - start ∧
        0 < x ∧
        FirstAt a x fx ∧
        fx < fy ∧
        x < m ∧
        x ∈ valuesThrough horizon) ∨
      (∃ x fx,
        x = anchor - start ∧
        m ≤ x ∧
        FirstAt a x fx ∧
        fx < fy ∧
        x < anchor ∧
        PhaseSearchProgress m
          ⟨horizon, x, .normal, x⟩
          ⟨horizon, anchor, .debt, fy⟩) := by
  have hshape := anchorBoundary_exact_local_shape
    hanchor hstart hrun hnot hstartValue
  by_cases hpositive : start < anchor
  · have hcanFail : anchor - start ∈ valuesThrough (start - 1) := by
      by_cases hseen : anchor - start ∈ valuesThrough (start - 1)
      · exact hseen
      · have hcan : CanSubtract start (stateAt (start - 1)) := by
          constructor
          · change start < a (start - 1)
            rw [hshape.1]
            exact hpositive
          · change a (start - 1) - start ∉ valuesThrough (start - 1)
            rw [hshape.1]
            exact hseen
        exact False.elim (hnot hcan)
    rcases history_member_has_firstAt hcanFail with
      ⟨fx, hfxBound, hfirst⟩
    let x := anchor - start
    have hxPositive : 0 < x := by
      simp only [x]
      omega
    have hxAnchor : x < anchor := by
      simp only [x]
      omega
    by_cases hxm : x < m
    · right
      left
      refine ⟨x, fx, rfl, hxPositive, hfirst, ?_, hxm, ?_⟩
      · omega
      · apply valuesThrough_mono (n := start - 1) (t := horizon)
        · omega
        · exact hcanFail
    · right
      right
      refine ⟨x, fx, rfl, Nat.le_of_not_gt hxm, hfirst, ?_, hxAnchor,
        phaseSearch_exitDebt_of_anchorDrop hxAnchor⟩
      omega
  · left
    exact Nat.le_of_not_gt hpositive

/-- The standard orbit shows that the residual nonpositive wedge is real:
the boundary landing `2` has `anchor = start = 3`.  Hence neither
`anchor < start` nor `start < anchor` is derivable from the length-one
boundary hypotheses. -/
theorem anchorBoundary_nonpositive_wedge_example :
    let y := 2
    let anchor := 3
    let start := 3
    anchor = y + 1 ∧
      anchor = start ∧
      ¬ CanSubtract start (stateAt (start - 1)) ∧
      DescentRun start (a start) 1 ∧
      a start = y + descentDrop start 1 := by
  dsimp
  refine ⟨rfl, rfl, by decide, ?_, by decide⟩
  constructor
  · rfl
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact (by decide)

end Recaman
