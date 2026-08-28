import Recaman.DebtSubtraction
import Recaman.DebtInvariant

namespace Recaman

/-- A legal subtraction producing a positive-time first occurrence extends
backwards to a nonempty maximal subtraction suffix.  The suffix cannot start
at time zero, since the first Recamán step is not a legal subtraction. -/
theorem legalSubtraction_firstAt_maximalBackward
    {y fy : Nat}
    (hfirst : FirstAt a y fy)
    (hfy : 0 < fy)
    (hcan : CanSubtract fy (stateAt (fy - 1))) :
    ∃ start length,
      start + length = fy ∧
      1 ≤ length ∧
      0 < start ∧
      DescentRun start (a start) length ∧
      ¬ CanSubtract start (stateAt (start - 1)) ∧
      a start = y + descentDrop start length := by
  have htime : (fy - 1) + 1 = fy := by omega
  have hcan' : CanSubtract ((fy - 1) + 1) (stateAt (fy - 1)) := by
    simpa [htime] using hcan
  have hone : DescentRun (fy - 1) (a (fy - 1)) 1 := by
    constructor
    · rfl
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simpa using hcan'
  rcases hone.maximal_backward_extension with
    ⟨start, length, hend, hlength, hrun, hmaximal⟩
  have hend' : start + length = fy := by omega
  have hstart : 0 < start := by
    by_cases hzero : start = 0
    · subst start
      have hfirstStep := hrun.subtracts 0 (by omega)
      have himpossible : ¬ CanSubtract 1 (stateAt 0) := by decide
      exact False.elim (himpossible (by simpa using hfirstStep))
    · omega
  have hnot : ¬ CanSubtract start (stateAt (start - 1)) := by
    rcases hmaximal with hzero | hnot
    · omega
    · exact hnot
  have heq := hrun.equation_at (i := length) (Nat.le_refl _)
  have hstartValue : a start = y + descentDrop start length := by
    rw [hend', hfirst.1] at heq
    omega
  exact ⟨start, length, hend', hlength, hstart, hrun, hnot,
    hstartValue⟩

/-- If the maximal backward suffix has length at least two, the forced
addition immediately before it has a positive, previously seen subtraction
candidate.  Two suffix subtractions are exactly what makes that blocker stay
at or above the endpoint target. -/
theorem maximalBackward_long_exposes_blocker
    {m y start length : Nat}
    (hmy : m ≤ y)
    (hlength : 2 ≤ length)
    (hstart : 0 < start)
    (hrun : DescentRun start (a start) length)
    (hnot : ¬ CanSubtract start (stateAt (start - 1)))
    (hstartValue : a start = y + descentDrop start length) :
    ∃ z fz,
      z = a (start - 1) - start ∧
      m ≤ z ∧
      FirstAt a z fz ∧
      fz < start ∧
      z < a start ∧
      CoverageStep m (a start) start := by
  cases start with
  | zero => omega
  | succ u =>
      have hnot' : ¬ CanSubtract (u + 1) (stateAt u) := by
        simpa using hnot
      have hadd := a_succ_of_not_canSubtract hnot'
      let z := a u - (u + 1)
      have hmul : 2 * (u + 1) ≤ length * (u + 1) :=
        Nat.mul_le_mul_right (u + 1) hlength
      have htri : 3 ≤ upperTri length := by
        have := upperTri_mono hlength
        simpa using this
      have hzEndpoint : y + 3 ≤ z := by
        simp only [descentDrop] at hstartValue
        simp only [z]
        omega
      have hzLower : m ≤ z := by omega
      have hpositive : u + 1 < a u := by
        simp only [z] at hzEndpoint
        omega
      have hzSeen : z ∈ valuesThrough u := by
        by_cases hseen : z ∈ valuesThrough u
        · exact hseen
        · have hcan : CanSubtract (u + 1) (stateAt u) := by
            constructor
            · simpa [a] using hpositive
            · change a u - (u + 1) ∉ valuesThrough u
              simpa only [z] using hseen
          exact False.elim (hnot' hcan)
      rcases history_member_has_firstAt hzSeen with
        ⟨fz, hfz, hfirstZ⟩
      have hzStart : z < a (u + 1) := by
        simp only [z]
        omega
      have hcoverage : CoverageStep m (a (u + 1)) (u + 1) :=
        Or.inr ⟨z, fz, hzLower, hfirstZ, hzStart⟩
      exact ⟨z, fz, rfl, hzLower, hfirstZ, by omega, hzStart,
        hcoverage⟩

/-- A maximal suffix of length one is the sharp boundary case.  The value
immediately before the forced addition is exactly `y+1`; with `y<anchor` it
is below the anchor or equal to it.  Equality cannot be strengthened away
from these hypotheses. -/
theorem maximalBackward_one_predecessor_boundary
    {m anchor y start : Nat}
    (hmy : m ≤ y)
    (hyAnchor : y < anchor)
    (hstart : 0 < start)
    (hrun : DescentRun start (a start) 1)
    (hnot : ¬ CanSubtract start (stateAt (start - 1)))
    (hstartValue : a start = y + descentDrop start 1) :
    ∃ p fp,
      p = y + 1 ∧
      m ≤ p ∧
      FirstAt a p fp ∧
      fp < start ∧
      (p < anchor ∨ p = anchor) := by
  cases start with
  | zero => omega
  | succ u =>
      have hnot' : ¬ CanSubtract (u + 1) (stateAt u) := by
        simpa using hnot
      have hadd := a_succ_of_not_canSubtract hnot'
      have hp : a u = y + 1 := by
        simp [descentDrop, upperTri] at hstartValue
        omega
      rcases history_member_has_firstAt (current_mem_valuesThrough u) with
        ⟨fp, hfp, hfirstP⟩
      refine ⟨a u, fp, hp, ?_, hfirstP, by omega, ?_⟩
      · omega
      · omega

/-- Complete backward classification of the legal-subtraction debt branch.

* A suffix of length at least two exposes an above-target blocker whose first
  occurrence strictly lowers debt time.
* A suffix of length one exits to normal mode when its predecessor is below
  the anchor.
* The only remaining arithmetic boundary is `anchor = y+1`.

The last alternative is genuine: `y<anchor` only implies `y+1≤anchor`, not
the strict inequality required by `phaseSearch_exitDebt_of_anchorDrop`. -/
theorem legalSubtraction_maximalBackward_trichotomy
    {m horizon anchor y fy : Nat}
    (hfirst : FirstAt a y fy)
    (hfy : 0 < fy)
    (hcan : CanSubtract fy (stateAt (fy - 1)))
    (hmy : m ≤ y)
    (hyAnchor : y < anchor) :
    (∃ start z fz,
      m ≤ z ∧
      FirstAt a z fz ∧
      fz < fy ∧
      z < a start ∧
      CoverageStep m (a start) start ∧
      PhaseSearchProgress m
        ⟨horizon, anchor, .debt, fz⟩
        ⟨horizon, anchor, .debt, fy⟩) ∨
    (∃ p fp,
      p = y + 1 ∧
      m ≤ p ∧
      FirstAt a p fp ∧
      fp < fy ∧
      p < anchor ∧
      PhaseSearchProgress m
        ⟨horizon, p, .normal, p⟩
        ⟨horizon, anchor, .debt, fy⟩) ∨
    anchor = y + 1 := by
  rcases legalSubtraction_firstAt_maximalBackward hfirst hfy hcan with
    ⟨start, length, hend, hlength, hstart, hrun, hnot, hstartValue⟩
  rcases Nat.eq_or_lt_of_le hlength with hone | hlong
  · have hlengthOne : length = 1 := by omega
    subst length
    rcases maximalBackward_one_predecessor_boundary
        hmy hyAnchor hstart hrun hnot hstartValue with
      ⟨p, fp, hp, hmp, hfirstP, hfp, hpAnchor | hpAnchor⟩
    · exact Or.inr (Or.inl
        ⟨p, fp, hp, hmp, hfirstP, by omega, hpAnchor,
          phaseSearch_exitDebt_of_anchorDrop hpAnchor⟩)
    · exact Or.inr (Or.inr (by omega))
  · have hlengthTwo : 2 ≤ length := by omega
    rcases maximalBackward_long_exposes_blocker
        hmy hlengthTwo hstart hrun hnot hstartValue with
      ⟨z, fz, _, hmz, hfirstZ, hfz, hzStart, hcoverage⟩
    exact Or.inl
      ⟨start, z, fz, hmz, hfirstZ, by omega, hzStart, hcoverage,
        phaseSearch_debtTimeDrop (by omega)⟩

/-- The standard orbit realizes the length-one equality boundary: `2` first
appears by subtracting at time four, its maximal suffix starts at time three,
and the value before the forced addition is `3 = 2+1`. -/
theorem legalSubtraction_anchor_boundary_example :
    FirstAt a 2 4 ∧
    CanSubtract 4 (stateAt 3) ∧
    ¬ CanSubtract 3 (stateAt 2) ∧
    DescentRun 3 (a 3) 1 ∧
    a 2 = 3 := by
  have hfirst : FirstAt a 2 4 := by
    constructor
    · decide
    · intro u hu hvalue
      have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by omega
      rcases hcases with h | h | h | h
      · subst u
        exact (by decide : a 0 ≠ 2) hvalue
      · subst u
        exact (by decide : a 1 ≠ 2) hvalue
      · subst u
        exact (by decide : a 2 ≠ 2) hvalue
      · subst u
        exact (by decide : a 3 ≠ 2) hvalue
  refine ⟨hfirst, by decide, by decide, ?_, by decide⟩
  constructor
  · rfl
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact (by decide)

end Recaman
