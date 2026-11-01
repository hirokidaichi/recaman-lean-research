import Recaman.HistoryFrontier

namespace Recaman

/-- A positive diagonal state `a_t=t` cannot have been reached by addition:
the previous value would have to be zero at positive time.  Hence its last
step was a legal subtraction from exactly `2t`. -/
theorem diagonal_last_step {n : Nat}
    (hdiagonal : a (n + 2) = n + 2) :
    CanSubtract (n + 2) (stateAt (n + 1)) ∧
      a (n + 1) = 2 * (n + 2) := by
  have hprevPositive : 0 < a (n + 1) :=
    a_pos_of_pos_time (by omega)
  by_cases hcan : CanSubtract (n + 2) (stateAt (n + 1))
  · have hvalue := a_succ_of_canSubtract hcan
    have hvalue' : a (n + 2) = a (n + 1) - (n + 2) := by
      simpa [Nat.add_assoc] using hvalue
    have hstepPositive : n + 2 < a (n + 1) := by
      simpa [a, Nat.add_assoc] using hcan.1
    constructor
    · exact hcan
    · omega
  · have hvalue := a_succ_of_not_canSubtract hcan
    have hvalue' : a (n + 2) = a (n + 1) + (n + 2) := by
      simpa [Nat.add_assoc] using hvalue
    omega

/-- Looking one step farther back gives the exact residual dichotomy for the
diagonal-successor problem.  Either `t+1` already occurred two times before
the diagonal `a_t=t`, or the diagonal was preceded by two legal subtractions
from the `q=3, G=-1` surface. -/
theorem diagonal_successor_occurs_or_longDescent {n : Nat}
    (hdiagonal : a (n + 2) = n + 2) :
    (∃ u, a u = n + 3) ∨
      (CanSubtract (n + 1) (stateAt n) ∧
        CoordinatesAt n 3 5 ∧ potential 3 5 = -1) := by
  rcases diagonal_last_step hdiagonal with ⟨_, hprevious⟩
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · have hvalue := a_succ_of_canSubtract hcan
    have hpositive : n + 1 < a n := by
      simpa [a] using hcan.1
    have hexact : a n = 3 * n + 5 := by omega
    have hn : 6 ≤ n := by
      by_cases hn : 6 ≤ n
      · exact hn
      · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨
            n = 3 ∨ n = 4 ∨ n = 5 := by omega
        rcases hcases with h | h | h | h | h | h
        · subst n
          exact False.elim
            ((by decide : a 2 ≠ 2) (by simpa using hdiagonal))
        · subst n
          exact False.elim
            ((by decide : a 3 ≠ 3) (by simpa using hdiagonal))
        · subst n
          exact False.elim
            ((by decide : a 4 ≠ 4) (by simpa using hdiagonal))
        · subst n
          exact False.elim
            ((by decide : a 5 ≠ 5) (by simpa using hdiagonal))
        · subst n
          exact False.elim
            ((by decide : a 6 ≠ 6) (by simpa using hdiagonal))
        · subst n
          exact False.elim
            ((by decide : a 7 ≠ 7) (by simpa using hdiagonal))
    have hcoord : CoordinatesAt n 3 5 := by
      constructor
      · omega
      · omega
    exact Or.inr ⟨hcan, hcoord, by decide⟩
  · have hvalue := a_succ_of_not_canSubtract hcan
    have htarget : a n = n + 3 := by omega
    exact Or.inl ⟨n, htarget⟩

/-- In the unresolved branch, the final two subtractions extend uniquely
backwards to a maximal consecutive subtraction suffix. -/
theorem diagonal_longDescent_has_maximalTail {n : Nat}
    (hdiagonal : a (n + 2) = n + 2)
    (hpenultimate : CanSubtract (n + 1) (stateAt n)) :
    ∃ start length,
      start + length = n + 2 ∧ 2 ≤ length ∧ 0 < start ∧
      DescentRun start (a start) length ∧
      ¬ CanSubtract start (stateAt (start - 1)) := by
  rcases diagonal_last_step hdiagonal with ⟨hlast, _⟩
  have htwoRun : DescentRun n (a n) 2 := by
    constructor
    · rfl
    · intro i hi
      have hicases : i = 0 ∨ i = 1 := by omega
      rcases hicases with hzero | hone
      · subst i
        simpa using hpenultimate
      · subst i
        simpa [Nat.add_assoc] using hlast
  rcases htwoRun.maximal_backward_extension with
    ⟨start, length, hend, hlength, hrun, hmaximal⟩
  have hstartPositive : 0 < start := by
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
  exact ⟨start, length, hend, hlength, hstartPositive, hrun, hnot⟩

/-- At the beginning of that maximal suffix, addition was forced by a
previously seen candidate.  For every suffix of length at least two, this
blocker is not merely positive: it is at least the desired diagonal
successor `n+3`, and it is smaller than the suffix's starting value. -/
theorem diagonal_longDescent_exposes_blocker {n : Nat}
    (hdiagonal : a (n + 2) = n + 2)
    (hpenultimate : CanSubtract (n + 1) (stateAt n)) :
    ∃ start length y fy,
      start + length = n + 2 ∧ 2 ≤ length ∧
      DescentRun start (a start) length ∧
      a start = n + 2 + descentDrop start length ∧
      y + 2 * start = a start ∧
      n + 3 ≤ y ∧ FirstAt a y fy ∧
      y < a start ∧ fy < start := by
  rcases diagonal_longDescent_has_maximalTail hdiagonal hpenultimate with
    ⟨start, length, hend, hlength, hstartPositive, hrun, hnot⟩
  have hendEquation := hrun.equation_at (i := length) (Nat.le_refl _)
  have hstartEquation :
      a start = n + 2 + descentDrop start length := by
    rw [hend] at hendEquation
    rw [hdiagonal] at hendEquation
    omega
  have hmul : 2 * start ≤ length * start :=
    Nat.mul_le_mul_right start hlength
  have htri : 3 ≤ upperTri length := by
    have := upperTri_mono hlength
    simpa using this
  cases start with
  | zero => omega
  | succ u =>
      have hnot' : ¬ CanSubtract (u + 1) (stateAt u) := by
        simpa using hnot
      have hadd := a_succ_of_not_canSubtract hnot'
      let y := a u - (u + 1)
      have hyLower : n + 3 ≤ y := by
        simp only [y]
        simp only [descentDrop] at hstartEquation
        omega
      have hpositive : u + 1 < a u := by
        simp only [y] at hyLower
        omega
      have hySeen : y ∈ valuesThrough u := by
        by_cases hseen : y ∈ valuesThrough u
        · exact hseen
        · have hcan : CanSubtract (u + 1) (stateAt u) := by
            constructor
            · simpa [a] using hpositive
            · change a u - (u + 1) ∉ valuesThrough u
              simpa only [y] using hseen
          exact False.elim (hnot' hcan)
      rcases history_member_has_firstAt hySeen with
        ⟨fy, hfyLe, hfirstY⟩
      have hyStart : y < a (u + 1) := by
        simp only [y]
        omega
      have hyExact : y + 2 * (u + 1) = a (u + 1) := by
        simp only [y]
        omega
      exact ⟨u + 1, length, y, fy, hend, hlength, hrun,
        hstartEquation, hyExact, hyLower, hfirstY, hyStart, by omega⟩

/-- Consequently the unresolved long-descent branch already provides a
concrete `CoverageStep` for target `n+3`, attached to the maximal suffix's
starting value. -/
theorem diagonal_longDescent_gives_coverageStep {n : Nat}
    (hdiagonal : a (n + 2) = n + 2)
    (hpenultimate : CanSubtract (n + 1) (stateAt n)) :
    ∃ start, CoverageStep (n + 3) (a start) start := by
  rcases diagonal_longDescent_exposes_blocker hdiagonal hpenultimate with
    ⟨start, length, y, fy, _, _, _, _, _,
      hyLower, hfirstY, hyStart, _⟩
  exact ⟨start, Or.inr ⟨y, fy, hyLower, hfirstY, hyStart⟩⟩

/-- Every positive diagonal endpoint therefore has an unconditional local
resolution: either its successor already occurs, or the maximal subtraction
suffix exposes a certified coverage step at its starting value. -/
theorem diagonal_successor_occurs_or_coverageStep {n : Nat}
    (hdiagonal : a (n + 2) = n + 2) :
    (∃ u, a u = n + 3) ∨
      ∃ start, CoverageStep (n + 3) (a start) start := by
  rcases diagonal_successor_occurs_or_longDescent hdiagonal with
    hoccurs | ⟨hpenultimate, _, _⟩
  · exact Or.inl hoccurs
  · exact Or.inr
      (diagonal_longDescent_gives_coverageStep hdiagonal hpenultimate)

/-- The same dichotomy stated in the coordinate-free form needed by a future
mixed time/value search: failure of immediate successor occurrence exposes a
value at least as large as the successor whose first occurrence is strictly
earlier than the diagonal endpoint. -/
theorem diagonal_successor_occurs_or_earlierBlocker {n : Nat}
    (hdiagonal : a (n + 2) = n + 2) :
    (∃ u, a u = n + 3) ∨
      ∃ y fy, n + 3 ≤ y ∧ FirstAt a y fy ∧ fy < n + 2 := by
  rcases diagonal_successor_occurs_or_longDescent hdiagonal with
    hoccurs | ⟨hpenultimate, _, _⟩
  · exact Or.inl hoccurs
  · rcases diagonal_longDescent_exposes_blocker
        hdiagonal hpenultimate with
      ⟨start, length, y, fy, hend, _, _, _, _,
        hyLower, hfirstY, _, hfyStart⟩
    exact Or.inr ⟨y, fy, hyLower, hfirstY, by omega⟩

/-- Hence the diagonal-successor property is reduced further to resolving
only diagonal endpoints whose two-step predecessor lies on `q=3,G=-1`. -/
def LongDiagonalDescentResolvable : Prop :=
  ∀ n, a (n + 2) = n + 2 →
    CoordinatesAt n 3 5 → ∃ u, a u = n + 3

theorem longDiagonalDescentResolvable_implies_diagonalSuccessor
    (hresolve : LongDiagonalDescentResolvable) :
    DiagonalSuccessorProperty := by
  intro t ht hdiagonal
  rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega : t ≠ 0)) with
    htone | httwo
  · have : t = 1 := by omega
    subst t
    exact ⟨4, by decide⟩
  · obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := by
      exact ⟨t - 2, by omega⟩
    rcases diagonal_successor_occurs_or_longDescent hdiagonal with
      hoccurs | ⟨_, hcoord, _⟩
    · exact hoccurs
    · exact hresolve n hdiagonal hcoord

end Recaman
