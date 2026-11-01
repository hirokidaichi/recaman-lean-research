import Recaman.EventualHighCorridorSupply
import Recaman.CoordinateDynamics

namespace Recaman

/-! # Recurrence pattern of a late corridor candidate

Inside an eventual high-candidate corridor, suppose some value `c` keeps
appearing as the subtraction candidate at arbitrarily late clocks.  Every
sufficiently late use clock `m` with `nextSubtractionCandidate m = c` is
then forced into a rigid three-step pattern:

* the step out of `m` is a forced addition, because subtracting would land
  on `c` and expose the truncated candidate `c - (m + 2) = 0`, violating
  the corridor high-candidate law;
* the step into `m` is a legal subtraction landing fresh on the diagonal
  value `c + m + 1`, because an addition into `m` would place the previous
  value `c + 1` below the corridor value law's floor;
* under a candidate floor `c ≤ nextSubtractionCandidate k` for all late
  `k`, the successor value `c + m` must already be recorded in history:
  otherwise the next clock would legally subtract to `c + m` and expose a
  candidate strictly below `c`.

The packaged event combines the three payloads.  A bounded-recurrence
extractor closes the file: if the candidate walk returns below a fixed
bound `K` at arbitrarily late clocks, then some single value `c ≤ K`
recurs as the candidate at arbitrarily late clocks.
-/

/-- **Use clocks are forced additions.**  Past the cutoff, a clock whose
subtraction candidate is a value `c ≤ m` cannot subtract: the landing value
`c` would present the truncated candidate `c - (m + 2) = 0` at the next
clock, contradicting the corridor high-candidate law. -/
theorem corridor_recurringCandidate_forcedAddition
    {target cutoff c m : Nat}
    (hhigh : ∀ k, cutoff ≤ k → target < nextSubtractionCandidate (k + 1))
    (hm : cutoff ≤ m)
    (hc : nextSubtractionCandidate m = c)
    (hlate : c ≤ m) :
    ¬ CanSubtract (m + 1) (stateAt m) := by
  intro hcan
  have hclock : m + 1 < a m := hcan.1
  have hstep := a_succ_of_canSubtract hcan
  have hnext := hhigh m hm
  simp only [nextSubtractionCandidate] at hc hnext
  omega

/-- **The step into a use clock is a legal subtraction landing fresh on the
diagonal.**  Two clocks past the cutoff, a use clock `m` of a late candidate
`c` (with `c + 1 ≤ m`) is entered by a legal subtraction: an addition into
`m` would force the previous value down to `c + 1`, below the corridor value
law's floor at clock `m - 1`.  The landing value is exactly the diagonal
value `c + m + 1`, and it is a first occurrence. -/
theorem corridor_recurringCandidate_entry_subtraction
    {target cutoff c m : Nat}
    (hhigh : ∀ k, cutoff ≤ k → target < nextSubtractionCandidate (k + 1))
    (hm : cutoff + 2 ≤ m)
    (hc : nextSubtractionCandidate m = c)
    (hlate : c + 1 ≤ m) :
    CanSubtract m (stateAt (m - 1)) ∧
      a m = c + m + 1 ∧
      FirstAt a (a m) m := by
  have hcut : cutoff < m := by omega
  have hlaw := corridor_value_law hhigh hcut
  have ham : a m = c + m + 1 := by
    simp only [nextSubtractionCandidate] at hc
    omega
  have hm1 : m - 1 + 1 = m := by omega
  by_cases hcan : CanSubtract (m - 1 + 1) (stateAt (m - 1))
  · have hfirst := firstAt_succ_of_canSubtract hcan
    rw [hm1] at hcan hfirst
    exact ⟨hcan, ham, hfirst⟩
  · have hstep := a_succ_of_not_canSubtract hcan
    rw [hm1] at hstep
    have hcut' : cutoff < m - 1 := by omega
    have hlaw' := corridor_value_law hhigh hcut'
    exact False.elim (by omega)

/-- **Successor demand.**  Under the candidate floor `c`, the value `c + m`
must already be in the history at time `m + 1`: the forced addition out of
the use clock `m` reaches `c + 2m + 2`, whose subtraction candidate is
`c + m`; were it fresh, the next clock would legally subtract onto it and
present the truncated candidate `c + m - (m + 3) < c`, breaking the floor. -/
theorem corridor_recurringCandidate_successor_seen
    {target cutoff c m M₁ : Nat}
    (hhigh : ∀ k, cutoff ≤ k → target < nextSubtractionCandidate (k + 1))
    (hfloor : ∀ k, M₁ ≤ k → c ≤ nextSubtractionCandidate k)
    (hm : cutoff ≤ m) (hM : M₁ ≤ m + 2)
    (hc : nextSubtractionCandidate m = c)
    (hlate : c ≤ m) (hcpos : 0 < c) :
    c + m ∈ valuesThrough (m + 1) := by
  have hforced := corridor_recurringCandidate_forcedAddition hhigh hm hc hlate
  have hstep := a_succ_of_not_canSubtract hforced
  have ham : a m = c + m + 1 := by
    simp only [nextSubtractionCandidate] at hc
    omega
  have ham1 : a (m + 1) = c + 2 * m + 2 := by omega
  by_cases hmem : c + m ∈ valuesThrough (m + 1)
  · exact hmem
  · have hcan2 : CanSubtract (m + 1 + 1) (stateAt (m + 1)) := by
      constructor
      · change m + 1 + 1 < a (m + 1)
        omega
      · change a (m + 1) - (m + 1 + 1) ∉ valuesThrough (m + 1)
        have hval : a (m + 1) - (m + 1 + 1) = c + m := by omega
        rw [hval]
        exact hmem
    have hstep2 := a_succ_of_canSubtract hcan2
    have hidx : m + 1 + 1 = m + 2 := by omega
    rw [hidx] at hstep2
    have hfl := hfloor (m + 2) hM
    simp only [nextSubtractionCandidate] at hfl
    exact False.elim (by omega)

/-- **Packaged use-clock event.**  A sufficiently late use clock of a
recurring corridor candidate `c` with floor `c` performs the full rigid
pattern: legal fresh subtraction into the diagonal value `c + m + 1`,
forced addition out to `c + 2m + 2`, and the successor value `c + m`
already recorded in history. -/
theorem corridor_recurringCandidate_event
    {target cutoff c m M₁ : Nat}
    (hhigh : ∀ k, cutoff ≤ k → target < nextSubtractionCandidate (k + 1))
    (hfloor : ∀ k, M₁ ≤ k → c ≤ nextSubtractionCandidate k)
    (hm : cutoff + 2 ≤ m) (hM : M₁ ≤ m + 2)
    (hc : nextSubtractionCandidate m = c)
    (hlate : c + 1 ≤ m) (hcpos : 0 < c) :
    CanSubtract m (stateAt (m - 1)) ∧
    FirstAt a (a m) m ∧
    a m = c + m + 1 ∧
    ¬ CanSubtract (m + 1) (stateAt m) ∧
    a (m + 1) = c + 2 * m + 2 ∧
    c + m ∈ valuesThrough (m + 1) := by
  have hentry := corridor_recurringCandidate_entry_subtraction hhigh hm hc hlate
  have hforced := corridor_recurringCandidate_forcedAddition hhigh
    (by omega) hc (by omega)
  have hseen := corridor_recurringCandidate_successor_seen hhigh hfloor
    (by omega) hM hc (by omega) hcpos
  have hstep := a_succ_of_not_canSubtract hforced
  have ham := hentry.2.1
  exact ⟨hentry.1, hentry.2.2, hentry.2.1, hforced, by omega, hseen⟩

/-- **Bounded-recurrence extractor.**  If the candidate walk drops to at
most `K` at arbitrarily late clocks, then some single value `c ≤ K` occurs
as the exact candidate at arbitrarily late clocks. -/
theorem corridor_candidate_bounded_recurrence
    {K : Nat}
    (hbounded : ∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m ≤ K) :
    ∃ c, c ≤ K ∧ ∀ M, ∃ m, M ≤ m ∧ nextSubtractionCandidate m = c := by
  classical
  revert hbounded
  induction K with
  | zero =>
      intro hbounded
      refine ⟨0, Nat.le_refl 0, ?_⟩
      intro M
      rcases hbounded M with ⟨m, hMm, hle⟩
      have hzero : nextSubtractionCandidate m = 0 := by omega
      exact ⟨m, hMm, hzero⟩
  | succ K ih =>
      intro hbounded
      by_cases hstop : ∃ N, ∀ m, N ≤ m → nextSubtractionCandidate m ≠ K + 1
      · rcases hstop with ⟨N, hN⟩
        have hbounded' : ∀ M, ∃ m, M ≤ m ∧
            nextSubtractionCandidate m ≤ K := by
          intro M
          rcases hbounded (max M N) with ⟨m, hm, hle⟩
          have hMm : M ≤ m := Nat.le_trans (Nat.le_max_left M N) hm
          have hNm : N ≤ m := Nat.le_trans (Nat.le_max_right M N) hm
          have hne := hN m hNm
          exact ⟨m, hMm, by omega⟩
        rcases ih hbounded' with ⟨c, hcK, hrec⟩
        exact ⟨c, Nat.le_succ_of_le hcK, hrec⟩
      · refine ⟨K + 1, Nat.le_refl _, ?_⟩
        intro M
        by_cases hexists : ∃ m, M ≤ m ∧
            nextSubtractionCandidate m = K + 1
        · exact hexists
        · exact False.elim
            (hstop ⟨M, fun m hm heq => hexists ⟨m, hm, heq⟩⟩)

end Recaman
