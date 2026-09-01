import Recaman.EventualHighCorridorStructure

namespace Recaman

/-! # Supply chain of the eventual high-candidate corridor

Inside an eventual high-candidate corridor every forced addition is blocked
by history: its candidate is a previously seen value.  This module tracks
where that supplier value can live.

First, the corridor value law places every strictly-post-cutoff orbit value
strictly above the missing target plus its own clock.  Second, the corridor
keeps producing forced additions forever: a perpetual subtraction ray past
the cutoff would drop the value by at least two per step, while the value
law keeps it nonnegative, which is impossible.  Third, once a forced
addition's candidate exceeds the pre-cutoff value hull `upperTri cutoff`,
its supplier must be a corridor-internal landing, and that landing itself
obeys the corridor value law: the infinite corridor is a self-fueling
closed system apart from a finite seed.  A clock-relative refinement pushes
the supplier past any prescribed time bound whenever the candidate clears
the corresponding hull.
-/

/-- **Corridor value law.**  Strictly past the cutoff, every orbit value
sits strictly above the missing target plus the next clock. -/
theorem corridor_value_law
    {target cutoff n : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff < n) :
    target + (n + 1) < a n := by
  have h := hhigh (n - 1) (by omega)
  have heq : n - 1 + 1 = n := by omega
  rw [heq] at h
  simp only [nextSubtractionCandidate] at h
  omega

/-- **Corridor forced-addition recurrence.**  The corridor produces forced
additions beyond every bound: a perpetual run of legal subtractions past the
cutoff would drop the value by at least two per step, while the corridor
value law keeps every post-cutoff value strictly positive. -/
theorem corridor_infinitely_many_forcedAdditions
    {target cutoff : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1)) :
    ∀ M, ∃ n, M ≤ n ∧ ¬ CanSubtract (n + 1) (stateAt n) := by
  classical
  intro M
  by_cases hresult : ∃ n, M ≤ n ∧ ¬ CanSubtract (n + 1) (stateAt n)
  · exact hresult
  · exfalso
    have hall : ∀ n, M ≤ n → CanSubtract (n + 1) (stateAt n) := by
      intro n hn
      by_cases hcan : CanSubtract (n + 1) (stateAt n)
      · exact hcan
      · exact False.elim (hresult ⟨n, hn, hcan⟩)
    obtain ⟨N, hN⟩ : ∃ N, N = M + cutoff + 2 := ⟨_, rfl⟩
    have hdrop : ∀ k, a (N + k) + 2 * k ≤ a N := by
      intro k
      induction k with
      | zero =>
          show a N + 2 * 0 ≤ a N
          omega
      | succ k ih =>
          have hstep := a_succ_of_canSubtract (hall (N + k) (by omega))
          have hval := corridor_value_law hhigh (show cutoff < N + k by omega)
          show a (N + k + 1) + 2 * (k + 1) ≤ a N
          omega
    have hvalN := corridor_value_law hhigh (show cutoff < N by omega)
    have hfinal := hdrop (a N)
    omega

/-- **Corridor supplier window.**  A forced addition strictly inside the
corridor whose candidate clears the pre-cutoff value hull must be supplied
by a corridor-internal landing: some strictly-post-cutoff time `t` carries
exactly the candidate value, that value obeys the corridor value law at `t`,
and it is bounded by the hull at `t`. -/
theorem corridor_forcedAddition_supplier
    {target cutoff n : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff + 1 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbig : upperTri cutoff < nextSubtractionCandidate n) :
    ∃ t, cutoff < t ∧ t ≤ n ∧
      a t = nextSubtractionCandidate n ∧
      t + 1 + target < nextSubtractionCandidate n ∧
      nextSubtractionCandidate n ≤ upperTri t := by
  classical
  have hseen := corridor_forcedAddition_candidate_seen hhigh hn hnot
  rcases mem_valuesThrough_iff.mp hseen with ⟨t, htn, hval⟩
  have hbound := a_le_upperTri t
  have htcut : cutoff < t := by
    by_cases hle : t ≤ cutoff
    · exfalso
      have hmono := upperTri_mono hle
      omega
    · omega
  have hlaw := corridor_value_law hhigh htcut
  exact ⟨t, htcut, htn, hval, by omega, by omega⟩

/-- **Late corridor suppliers, packaged.**  An eventual high-candidate
corridor supplies a cutoff past which every forced addition whose candidate
clears the pre-cutoff hull is fueled from inside the corridor itself. -/
theorem EventualHighCandidateTail.late_forcedAdditions_are_self_fueled
    {target tailStart : Nat}
    (hcorridor : EventualHighCandidateTail target tailStart) :
    ∃ cutoff, tailStart ≤ cutoff ∧
      ∀ n, cutoff + 1 ≤ n →
        ¬ CanSubtract (n + 1) (stateAt n) →
        upperTri cutoff < nextSubtractionCandidate n →
        ∃ t, cutoff < t ∧ t ≤ n ∧
          a t = nextSubtractionCandidate n ∧
          t + 1 + target < nextSubtractionCandidate n ∧
          nextSubtractionCandidate n ≤ upperTri t := by
  rcases hcorridor with ⟨cutoff, htail, hhigh⟩
  exact ⟨cutoff, htail, fun n hn hnot hbig =>
    corridor_forcedAddition_supplier hhigh hn hnot hbig⟩

/-- **Supplier clock lower bound.**  Whenever a corridor forced addition's
candidate clears the value hull at `max cutoff T`, its supplier must sit
strictly past `T` as well: hull monotonicity leaves no room for an earlier
supplier. -/
theorem corridor_supplier_clock_lower_bound
    {target cutoff n T : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff + 1 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbig : upperTri (max cutoff T) < nextSubtractionCandidate n) :
    ∃ t, T < t ∧ cutoff < t ∧ t ≤ n ∧ a t = nextSubtractionCandidate n ∧
      t + 1 + target < nextSubtractionCandidate n := by
  classical
  have hcutmax : upperTri cutoff ≤ upperTri (max cutoff T) :=
    upperTri_mono (Nat.le_max_left cutoff T)
  have hbigcut : upperTri cutoff < nextSubtractionCandidate n := by omega
  rcases corridor_forcedAddition_supplier hhigh hn hnot hbigcut with
    ⟨t, htcut, htn, hval, htarget, hupper⟩
  have hTt : T < t := by
    by_cases hle : t ≤ max cutoff T
    · exfalso
      have hmono := upperTri_mono hle
      omega
    · have hmaxT := Nat.le_max_right cutoff T
      omega
  exact ⟨t, hTt, htcut, htn, hval, htarget⟩

end Recaman
