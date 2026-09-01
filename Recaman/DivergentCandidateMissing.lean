import Recaman.EventualHighCorridorSecondMissing
import Recaman.EventualHighCorridorDichotomy

namespace Recaman

/-! # Divergent candidates force an unbounded missing set

The branch-A dichotomy leaves a divergence residual: past some clock every
subtraction candidate exceeds any prescribed bound.  This file shows the
residual alone — with no corridor value law and no tail certificate —
forces the set of permanently missing values to be unbounded.

Given a bound `B`, instantiate divergence at `B + 2` to obtain a clock `N`
past which every candidate clears `B + 2`; unfolding the candidate turns
this into the value law `a m > K + m + 1` for all `m ≥ N`.  Counting the
stored history at time `N` (exactly `N + 1` values) against the window
`(B, N + B + 3]` (its `N + 3` values) leaves some windowed value `u`
unvisited at time `N`.  The value law then freezes `u` out forever: every
later orbit value clears the whole window, so `u` is permanently missing
and lies strictly above `B`.

Honesty note: the divergence residual is a hypothesis about the
hypothetical branch-A orbit, not the observed one — the real orbit keeps
producing low candidates.  The theorem's content is that the divergence
escape route pays an unbounded missing set, complementing the
second-missing theorem on the recurrence side of the dichotomy.
-/

/-- **Candidate floor forces a missing value above any bound.**  If past
clock `N` every subtraction candidate exceeds `K ≥ B + 2`, then some value
strictly above `B` is never visited by the orbit at any time.  The window
`(B, N + B + 3]` outnumbers the time-`N` history, and the candidate floor
freezes its unvisited member out of the entire future. -/
theorem candidateFloor_forces_missing_above
    {K N B : Nat}
    (hfloor : ∀ m, N ≤ m → K < nextSubtractionCandidate m)
    (hK : B + 2 ≤ K) :
    ∃ u, B < u ∧ ∀ time, a time ≠ u := by
  classical
  have hlaw : ∀ m, N ≤ m → K + m + 1 < a m := by
    intro m hm
    have h := hfloor m hm
    simp only [nextSubtractionCandidate] at h
    omega
  have hfresh : ∃ u, B < u ∧ u ≤ N + B + 3 ∧ u ∉ valuesThrough N := by
    by_cases hexists : ∃ u, B < u ∧ u ≤ N + B + 3 ∧
        u ∉ valuesThrough N
    · exact hexists
    · exfalso
      have hall : ∀ u, B < u → u ≤ N + B + 3 →
          u ∈ valuesThrough N := by
        intro u hu1 hu2
        by_cases hmem : u ∈ valuesThrough N
        · exact hmem
        · exact False.elim (hexists ⟨u, hu1, hu2, hmem⟩)
      have hsubset : List.range (N + B + 4) ⊆
          List.range (B + 1) ++ valuesThrough N := by
        intro u hu
        rw [List.mem_range] at hu
        rw [List.mem_append]
        by_cases hle : u ≤ B
        · exact Or.inl (List.mem_range.mpr (by omega))
        · exact Or.inr (hall u (by omega) (by omega))
      have hlength := List.nodup_range.length_le_of_subset hsubset
      simp only [List.length_range, List.length_append,
        valuesThrough_length] at hlength
      omega
  rcases hfresh with ⟨u, habove, hwindow, hfreshMem⟩
  refine ⟨u, habove, ?_⟩
  intro time hvisit
  by_cases htime : time ≤ N
  · exact hfreshMem (mem_valuesThrough_iff.mpr ⟨time, htime, hvisit⟩)
  · have hlate := hlaw time (by omega)
    omega

/-- **Divergent candidates leave unbounded missing values.**  If the
subtraction-candidate walk diverges, then above every bound some value is
permanently missing from the orbit. -/
theorem divergent_candidates_missing_unbounded
    (hdiv : ∀ K, ∃ N, ∀ m, N ≤ m → K < nextSubtractionCandidate m) :
    ∀ B, ∃ u, B < u ∧ ∀ time, a time ≠ u := by
  intro B
  rcases hdiv (B + 2) with ⟨N, hfloor⟩
  exact candidateFloor_forces_missing_above hfloor (Nat.le_refl (B + 2))

/-- **Capstone: unbounded missing values or a rigid event stream.**  In an
eventual high-candidate corridor, either permanently missing values occur
above every bound, or some value `c` strictly above the missing target has
arbitrarily late use clocks each performing the complete rigid pattern.
The divergent branch of the corridor dichotomy is upgraded from a bare
candidate limit to an unbounded missing set, so both branches now carry a
structural price. -/
theorem EventualHighCandidateTail.missingUnbounded_or_rigidEventStream
    {target tailStart : Nat}
    (hcorridor : EventualHighCandidateTail target tailStart) :
    (∀ B, ∃ u, B < u ∧ ∀ time, a time ≠ u) ∨
      ∃ c, target < c ∧
        ∀ M, ∃ m, M ≤ m ∧
          nextSubtractionCandidate m = c ∧
          CanSubtract m (stateAt (m - 1)) ∧
          FirstAt a (a m) m ∧
          a m = c + m + 1 ∧
          ¬ CanSubtract (m + 1) (stateAt m) ∧
          a (m + 1) = c + 2 * m + 2 ∧
          c + m ∈ valuesThrough (m + 1) := by
  rcases hcorridor.diverges_or_rigidEventStream with hdiv | hstream
  · exact Or.inl (divergent_candidates_missing_unbounded hdiv)
  · exact Or.inr hstream

end Recaman
