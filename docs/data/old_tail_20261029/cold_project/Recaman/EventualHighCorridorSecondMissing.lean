import Recaman.EventualHighCorridorSupply
import Recaman.TargetTailResidualKernel

namespace Recaman

/-! # A second missing value inside an eventual high corridor

An eventual high-candidate corridor over a missing permanent tail forces a
second permanently missing value strictly above the target.

The counting step is free: the stored history through time `cutoff + 1`
holds exactly `cutoff + 2` values, so among the `cutoff + target + 3`
numbers bounded by the window `cutoff + target + 2` some non-target value
is absent from that history.  Any finite history misses such a value in a
sufficiently wide window, with no corridor hypothesis at all.

The non-free step is exactly the corridor value law: strictly past the
cutoff every orbit value exceeds `target` plus its own clock, hence clears
the entire window, so the fresh windowed value is never visited later
either.  Finally, every value below the target already lies in the
pre-tail history by the permanent-tail certificate, so the fresh value
sits strictly above the target: the missing target is not the only
permanently missing value.
-/

/-- The stored history through time `n` lists exactly `n + 1` values,
multiplicities included. -/
theorem valuesThrough_length (n : Nat) :
    (valuesThrough n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [valuesThrough_succ, List.length_cons, ih]

/-- **Second missing value.**  A missing permanent tail equipped with an
eventual high-candidate corridor leaves a further value, strictly above the
target, that the orbit never visits at any time. -/
theorem EventualHighCandidateTail.exists_second_missing
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hcorridor : EventualHighCandidateTail target tailStart) :
    ∃ u, target < u ∧ ∀ time, a time ≠ u := by
  classical
  rcases hcorridor with ⟨cutoff, htailLe, hhigh⟩
  have hfresh : ∃ u, u ≤ cutoff + target + 2 ∧ u ≠ target ∧
      u ∉ valuesThrough (cutoff + 1) := by
    by_cases hexists : ∃ u, u ≤ cutoff + target + 2 ∧ u ≠ target ∧
        u ∉ valuesThrough (cutoff + 1)
    · exact hexists
    · exfalso
      have hall : ∀ u, u ≤ cutoff + target + 2 → u ≠ target →
          u ∈ valuesThrough (cutoff + 1) := by
        intro u hu hne
        by_cases hmem : u ∈ valuesThrough (cutoff + 1)
        · exact hmem
        · exact False.elim (hexists ⟨u, hu, hne, hmem⟩)
      have hsubset : List.range (cutoff + target + 3) ⊆
          target :: valuesThrough (cutoff + 1) := by
        intro u hu
        rw [List.mem_range] at hu
        by_cases hne : u = target
        · exact List.mem_cons.mpr (Or.inl hne)
        · exact List.mem_cons.mpr (Or.inr (hall u (by omega) hne))
      have hlength := List.nodup_range.length_le_of_subset hsubset
      rw [List.length_range, List.length_cons, valuesThrough_length]
        at hlength
      have hpositive := htail.target_positive
      omega
  rcases hfresh with ⟨u, hwindow, hne, hfreshMem⟩
  have habove : target < u := by
    by_cases hbelow : u < target
    · exfalso
      have hcovered := htail.below_covered u hbelow
      rcases mem_valuesThrough_iff.mp hcovered with ⟨t, ht, hvalue⟩
      exact hfreshMem
        (mem_valuesThrough_iff.mpr ⟨t, by omega, hvalue⟩)
    · omega
  refine ⟨u, habove, ?_⟩
  intro time hvisit
  by_cases htime : time ≤ cutoff + 1
  · exact hfreshMem
      (mem_valuesThrough_iff.mpr ⟨time, htime, hvisit⟩)
  · have hlaw := corridor_value_law hhigh
      (show cutoff < time by omega)
    omega

/-- Negated-existential packaging of the second missing value, matching the
shape of the `target_missing` field. -/
theorem EventualHighCandidateTail.missing_not_unique
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hcorridor : EventualHighCandidateTail target tailStart) :
    ∃ u, target < u ∧ ¬ ∃ time, a time = u := by
  rcases hcorridor.exists_second_missing htail with ⟨u, habove, hnever⟩
  exact ⟨u, habove, fun ⟨time, hvisit⟩ => hnever time hvisit⟩

end Recaman
