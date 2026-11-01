import Recaman.TargetCombTimeAncestry
import Recaman.OrbitBounds
import Recaman.ActualDescent
import Std

namespace Recaman

/-! # A finite ceiling for pre-tail ancestry obstructions

Time-only ancestry can leave a first occurrence in the finite pre-tail
prefix.  Its value is not merely drawn from a finite set: the universal
orbit bound gives the explicit ceiling `upperTri tailStart`.  Consequently
an active anchor above that ceiling eliminates the residual branch of
`FirstAt.preTail_anchorObstruction_or_normalProgress` outright.
-/

/-- The existential pre-tail-root obstruction collapses to one numeric
inequality on the active anchor. -/
theorem FirstAt.ceilingObstruction_or_normalProgress
    {target tailStart horizon anchor value firstTime : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htarget : target < value)
    (hanchor : anchor ≤ value)
    (hfirst : FirstAt a value firstTime)
    (hhorizon : firstTime < horizon) :
    anchor ≤ upperTri tailStart ∨
    ∃ child childFirstTime,
      target < child ∧
      child < anchor ∧
      FirstAt a child childFirstTime ∧
      childFirstTime < firstTime ∧
      DebtInvariant target
        ⟨horizon, anchor, .debt, childFirstTime⟩ child childFirstTime ∧
      PhaseSearchProgress target
        ⟨horizon, child, .normal, child⟩
        ⟨horizon, anchor, .debt, firstTime⟩ := by
  rcases hfirst.preTail_anchorObstruction_or_normalProgress
      htail htarget hanchor hhorizon with
    ⟨root, rootFirstTime, _hrootTarget, hrootAnchor,
      hrootFirst, hrootTime⟩ | hprogress
  · exact Or.inl (Nat.le_trans hrootAnchor
      (hrootFirst.value_le_upperTri_of_time_le hrootTime))
  · exact Or.inr hprogress

/-! ## One-use blockers eventually clear every fixed ceiling -/

/-- Among `B + 2` completed combs with pairwise distinct final times, at
least one terminal blocker is greater than `B`.  This is the finite
pigeonhole form of the fact that an infinite stream of completed combs has
unbounded blocker values. -/
theorem HistoryTerminatedComb.exists_blocker_gt_of_many
    {B : Nat}
    {s k blocker : Fin (B + 2) → Nat}
    (hcomb : ∀ i, HistoryTerminatedComb (s i) (k i) (blocker i))
    (hfinal : Function.Injective (fun i => s i + 2 * k i)) :
    ∃ i, B < blocker i := by
  classical
  by_cases hexists : ∃ i, B < blocker i
  · exact hexists
  have hnone : ∀ i, blocker i ≤ B := by
    intro i
    exact Nat.le_of_not_gt (fun hlt => hexists ⟨i, hlt⟩)
  have hblockerInjective : Function.Injective blocker := by
    intro i j heq
    have hj : HistoryTerminatedComb (s j) (k j) (blocker i) := by
      simpa [heq] using hcomb j
    exact hfinal ((hcomb i).same_blocker_finalTime_eq hj)
  have nodup_of_injective :
      ∀ {n : Nat} (f : Fin n → Nat), Function.Injective f →
        (List.ofFn f).Nodup := by
    intro n
    induction n with
    | zero =>
        intro f _
        simp only [List.ofFn_zero, List.nodup_nil]
    | succ n ih =>
        intro f hf
        rw [List.ofFn_succ, List.nodup_cons]
        constructor
        · intro hmem
          rw [List.mem_ofFn] at hmem
          rcases hmem with ⟨i, hi⟩
          have heq : i.succ = (0 : Fin (n + 1)) := hf hi
          have hval := congrArg Fin.val heq
          simp at hval
        · apply ih
          intro i j hij
          have heq : i.succ = j.succ := hf hij
          exact Fin.succ_inj.mp heq
  have hnodup : (List.ofFn blocker).Nodup :=
    nodup_of_injective blocker hblockerInjective
  have hsubset : List.ofFn blocker ⊆ List.range (B + 1) := by
    intro value hvalue
    rw [List.mem_ofFn] at hvalue
    rcases hvalue with ⟨i, rfl⟩
    rw [List.mem_range]
    exact Nat.lt_succ_of_le (hnone i)
  have hlength := hnodup.length_le_of_subset hsubset
  simp only [List.length_ofFn, List.length_range] at hlength
  exact False.elim (by omega)

end Recaman
