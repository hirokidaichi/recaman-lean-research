import Recaman.OrbitCombWitness

namespace Recaman

/-! # Value-set representation of a comb run

The history gained over a comb run is exactly the two rails.  Membership at
the run exit therefore splits into the pre-run history, the ascending high
rail, and the descending low rail — and both rails live in explicit
arithmetic ranges determined by the entry value.  As a consequence a value
strictly below the final low rail that is fresh at the run entry stays
fresh through the whole run.  This is the freshness-transport mechanism
compressed orbit verification needs: comb segments cannot silently consume
the deep stragglers guarding the fixed-point floor.
-/

/-- History membership at a comb-run exit: the pre-run history plus the two
rails. -/
theorem CombRun.mem_valuesThrough_iff
    {s x : Nat} :
    ∀ {k : Nat}, CombRun s k →
      (x ∈ valuesThrough (s + 2 * k) ↔
        x ∈ valuesThrough s ∨
          (∃ i, i < k ∧ x = a (s + 2 * i + 1)) ∨
          (∃ i, i < k ∧ x = a (s + 2 * i + 2))) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro h
      have hrun : CombRun s k := h.mono (by omega)
      have hprev := ih hrun
      have hstep : valuesThrough (s + 2 * (k + 1)) =
          a (s + 2 * k + 2) :: a (s + 2 * k + 1) ::
            valuesThrough (s + 2 * k) := by
        have h1 : s + 2 * (k + 1) = s + 2 * k + 1 + 1 := by omega
        rw [h1, valuesThrough_succ, valuesThrough_succ]
      rw [hstep]
      constructor
      · intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem2
        · exact Or.inr (Or.inr ⟨k, Nat.lt_succ_self k, heq⟩)
        · rcases List.mem_cons.mp hmem2 with heq | hmem3
          · exact Or.inr (Or.inl ⟨k, Nat.lt_succ_self k, heq⟩)
          · rcases hprev.mp hmem3 with hbase | hhigh | hlow
            · exact Or.inl hbase
            · rcases hhigh with ⟨i, hik, hx⟩
              exact Or.inr (Or.inl ⟨i, by omega, hx⟩)
            · rcases hlow with ⟨i, hik, hx⟩
              exact Or.inr (Or.inr ⟨i, by omega, hx⟩)
      · intro hcases
        rcases hcases with hbase | hhigh | hlow
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
            (Or.inr (hprev.mpr (Or.inl hbase)))))
        · rcases hhigh with ⟨i, hik, hx⟩
          by_cases hik' : i < k
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
              (Or.inr (hprev.mpr (Or.inr (Or.inl ⟨i, hik', hx⟩))))))
          · have hieq : i = k := by omega
            subst hieq
            exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
              (Or.inl hx)))
        · rcases hlow with ⟨i, hik, hx⟩
          by_cases hik' : i < k
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
              (Or.inr (hprev.mpr (Or.inr (Or.inr ⟨i, hik', hx⟩))))))
          · have hieq : i = k := by omega
            subst hieq
            exact List.mem_cons.mpr (Or.inl hx)

/-- Freshness transport: a value strictly below the final low rail which is
fresh at the run entry stays fresh through the whole run. -/
theorem CombRun.fresh_below_transport
    {s k x : Nat} (h : CombRun s k)
    (hbelow : x + k < a s)
    (hnotin : x ∉ valuesThrough s) :
    x ∉ valuesThrough (s + 2 * k) := by
  intro hmem
  rcases h.mem_valuesThrough_iff.mp hmem with hbase | hhigh | hlow
  · exact hnotin hbase
  · rcases hhigh with ⟨i, hik, hx⟩
    have hrail := h.high_rail i hik
    omega
  · rcases hlow with ⟨i, hik, hx⟩
    have hrail := h.low_rail (i + 1) (by omega)
    have harith : s + 2 * (i + 1) = s + 2 * i + 2 := by omega
    rw [harith] at hrail
    omega

end Recaman
