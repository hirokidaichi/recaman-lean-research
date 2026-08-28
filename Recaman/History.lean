import Recaman.Basic
import Recaman.Blocker

namespace Recaman

@[simp] theorem valuesThrough_succ (n : Nat) :
    valuesThrough (n + 1) = a (n + 1) :: valuesThrough n := by
  rfl

/-- Membership in the stored history is exactly occurrence at some earlier
or equal index of the actual Recamán sequence. -/
theorem mem_valuesThrough_iff {x n : Nat} :
    x ∈ valuesThrough n ↔ ∃ t, t ≤ n ∧ a t = x := by
  induction n with
  | zero =>
      constructor
      · intro hmem
        simp [valuesThrough, stateAt, initial] at hmem
        exact ⟨0, Nat.le_refl 0, hmem.symm⟩
      · rintro ⟨t, ht, hvalue⟩
        have ht0 : t = 0 := by omega
        subst t
        simpa [valuesThrough, stateAt, initial, a] using hvalue.symm
  | succ n ih =>
      constructor
      · intro hmem
        rw [valuesThrough_succ] at hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hnow | holdmem
        · exact ⟨n + 1, Nat.le_refl _, hnow.symm⟩
        · rcases ih.mp holdmem with ⟨t, ht, hvalue⟩
          exact ⟨t, Nat.le_trans ht (Nat.le_succ n), hvalue⟩
      · rintro ⟨t, ht, hvalue⟩
        rw [valuesThrough_succ]
        simp only [List.mem_cons]
        rcases Nat.eq_or_lt_of_le ht with heq | hlt
        · exact Or.inl (by simpa [heq] using hvalue.symm)
        · apply Or.inr
          apply ih.mpr
          exact ⟨t, Nat.le_of_lt_succ hlt, hvalue⟩

/-- The actual sequence has seen x before step n+1 exactly when x is in the
history stored at time n. -/
theorem seenBefore_succ_iff {x n : Nat} :
    SeenBefore a x (n + 1) ↔ x ∈ valuesThrough n := by
  constructor
  · rintro ⟨t, ht, hvalue⟩
    apply mem_valuesThrough_iff.mpr
    exact ⟨t, Nat.le_of_lt_succ ht, hvalue⟩
  · intro hmem
    rcases mem_valuesThrough_iff.mp hmem with ⟨t, ht, hvalue⟩
    exact ⟨t, Nat.lt_succ_of_le ht, hvalue⟩

/-- A value occurring by n has a first occurrence no later than n. -/
theorem exists_firstAt_bounded (seq : Nat → Nat) (n : Nat) :
    ∀ x, (∃ t, t ≤ n ∧ seq t = x) →
      ∃ f, f ≤ n ∧ FirstAt seq x f := by
  classical
  induction n with
  | zero =>
      intro x hexists
      rcases hexists with ⟨t, ht, hvalue⟩
      have ht0 : t = 0 := by omega
      subst t
      refine ⟨0, Nat.le_refl 0, hvalue, ?_⟩
      intro u hu
      omega
  | succ n ih =>
      intro x hexists
      by_cases hearlier : ∃ t, t ≤ n ∧ seq t = x
      · rcases ih x hearlier with ⟨f, hf, hfirst⟩
        exact ⟨f, Nat.le_trans hf (Nat.le_succ n), hfirst⟩
      · rcases hexists with ⟨t, ht, hvalue⟩
        have ht_eq : t = n + 1 := by
          have hnot_le : ¬ t ≤ n := by
            intro ht_le
            exact hearlier ⟨t, ht_le, hvalue⟩
          omega
        subst t
        refine ⟨n + 1, Nat.le_refl _, hvalue, ?_⟩
        intro u hu hux
        exact hearlier ⟨u, Nat.le_of_lt_succ hu, hux⟩

/-- Every value that occurs has a first occurrence. -/
theorem exists_firstAt {seq : Nat → Nat} {x : Nat}
    (hexists : ∃ t, seq t = x) : ∃ f, FirstAt seq x f := by
  rcases hexists with ⟨t, hvalue⟩
  rcases exists_firstAt_bounded seq t x
    ⟨t, Nat.le_refl t, hvalue⟩ with ⟨f, _, hfirst⟩
  exact ⟨f, hfirst⟩

/-- A stored history member therefore has an actual first occurrence no later
than the current time. -/
theorem history_member_has_firstAt {x n : Nat}
    (hmem : x ∈ valuesThrough n) :
    ∃ f, f ≤ n ∧ FirstAt a x f := by
  exact exists_firstAt_bounded a n x (mem_valuesThrough_iff.mp hmem)

end Recaman
