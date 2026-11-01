import Recaman.PermanentAboveCorridorLeastMissingSummit

namespace Recaman

noncomputable section

/-! # Nineteen as the first concrete boundary

Every value below nineteen occurs in the kernel-range orbit, so nineteen is
a least missing target exactly when nineteen itself never occurs.  The
summit floor said no counterexample below nineteen exists; this module
pins the first genuinely open instance: whether the orbit reaches
nineteen.  Empirically it does, at time 99734, but that clock lies far
beyond kernel range, so the statement stays an honest open boundary rather
than a theorem.

Consequently the fixed-point branch of the summit splits on this single
value: if nineteen occurs, any least missing target terminating in a fixed
point is at least twenty; if nineteen never occurs, nineteen itself is the
least missing target.  The first unverified instance guarding the floor is
one concrete orbit value.
-/

/-- Nineteen is a least missing target exactly when it never occurs: all
smaller values occur within kernel range. -/
theorem leastMissingTarget_nineteen_iff :
    LeastMissingTarget 19 ↔ ¬ ∃ time, a time = 19 := by
  constructor
  · intro h
    exact h.target_missing
  · intro hmissing
    refine ⟨hmissing, ?_⟩
    intro value hvalue
    have hcases : value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
        value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7 ∨ value = 8 ∨
        value = 9 ∨ value = 10 ∨ value = 11 ∨ value = 12 ∨ value = 13 ∨
        value = 14 ∨ value = 15 ∨ value = 16 ∨ value = 17 ∨
        value = 18 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨131, by set_option maxRecDepth 100000 in decide⟩
    · exact ⟨129, by set_option maxRecDepth 100000 in decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨5, by decide⟩
    · exact ⟨16, by decide⟩
    · exact ⟨14, by decide⟩
    · exact ⟨12, by decide⟩
    · exact ⟨10, by decide⟩
    · exact ⟨8, by decide⟩
    · exact ⟨6, by decide⟩
    · exact ⟨31, by set_option maxRecDepth 100000 in decide⟩
    · exact ⟨29, by set_option maxRecDepth 100000 in decide⟩
    · exact ⟨27, by set_option maxRecDepth 100000 in decide⟩
    · exact ⟨25, by set_option maxRecDepth 100000 in decide⟩
    · exact ⟨23, by set_option maxRecDepth 100000 in decide⟩

/-- If nineteen occurs, the fixed-point branch of the summit sharpens to a
target of at least twenty: the exceptional target nineteen would then be
present in the orbit, contradicting its own missing-target field. -/
theorem LeastMissingTarget.semantic_or_twenty_le_of_nineteen_occurs
    {target : Nat}
    (hocc : ∃ time, a time = 19)
    (h : LeastMissingTarget target) :
    (∃ stepParent child : PhaseSearchNode,
      PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child stepParent) ∨ 20 ≤ target := by
  rcases h.semantic_or_flooredCore with hsemantic | hfixed
  · exact Or.inl hsemantic
  · rcases hfixed with ⟨_, _, _, _, hnineteen⟩
    right
    by_cases heq : target = 19
    · subst heq
      exact absurd hocc h.target_missing
    · omega

end

end Recaman
