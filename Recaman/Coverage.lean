import Recaman.TargetDescent

namespace Recaman

/-- For target m, every larger first-occurring value admits a triangular
descent equation aimed exactly at m.  This is now the isolated arithmetic
condition needed by the blocker induction. -/
def TargetResolvable (m : Nat) : Prop :=
  ∀ v f, FirstAt a v f → m < v →
    ∃ k, TargetEquation f v m k

/-- One admissible global-proof step: either `m` has already been witnessed,
or we obtain a strictly smaller value together with one of its first
occurrences.  Value decrease alone is the exact condition needed by the
strong induction below; blocker constructions often prove the stronger time
decrease as additional information. -/
def CoverageStep (m v _f : Nat) : Prop :=
  (∃ t, a t = m) ∨
    ∃ y fy, m ≤ y ∧ FirstAt a y fy ∧ y < v

/-- The flexible proof obligation left to future local mechanisms.  Unlike
TargetResolvable, this can be discharged by direct descent, an exact gate, a
local escape, or another certified construction. -/
def CoverageOracle (m : Nat) : Prop :=
  ∀ v f, FirstAt a v f → m ≤ v → CoverageStep m v f

/-- A coverage step can be transported to any strictly larger parent value.
The parent time is irrelevant because the global recursion is on values. -/
theorem CoverageStep.mono_parent {m v f V F : Nat}
    (hstep : CoverageStep m v f) (hbelow : v < V) :
    CoverageStep m V F := by
  rcases hstep with hoccurs | ⟨y, fy, hmy, hfirstY, hyv⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨y, fy, hmy, hfirstY, Nat.lt_trans hyv hbelow⟩

/-- A step aimed at a higher intermediate target `M` also resolves every
smaller target `m`, provided `M` itself is below the parent value. -/
theorem CoverageStep.lower_target {m M v f : Nat}
    (hstep : CoverageStep M v f) (hmM : m ≤ M) (hMv : M < v) :
    CoverageStep m v f := by
  rcases hstep with hoccurs | ⟨y, fy, hMy, hfirstY, hyv⟩
  · rcases Nat.eq_or_lt_of_le hmM with heq | hmMlt
    · subst M
      exact Or.inl hoccurs
    · rcases exists_firstAt hoccurs with ⟨fM, hfirstM⟩
      exact Or.inr ⟨M, fM, hmM, hfirstM, hMv⟩
  · exact Or.inr
      ⟨y, fy, Nat.le_trans hmM hMy, hfirstY, hyv⟩

/-- Above every bound m, the real Recamán orbit has an actually occurring
value, and hence a first-occurring value.  No global unboundedness theorem is
needed: inspect a_m, then force addition at step m+1 if necessary. -/
theorem exists_firstAbove (m : Nat) :
    ∃ v f, m < v ∧ FirstAt a v f := by
  by_cases habove : m < a m
  · rcases history_member_has_firstAt (current_mem_valuesThrough m) with
      ⟨f, _, hfirst⟩
    exact ⟨a m, f, habove, hfirst⟩
  · have hnonpositive : ¬ m + 1 < (stateAt m).value := by
      simpa [a] using (show ¬ m + 1 < a m by omega)
    have hstep := step_of_nonpositive
      (n := m + 1) (state := stateAt m) hnonpositive
    have hnext : a (m + 1) = a m + (m + 1) := by
      have hvalue := congrArg State.value hstep
      simpa [a, stateAt] using hvalue
    have hnextAbove : m < a (m + 1) := by omega
    rcases history_member_has_firstAt
      (current_mem_valuesThrough (m + 1)) with ⟨f, _, hfirst⟩
    exact ⟨a (m + 1), f, hnextAbove, hfirst⟩

/-- Well-founded target descent from any larger first-occurring value.
Every blocker recursively replaces v by a strictly smaller value y while
preserving m ≤ y; equality already witnesses the target. -/
theorem targetResolvable_reaches_from {m : Nat}
    (hm : 0 < m) (hresolve : TargetResolvable m)
    {v f : Nat} (hfirst : FirstAt a v f) (hmv : m < v) :
    ∃ t, a t = m := by
  induction v using Nat.strongRecOn generalizing f with
  | ind v ih =>
      rcases hresolve v f hfirst hmv with ⟨k, hequation⟩
      rcases targetDescent_lands_or_doubleDescent
        hfirst hm hequation with hlanding |
          ⟨length, y, fy, hbefore, hmle, hylt, hfirstY, hfy⟩
      · exact ⟨f + k, hlanding⟩
      · rcases Nat.eq_or_lt_of_le hmle with heq | hmy
        · subst y
          exact ⟨fy, hfirstY.1⟩
        · exact ih y hylt hfirstY hmy

/-- The generic well-founded induction behind the research program. -/
theorem coverageOracle_reaches_from {m v f : Nat}
    (horacle : CoverageOracle m)
    (hfirst : FirstAt a v f) (hmv : m ≤ v) :
    ∃ t, a t = m := by
  induction v using Nat.strongRecOn generalizing f with
  | ind v ih =>
      rcases horacle v f hfirst hmv with hdone |
        ⟨y, fy, hmy, hfirstY, hylt⟩
      · exact hdone
      · exact ih y hylt hfirstY hmy

theorem coverageOracle_implies_occurs {m : Nat}
    (horacle : CoverageOracle m) : ∃ t, a t = m := by
  rcases exists_firstAbove m with ⟨v, f, hmv, hfirst⟩
  exact coverageOracle_reaches_from horacle hfirst (Nat.le_of_lt hmv)

/-- Direct target resolvability is one, deliberately strong, way to construct
the more flexible coverage oracle. -/
theorem targetResolvable_implies_coverageOracle {m : Nat}
    (hm : 0 < m) (hresolve : TargetResolvable m) : CoverageOracle m := by
  intro v f hfirst hmv
  rcases Nat.eq_or_lt_of_le hmv with heq | hstrict
  · subst v
    exact Or.inl ⟨f, hfirst.1⟩
  · rcases hresolve v f hfirst hstrict with ⟨k, hequation⟩
    rcases targetDescent_lands_or_doubleDescent
      hfirst hm hequation with hlanding |
        ⟨length, y, fy, _, hmle, hylt, hfirstY, hfy⟩
    · exact Or.inl ⟨f + k, hlanding⟩
    · exact Or.inr ⟨y, fy, hmle, hfirstY, hylt⟩

/-- Conditional coverage theorem for one target: TargetResolvable m is
sufficient for m to occur in the Recamán sequence. -/
theorem targetResolvable_implies_occurs {m : Nat}
    (hm : 0 < m) (hresolve : TargetResolvable m) :
    ∃ t, a t = m := by
  rcases exists_firstAbove m with ⟨v, f, hmv, hfirst⟩
  exact targetResolvable_reaches_from hm hresolve hfirst hmv

/-- A single arithmetic resolution hypothesis for all positive targets would
therefore imply the full nonnegative-integer coverage conjecture. -/
theorem all_targetResolvable_implies_surjective
    (hresolve : ∀ m, 0 < m → TargetResolvable m) :
    ∀ m, ∃ t, a t = m := by
  intro m
  cases m with
  | zero => exact ⟨0, rfl⟩
  | succ m =>
      exact targetResolvable_implies_occurs (by omega)
        (hresolve (m + 1) (by omega))

/-- The final global theorem schema: constructing a coverage oracle for each
positive target is enough to prove the Recamán coverage conjecture. -/
theorem all_coverageOracles_imply_surjective
    (horacle : ∀ m, 0 < m → CoverageOracle m) :
    ∀ m, ∃ t, a t = m := by
  intro m
  cases m with
  | zero => exact ⟨0, rfl⟩
  | succ m =>
      exact coverageOracle_implies_occurs
        (horacle (m + 1) (by omega))

end Recaman
