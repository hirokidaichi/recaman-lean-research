import Recaman.FirstP2EndingS

open Recaman.LeadingRunSupply Recaman.FirstP2EndingS

namespace FirstP2SemanticControls

local instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

def nonminimal : List Bool := [true, true, false, true, false, false, true]
def ceilingThree : List Bool :=
  [true, true, true, false, false, false, true, false, true, false, true]

-- Removing minimality permits a P2 word ending A even under ceiling two.
example : P2 nonminimal ∧ P2 (nonminimal.take 3) := by decide
example : ((List.range 8).all fun j => decide (mass (nonminimal.take j) ≤ 2)) = true := by
  decide
example : ¬ ∃ u, nonminimal = u ++ [false] := by
  intro ⟨u, hu⟩
  have hr := congrArg List.reverse hu
  simp [nonminimal] at hr

-- Raising the ceiling to three permits a minimal P2 word ending A.
example : P2 ceilingThree := by decide
example : ((List.range 11).all fun j => decide (j = 0 ∨ ¬ P2 (ceilingThree.take j))) = true := by
  decide
example : mass (ceilingThree.take 3) = 3 := by decide
example : ¬ ∃ u, ceilingThree = u ++ [false] := by
  intro ⟨u, hu⟩
  have hr := congrArg List.reverse hu
  simp [ceilingThree] at hr

-- Existence must not be inferred for an empty or mass-only word.
example : ¬ P2 ([] : List Bool) ∧ ¬ P2 [true] ∧
    ¬ P2 [true, false, false, true] := by decide

-- The nonminimal word's first P2 still ends S, as the corollary says.
example : ∃ j, 0 < j ∧ j ≤ nonminimal.length ∧ P2 (nonminimal.take j) ∧
    (∀ k, 0 < k → k < j → ¬ P2 (nonminimal.take k)) ∧
    ∃ u, nonminimal.take j = u ++ [false] := by
  apply first_p2_prefix_ends_S
  · intro j hj
    have hc : ((List.range 8).all fun k => decide (mass (nonminimal.take k) ≤ 2)) = true := by
      decide
    have hmem : j ∈ List.range 8 := by simp [nonminimal] at hj; simp; omega
    exact of_decide_eq_true (List.all_eq_true.mp hc j hmem)
  · exact ⟨3, by omega, by decide, by decide⟩

end FirstP2SemanticControls
