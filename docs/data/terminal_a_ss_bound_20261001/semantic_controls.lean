import Recaman.TerminalASSBound

open Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.TerminalASSBound

namespace TerminalASSBoundControls

local instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

def nonminimal : List Bool := [true, true, false, true, false, false, true]
def sharpTwo : List Bool :=
  [true, true, true, false, false, false, true, false, true, false, true]

-- t>0 is indispensable for strictness when q=0.
example : P2 [true, true, false] ∧ ssCount [true, true, false] = 0 ∧
    (([true, true, false] : List Bool).reverse.takeWhile id).length = 0 := by decide

-- P2 alone can attain t=q=1; dropping minimality from strictness is false.
example : P2 nonminimal ∧ P2 (nonminimal.take 3) ∧ ssCount nonminimal = 1 ∧
    (nonminimal.reverse.takeWhile id).length = 1 := by decide

-- Mass or moment alone does not give the truncated minimal bound.
example : moment [true, false, false, true] = 0 ∧
    mass [true, false, false, true] = 0 := by decide
example : mass [true] = 1 ∧ moment [true] = 1 ∧ ssCount [true] = 0 := by decide

-- q=2,t=1 is genuinely allowed; its ceiling is three, not two.
example : P2 sharpTwo ∧ ssCount sharpTwo = 2 ∧
    (sharpTwo.reverse.takeWhile id).length = 1 ∧ mass (sharpTwo.take 3) = 3 := by decide

example : ∃ u t, sharpTwo = (u ++ [false]) ++ List.replicate t true ∧
    (sharpTwo.reverse.takeWhile id).length = t ∧ t ≤ ssCount sharpTwo - 1 := by
  apply minimal_p2_terminal_bound _ (by decide)
  intro j hj hlen
  have hc : ((List.range 11).all fun k => decide (k = 0 ∨ ¬ P2 (sharpTwo.take k))) = true := by
    decide
  have hmem : j ∈ List.range 11 := by simp [sharpTwo] at hlen; simp; omega
  have hx := of_decide_eq_true (List.all_eq_true.mp hc j hmem)
  exact hx.resolve_left (by omega)

end TerminalASSBoundControls
