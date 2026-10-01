import Recaman.TerminalASharpWords

open Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.TerminalASharpWords

namespace TerminalASharpControls

local instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

-- The general Nat-subtracted expression is not a substitute for small words.
example : ¬ P2 (body 0 (pairCount 0)) ∧ ¬ P2 (body 1 (pairCount 1)) ∧
    ¬ P2 (body 2 (pairCount 2)) := by decide
example : P2 (word 0) ∧ P2 (word 1) ∧ P2 (word 2) := by decide

-- First large-family case: same length as q=2, different SS count and tail.
example : pairCount 3 = 1 ∧ (word 3).length = 11 ∧
    ssCount (word 3) = 3 ∧ ((word 3).reverse.takeWhile id).length = 2 := by decide
example : word 2 ≠ word 3 ∧ ((word 2).reverse.takeWhile id).length = 1 := by decide

-- Complete proper mass-one positions and their exact nonzero moments.
example : (List.range 11).filter (fun j => decide (mass ((word 3).take j) = 1)) =
    [1, 5, 7] := by decide
example : ([1, 5, 7] : List Nat).map (fun j => moment ((word 3).take j)) =
    [1, -3, -4] := by decide

-- P2 fails without the prescribed insertion count even when mass/SS/tail fit.
example : mass (body 3 0) = 1 ∧ moment (body 3 0) = 1 ∧
    ssCount (body 3 0) = 3 ∧ ((body 3 0).reverse.takeWhile id).length = 2 := by decide
example : ¬ P2 (body 3 0) := by decide

-- Overlapping counting must include both adjacent pairs in SSS.
example : ssCount [false, false, false] = 2 := by decide

end TerminalASharpControls
