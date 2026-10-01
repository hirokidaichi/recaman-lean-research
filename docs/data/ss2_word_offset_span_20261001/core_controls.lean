import Recaman.OneSSMultiplicity

open Recaman.LeadingRunSupply Recaman.OneSSMultiplicity

namespace SS2SpanCoreControls

def core : List Bool :=
  [false, true, true, true, false, false, true, true, true, false, false]

example : mass core = 1 ∧ moment core = 0 ∧ ssCount core = 2 := by decide
example : (List.range 12).filter (fun j => decide (mass (core.take j) = 1)) =
    [3, 5, 7, 11] := by decide
example : ([3, 5, 7, 11] : List Nat).map (fun j => moment (core.take j)) =
    [4, 3, 4, 0] := by decide
example : ((List.range 13).all fun j => decide
    (((true :: core).drop j).take 4 ≠ [false, true, true, false])) = true := by decide
example : core.head? = some false ∧ core.reverse.head? = some false := by decide

end SS2SpanCoreControls
