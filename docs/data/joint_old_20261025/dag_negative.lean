import Recaman.FourEventProof
open Recaman.FourEventProof Recaman.FourNonsuppliedData
-- Expected failures: A11 cannot be certified, and initial real successors cannot be omitted.
example : goodState ⟨[],11,19,4⟩=true := by decide
example : successors ⟨[],0,0,0⟩=[] := by decide
