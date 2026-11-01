import Recaman.DeepSixtyoneTraceCertificate
import Recaman.BalancedTraceSuffix

namespace Recaman

noncomputable section

/-!
# Least absent value at the authenticated clock-181653 endpoint

The deep trace already checks the entire Recamán history through the late
landing at 61.  This companion certificate asks the same authenticated
endpoint bitset for its mex.  It proves in one pass that every value below
879 has occurred by clock 181653, while 879 has not.
-/

namespace GeneratedBalancedTrace181653

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem traceBits_mex879_checked :
    traceTree.verifiesBitsMex traceCapacity 0
      initialBitTraceMachine 879 = true := by
  decide

/-- At clock 181653 the actual history contains every value below 879 and
does not contain 879 itself. -/
theorem generated_mex879 :
    (∀ value, value < 879 → value ∈ valuesThrough 181653) ∧
      879 ∉ valuesThrough 181653 := by
  have hmex := BalancedTrace.verified_bits_mex
    initialBitTraceMachine_represents traceBits_mex879_checked
  rw [traceTree_length] at hmex
  have htime : 0 + traceSteps = 181653 := by rfl
  rw [htime] at hmex
  exact hmex

end GeneratedBalancedTrace181653

end

end Recaman
