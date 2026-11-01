import Recaman.DeepSixtyoneTraceCertificate
import Recaman.BalancedTraceSuffix

namespace Recaman

noncomputable section

/-!
# Recovering the nearby value 76 from the authenticated 61 trace

The 181,653-step certificate already authenticates every preceding branch.
Its rightmost leaf begins at clock 181,633.  Splitting that leaf after eleven
steps and reversing the remaining ten value updates recovers the checkpoint
`a 181643 = 76` without checking a second 181,643-step trace.
-/

namespace GeneratedBalancedTrace181653

set_option maxRecDepth 100000

def lastLeafFront : List Nat :=
  [67, 0, 61, 0, 55, 0, 49, 0, 35, 0, 0]

def lastTenCodes : List Nat :=
  [1, 79, 181644, 0, 0, 95, 0, 101, 0, 0]

theorem lastBlock_split :
    traceBlock2838 = lastLeafFront ++ lastTenCodes := by
  rfl

theorem rightmostCodes_eq_lastBlock :
    traceTree.rightmostCodes = traceBlock2838 := by
  rfl

/-- Any split of the rightmost block exposes a represented intermediate
checkpoint and the successful remaining suffix. -/
theorem rightmostSplitCheckpoint {front back : List Nat}
    (hsplit : traceBlock2838 = front ++ back) :
    ∃ (middle output : BitTraceMachine),
      middle.Represents (stateAt (181632 + front.length)) ∧
      runCheckedBitTraceBlock traceCapacity
        (181632 + 1 + front.length) middle back = some output ∧
      output.value = 61 := by
  rcases BalancedTrace.verifiesBitsValue_witness traceBits_checked with
    ⟨output, hrun, houtput⟩
  rcases traceTree.runBits_rightmostCheckpoint
      initialBitTraceMachine_represents hrun with
    ⟨leafStart, checkpoint, htime, hcheckpointRep, hleaf⟩
  rw [rightmostCodes_eq_lastBlock] at htime hleaf
  have hlastLength : traceBlock2838.length = 21 := by decide
  have hleafStart : leafStart = 181632 := by
    rw [hlastLength, traceTree_length] at htime
    simp [traceSteps] at htime
    omega
  subst leafStart
  rw [hsplit] at hleaf
  rcases runCheckedBitTraceBlock_append_witness hleaf with
    ⟨middle, hfront, hsuffix⟩
  have hmiddleRep := runCheckedBitTraceBlock_represents
    hcheckpointRep hfront
  rw [← stateAt_add_eq_runRecamanSteps 181632 front.length] at hmiddleRep
  exact ⟨middle, output, hmiddleRep, hsuffix, houtput⟩

/-- Reversing the final ten authenticated value updates determines the input
checkpoint value uniquely.  Seen-set details are needed for validity but not
for this reverse arithmetic. -/
theorem lastTen_input_value {machine output : BitTraceMachine}
    (hrun : runCheckedBitTraceBlock traceCapacity 181644 machine
      lastTenCodes = some output)
    (houtput : output.value = 61) :
    machine.value = 76 := by
  have hreplay := runCheckedBitTraceBlock_eq_replay hrun
  have hvalue := congrArg BitTraceMachine.value hreplay
  simp [lastTenCodes, replayBitTraceBlock, applyBitTraceReason,
    BitTraceMachine.record, decodeTraceReason] at hvalue
  omega

/-- The already-checked deep trace contains the clock-181643 value 76. -/
theorem generated_value_seventysix : a 181643 = 76 := by
  rcases BalancedTrace.verifiesBitsValue_witness traceBits_checked with
    ⟨output, hrun, houtput⟩
  rcases traceTree.runBits_rightmostCheckpoint
      initialBitTraceMachine_represents hrun with
    ⟨leafStart, checkpoint, htime, hcheckpointRep, hleaf⟩
  rw [rightmostCodes_eq_lastBlock] at htime hleaf
  have hlastLength : traceBlock2838.length = 21 := by decide
  have hleafStart : leafStart = 181632 := by
    rw [hlastLength, traceTree_length] at htime
    simp [traceSteps] at htime
    omega
  subst leafStart
  rw [lastBlock_split] at hleaf
  rcases runCheckedBitTraceBlock_append_witness hleaf with
    ⟨middle, hfront, hsuffix⟩
  have hfrontLength : lastLeafFront.length = 11 := by decide
  rw [hfrontLength] at hsuffix
  have hmiddleValue : middle.value = 76 := by
    apply lastTen_input_value hsuffix
    exact houtput
  have hmiddleRep := runCheckedBitTraceBlock_represents
    hcheckpointRep hfront
  rw [hfrontLength] at hmiddleRep
  rw [← stateAt_add_eq_runRecamanSteps 181632 11] at hmiddleRep
  have htimeEq : 181632 + 11 = 181643 := by omega
  rw [htimeEq] at hmiddleRep
  unfold a
  exact hmiddleRep.value_eq.symm.trans hmiddleValue

def lastLeafFrontNineteen : List Nat :=
  [67, 0, 61, 0, 55, 0, 49, 0, 35, 0, 0, 1, 79, 181644, 0, 0,
    95, 0, 101]

def lastTwoCodes : List Nat := [0, 0]

theorem lastBlock_split_nineteen :
    traceBlock2838 = lastLeafFrontNineteen ++ lastTwoCodes := by
  rfl

theorem lastTwo_input_value {machine output : BitTraceMachine}
    (hrun : runCheckedBitTraceBlock traceCapacity 181652 machine
      lastTwoCodes = some output)
    (houtput : output.value = 61) :
    machine.value = 363366 := by
  have hreplay := runCheckedBitTraceBlock_eq_replay hrun
  have hvalue := congrArg BitTraceMachine.value hreplay
  simp [lastTwoCodes, replayBitTraceBlock, applyBitTraceReason,
    BitTraceMachine.record, decodeTraceReason] at hvalue
  omega

/-- The value two clocks before the deep 61 landing. -/
theorem generated_value_181651 : a 181651 = 363366 := by
  rcases rightmostSplitCheckpoint lastBlock_split_nineteen with
    ⟨middle, output, hmiddleRep, hsuffix, houtput⟩
  have hfrontLength : lastLeafFrontNineteen.length = 19 := by decide
  rw [hfrontLength] at hmiddleRep hsuffix
  have hmiddleValue := lastTwo_input_value hsuffix houtput
  have htimeEq : 181632 + 19 = 181651 := by omega
  rw [htimeEq] at hmiddleRep
  unfold a
  exact hmiddleRep.value_eq.symm.trans hmiddleValue

def lastLeafFrontTwenty : List Nat :=
  [67, 0, 61, 0, 55, 0, 49, 0, 35, 0, 0, 1, 79, 181644, 0, 0,
    95, 0, 101, 0]

def lastOneCode : List Nat := [0]

theorem lastBlock_split_twenty :
    traceBlock2838 = lastLeafFrontTwenty ++ lastOneCode := by
  rfl

theorem lastOne_input_value {machine output : BitTraceMachine}
    (hrun : runCheckedBitTraceBlock traceCapacity 181653 machine
      lastOneCode = some output)
    (houtput : output.value = 61) :
    machine.value = 181714 := by
  have hreplay := runCheckedBitTraceBlock_eq_replay hrun
  have hvalue := congrArg BitTraceMachine.value hreplay
  simp [lastOneCode, replayBitTraceBlock, applyBitTraceReason,
    BitTraceMachine.record, decodeTraceReason] at hvalue
  omega

/-- The immediate predecessor of the deep 61 landing. -/
theorem generated_value_181652 : a 181652 = 181714 := by
  rcases rightmostSplitCheckpoint lastBlock_split_twenty with
    ⟨middle, output, hmiddleRep, hsuffix, houtput⟩
  have hfrontLength : lastLeafFrontTwenty.length = 20 := by decide
  rw [hfrontLength] at hmiddleRep hsuffix
  have hmiddleValue := lastOne_input_value hsuffix houtput
  have htimeEq : 181632 + 20 = 181652 := by omega
  rw [htimeEq] at hmiddleRep
  unfold a
  exact hmiddleRep.value_eq.symm.trans hmiddleValue

/-- The transition immediately before the deep 61 landing's incoming high
is itself a legal subtraction. -/
theorem generated_previous_subtraction :
    CanSubtract 181652 (stateAt 181651) := by
  by_cases hcan : CanSubtract 181652 (stateAt 181651)
  · exact hcan
  · have hadd := recurrence 181651
    simp only [hcan, ↓reduceIte] at hadd
    rw [generated_value_181652, generated_value_181651] at hadd
    omega

end GeneratedBalancedTrace181653

end

end Recaman
