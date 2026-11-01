import Recaman.PermanentAboveCorridorPrefixSuccessorCoverage
import Recaman.BalancedTraceCertificate

namespace Recaman

noncomputable section

/-! # Balanced kernel pin of the clock-112 target

The balanced 4825-step trace already authenticates the complete visited-set
bitset.  This module checks, in the same boolean reduction that runs the
trace, that every value in `[153, 261]` except 223 has its bit set.  The
semantic `BitTraceMachine.Represents` invariant then turns the bit into an
ordinary Recamán occurrence, contradicting the replay's `target_missing`
field unless the target is 223.
-/

/-- An authenticated bit in a balanced trace checkpoint is an occurrence in
the ordinary Recamán history. -/
theorem BitTraceMachine.Represents.occurs_of_seenBit
    {machine : BitTraceMachine} {horizon value : Nat}
    (hrep : machine.Represents (stateAt horizon))
    (hseen : machine.seenBits.testBit value = true) :
    ∃ witness, a witness = value := by
  have hhistory : value ∈ valuesThrough horizon := by
    exact (hrep.seen_iff value).1 hseen
  rcases mem_valuesThrough_iff.mp hhistory with ⟨witness, _, hvalue⟩
  exact ⟨witness, hvalue⟩

/-- Boolean coverage query for the whole clock-112 target band.  Values
outside the band and the single candidate 223 are ignored. -/
def clock112TargetBandSeen (bits : Nat) : Bool :=
  (List.range 262).all fun value =>
    if 153 ≤ value ∧ value ≤ 261 ∧ value ≠ 223 then
      bits.testBit value
    else
      true

/-- Extract one target bit from the single finite-band boolean check. -/
theorem clock112TargetBandSeen_testBit
    {bits value : Nat}
    (hchecked : clock112TargetBandSeen bits = true)
    (hlow : 153 ≤ value) (hhigh : value ≤ 261) (hne : value ≠ 223) :
    bits.testBit value = true := by
  have hmember : value ∈ List.range 262 := List.mem_range.mpr (by omega)
  have hall := (List.all_eq_true.mp hchecked) value hmember
  simpa [clock112TargetBandSeen, hlow, hhigh, hne] using hall

/-- Run and validate the balanced trace once, then inspect its output bitset.
The trace data and the bitset are both untrusted inputs to this boolean
kernel computation. -/
def trace4825Clock112TargetBandVerified : Bool :=
  match trace4825Tree.runBits 20000 0 initialBitTraceMachine with
  | none => false
  | some output => clock112TargetBandSeen output.seenBits

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem trace4825Clock112TargetBand_checked :
    trace4825Clock112TargetBandVerified = true := by
  decide

set_option maxRecDepth 100000 in
/-- The successful boolean check exposes one authenticated output checkpoint
together with its checked band bitset. -/
theorem trace4825Clock112TargetBand_witness :
    ∃ output,
      trace4825Tree.runBits 20000 0 initialBitTraceMachine = some output ∧
      clock112TargetBandSeen output.seenBits = true := by
  have hchecked := trace4825Clock112TargetBand_checked
  unfold trace4825Clock112TargetBandVerified at hchecked
  generalize hrun : trace4825Tree.runBits 20000 0 initialBitTraceMachine =
    result at hchecked
  cases result with
  | none => simp at hchecked
  | some output =>
      exact ⟨output, rfl, hchecked⟩

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Unconditional balanced-trace closure of the clock-112 target band. -/
theorem target_eq_223_of_crossingTime_eq_112_balanced
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) :
    target = 223 := by
  have hpins := r.clock112_historical_downcross_pins hclock
  by_cases heq : target = 223
  · exact heq
  · have hlow : 153 ≤ target := by omega
    have hhigh : target ≤ 261 := hpins.2.2.2
    rcases trace4825Clock112TargetBand_witness with
      ⟨output, hrun, hband⟩
    have hrep := BalancedTrace.runBits_represents
      initialBitTraceMachine_represents hrun
    have hrep4825 : output.Represents (stateAt 4825) := by
      rw [trace4825Tree_length] at hrep
      simpa only [Nat.zero_add] using hrep
    have hseen := clock112TargetBandSeen_testBit hband hlow hhigh heq
    have hoccurs := hrep4825.occurs_of_seenBit hseen
    exact False.elim (r.target_missing hoccurs)

end TerminalExactDischargeReplayCertificate

end

end Recaman
