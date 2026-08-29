import Recaman.BalancedTraceCertificate
import Recaman.PermanentAboveClock112Obstruction

namespace Recaman

noncomputable section

/-!
# The first occurrence behind the clock-112 obstruction

The balanced certificate proves the orbit through clock 4825.  To prove a
`FirstAt`, rather than only the endpoint equality, we also authenticate the
4824-step checkpoint and inspect its authenticated bit for 371.  The final
step then supplies `a 4825 = 371`, while the bit invariant rules out every
earlier occurrence.

Empirically, the later value 19 at clock 99734 is the next much deeper
phenomenon.  It is deliberately not used by any theorem in this module.
-/

namespace BalancedTrace

/-- Retain a prefix of a balanced trace without flattening its leaves. -/
def takePrefix : Nat → BalancedTrace → BalancedTrace
  | count, .leaf codes => .leaf (codes.take count)
  | count, .node left right =>
      if count < left.length then
        left.takePrefix count
      else
        .node left (right.takePrefix (count - left.length))

/-- Check an endpoint value and a still-unseen bit in one kernel pass. -/
def verifiesBitsValueUnseen (tree : BalancedTrace) (capacity start : Nat)
    (machine : BitTraceMachine) (expected unseen : Nat) : Bool :=
  match tree.runBits capacity start machine with
  | none => false
  | some output =>
      (output.value == expected) &&
        (output.seenBits.testBit unseen == false)

theorem verifiesBitsValueUnseen_witness {tree : BalancedTrace}
    {capacity start expected unseen : Nat} {machine : BitTraceMachine}
    (hverify : tree.verifiesBitsValueUnseen capacity start machine
      expected unseen = true) :
    ∃ output,
      tree.runBits capacity start machine = some output ∧
      output.value = expected ∧
      output.seenBits.testBit unseen = false := by
  unfold verifiesBitsValueUnseen at hverify
  generalize hrun : tree.runBits capacity start machine = result at hverify
  cases result with
  | none => simp at hverify
  | some output =>
      have hparts := Bool.and_eq_true_iff.mp hverify
      refine ⟨output, rfl, ?_, ?_⟩
      · simpa using hparts.1
      · simpa using hparts.2

end BalancedTrace

/-- The authenticated state immediately before the first 371. -/
def trace4824Tree : BalancedTrace := trace4825Tree.takePrefix 4824

theorem trace4824Tree_length : trace4824Tree.length = 4824 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem trace4824Bits_value_unseen_371 :
    trace4824Tree.verifiesBitsValueUnseen 20000 0
      initialBitTraceMachine 5196 371 = true := by
  decide

/-- 371 is created for the first time at clock 4825. -/
theorem firstAt_371_4825 : FirstAt a 371 4825 := by
  rcases BalancedTrace.verifiesBitsValueUnseen_witness
      trace4824Bits_value_unseen_371 with
    ⟨output, hrun, _, hunseen⟩
  have hrep := BalancedTrace.runBits_represents
    initialBitTraceMachine_represents hrun
  rw [trace4824Tree_length] at hrep
  refine ⟨balanced_a_4825, ?_⟩
  intro witness hwitness hvalue
  have hmem : 371 ∈ valuesThrough 4824 := by
    apply mem_valuesThrough_iff.mpr
    exact ⟨witness, by omega, hvalue⟩
  have hseen : output.seenBits.testBit 371 = true :=
    (hrep.seen_iff 371).2 hmem
  rw [hunseen] at hseen
  exact Bool.false_ne_true hseen

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The replay's abstract first occurrence is the concrete certified clock. -/
theorem historicalMinimumTime_eq_4825_of_crossingTime_eq_112
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) :
    source.historicalMinimumTime = 4825 := by
  have hobstruction := r.clock112_firstOccurrenceObstruction hclock
  exact hobstruction.minimum_first.unique firstAt_371_4825

/-- Low-value witnesses at or after the certified minimum clock are
impossible. This isolates the remaining global contradiction to one future
low-witness obligation. -/
theorem no_low_witness_at_or_after_4825_of_crossingTime_eq_112
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) (witness : Nat)
    (hwitness : 4825 ≤ witness) (hlow : a witness ≤ target) : False := by
  have hminimumTime :=
    r.historicalMinimumTime_eq_4825_of_crossingTime_eq_112 hclock
  have htailStart : source.tailStart ≤ 4825 := by
    have hstart := source.historical_minimum.minimum.start_le_time
    omega
  have habove := source.historical_tail.strictly_above witness
    (Nat.le_trans htailStart hwitness)
  omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
