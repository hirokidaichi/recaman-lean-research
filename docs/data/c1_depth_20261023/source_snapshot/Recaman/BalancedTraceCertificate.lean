import Recaman.ChunkedTraceCertificate

namespace Recaman

/-!
# Balanced trace certificates

`checkTraceChunk` is intentionally simple, but a single large `List` asks the
kernel to reduce a deeply nested term.  This module keeps leaves short and
sequences them through a balanced tree.  Each successful leaf returns its
authenticated `TraceMachine` checkpoint exactly once, so checking the right
subtree neither replays nor rechecks the left subtree.

The numeric encoding used by the generated data is untrusted:

* `0` means `fresh`;
* `1` means `nonpositive`;
* `witnessTime + 2` means `blocked witnessTime`.

Soundness still passes through `ValidTraceStep` and
`TraceMachine.Represents`; no result depends on trusting the generator.
-/

/-- Decode the compact, external representation of one branch reason. -/
def decodeTraceReason : Nat → TraceStepReason
  | 0 => .fresh
  | 1 => .nonpositive
  | witnessTime + 2 => .blocked witnessTime

/-- Check a fixed-size leaf in one pass, returning its authenticated endpoint.
Unlike a separate boolean check followed by replay, successful prefixes are
not reduced twice. -/
def runCheckedTraceBlock : Nat → TraceMachine → List Nat → Option TraceMachine
  | _, machine, [] => some machine
  | clock, machine, code :: codes =>
      let reason := decodeTraceReason code
      if ValidTraceStep clock machine reason then
        runCheckedTraceBlock (clock + 1)
          (applyTraceReason clock machine reason) codes
      else
        none

/-- A sequencing tree whose leaves are deliberately small certificate blocks. -/
inductive BalancedTrace where
  | leaf (codes : List Nat)
  | node (left right : BalancedTrace)

namespace BalancedTrace

def length : BalancedTrace → Nat
  | .leaf codes => codes.length
  | .node left right => left.length + right.length

/-- Run the left child once and pass its checked checkpoint to the right. -/
def run : Nat → TraceMachine → BalancedTrace → Option TraceMachine
  | start, machine, .leaf codes =>
      runCheckedTraceBlock (start + 1) machine codes
  | start, machine, .node left right =>
      match left.run start machine with
      | none => none
      | some checkpoint => right.run (start + left.length) checkpoint

theorem runCheckedTraceBlock_represents {clock : Nat}
    {machine output : TraceMachine} {state : State} {codes : List Nat}
    (hrep : machine.Represents state)
    (hrun : runCheckedTraceBlock clock machine codes = some output) :
    output.Represents (runRecamanSteps clock state codes.length) := by
  induction codes generalizing clock machine state with
  | nil =>
      simp only [runCheckedTraceBlock, Option.some.injEq] at hrun
      subst output
      simpa [runRecamanSteps] using hrep
  | cons code codes ih =>
      simp only [runCheckedTraceBlock] at hrun
      split at hrun
      · rename_i hvalid
        have hnext := applyTraceReason_represents_step hrep hvalid
        simpa [runRecamanSteps] using ih hnext hrun
      · simp at hrun

/-- A successful balanced run is an ordinary Recamán prefix.  This is the
checkpoint theorem used at every internal node. -/
theorem run_represents {start : Nat} {machine output : TraceMachine}
    {tree : BalancedTrace}
    (hrep : machine.Represents (stateAt start))
    (hrun : tree.run start machine = some output) :
    output.Represents (stateAt (start + tree.length)) := by
  induction tree generalizing start machine output with
  | leaf codes =>
      have hout := runCheckedTraceBlock_represents hrep hrun
      rw [← stateAt_add_eq_runRecamanSteps] at hout
      exact hout
  | node left right ihLeft ihRight =>
      simp only [run] at hrun
      generalize hcheckpoint : left.run start machine = checkpoint at hrun
      cases checkpoint with
      | none => simp at hrun
      | some checkpoint =>
          have hleft := ihLeft hrep hcheckpoint
          have hright := ihRight hleft hrun
          simpa [length, Nat.add_assoc] using hright

/-- Check validity and the expected endpoint in the same reduction pass. -/
def verifiesValue (tree : BalancedTrace) (start : Nat)
    (machine : TraceMachine) (expected : Nat) : Bool :=
  match tree.run start machine with
  | none => false
  | some output => output.value == expected

theorem verifiesValue_witness {tree : BalancedTrace} {start expected : Nat}
    {machine : TraceMachine}
    (hverify : tree.verifiesValue start machine expected = true) :
    ∃ output, tree.run start machine = some output ∧ output.value = expected := by
  unfold verifiesValue at hverify
  generalize hrun : tree.run start machine = result at hverify
  cases result with
  | none => simp at hverify
  | some output =>
      refine ⟨output, rfl, ?_⟩
      simpa using hverify

/-- Kernel-checked endpoint extraction from a balanced certificate. -/
theorem verified_value {tree : BalancedTrace} {start expected : Nat}
    {machine : TraceMachine}
    (hrep : machine.Represents (stateAt start))
    (hverify : tree.verifiesValue start machine expected = true) :
    a (start + tree.length) = expected := by
  rcases verifiesValue_witness hverify with ⟨output, hrun, hvalue⟩
  have hout := run_represents hrep hrun
  unfold a
  rw [← hout.value_eq, hvalue]

end BalancedTrace


/-! ## A 1024-step kernel certificate

Sixteen 64-step leaves keep list reduction shallow; the four-level tree keeps
checkpoint composition shallow as well. -/

def trace1024Block00 : List Nat :=
  [1, 1, 1, 0, 1, 3, 5, 0, 4, 0, 1, 0, 1, 0, 1, 0, 1, 7, 17, 0, 11, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 8, 32, 0, 22, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace1024Block01 : List Nat :=
  [1, 19, 65, 0, 59, 0, 53, 0, 47, 0, 37, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 23, 100, 0, 94, 0, 68, 0, 74, 0, 0, 0, 1, 40, 112, 105, 0, 111, 0, 0, 0, 27, 0, 33, 0, 12, 0, 18, 0]

def trace1024Block02 : List Nat :=
  [0, 1, 0, 1, 4, 128, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 38, 171, 0, 165, 0, 159, 0, 153, 0, 147, 0, 141, 0, 0, 47, 0, 37, 103, 184, 0, 0]

def trace1024Block03 : List Nat :=
  [0, 23, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 34, 135, 0, 189, 0, 107, 0, 125, 0, 195, 0, 0, 25, 0, 31, 0, 10, 0, 16, 0, 5, 0, 4, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace1024Block04 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 77, 286, 0, 280, 0, 274, 0, 268, 0, 262, 0, 256, 0, 250, 0, 228, 0, 234, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace1024Block05 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 102, 262, 0, 256, 0, 250, 0, 228, 0, 234, 0, 308, 0, 0, 140, 0, 146, 0, 152, 0, 158, 0, 164, 0, 170, 0, 36, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace1024Block06 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 67, 119, 0, 230, 0, 236, 0, 386, 0, 356, 0, 362, 0, 368, 0, 0, 212, 0, 218, 0, 224, 0, 30, 0, 24, 0, 42, 0, 48, 0, 54, 0, 60, 0, 66, 0, 15, 0, 9, 0, 27, 0, 33, 0]

def trace1024Block07 : List Nat :=
  [12, 0, 18, 174, 451, 0, 445, 0, 439, 0, 409, 0, 415, 0, 421, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 136, 509, 0]

def trace1024Block08 : List Nat :=
  [451, 0, 445, 0, 439, 0, 409, 0, 415, 0, 421, 0, 467, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace1024Block09 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace1024Block10 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 173, 675, 0, 669, 0, 663, 0, 657, 0, 651, 0, 645, 0, 639, 0, 633, 0, 627, 0, 621, 0, 615, 0, 609, 0, 603, 0, 597, 0]

def trace1024Block11 : List Nat :=
  [591, 0, 585, 0, 511, 0, 453, 0, 447, 0, 441, 0, 407, 0, 413, 0, 419, 0, 469, 0, 531, 0, 0, 90, 0, 72, 0, 78, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 122, 471, 0, 533, 0, 743, 0, 733, 0, 0, 172, 0, 0]

def trace1024Block12 : List Nat :=
  [1, 0, 1, 369, 767, 0, 0, 385, 0, 391, 0, 397, 0, 403, 0, 65, 0, 59, 0, 53, 0, 47, 0, 37, 0, 79, 0, 85, 0, 91, 0, 97, 0, 23, 0, 198, 0, 204, 0, 210, 0, 216, 0, 222, 0, 32, 0, 22, 0, 40, 0, 46, 0, 52, 0, 58, 0, 64, 0, 17, 0, 11, 0, 25]

def trace1024Block13 : List Nat :=
  [0, 31, 0, 10, 0, 16, 0, 5, 0, 4, 0, 1, 367, 844, 0, 838, 0, 832, 0, 826, 0, 820, 0, 814, 0, 808, 0, 802, 0, 796, 0, 790, 0, 784, 0, 774, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace1024Block14 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace1024Block15 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 235, 984, 0, 978, 0, 972, 0, 966, 0, 960, 0, 954, 0, 948, 0, 842, 0, 836, 0, 830, 0, 824, 0, 818, 0, 812, 0, 806, 0, 800, 0, 794, 0, 788, 0, 782, 0, 776, 0, 758]

def trace1024Tree : BalancedTrace :=
  .node (.node (.node (.node (.leaf trace1024Block00) (.leaf trace1024Block01)) (.node (.leaf trace1024Block02) (.leaf trace1024Block03))) (.node (.node (.leaf trace1024Block04) (.leaf trace1024Block05)) (.node (.leaf trace1024Block06) (.leaf trace1024Block07)))) (.node (.node (.node (.leaf trace1024Block08) (.leaf trace1024Block09)) (.node (.leaf trace1024Block10) (.leaf trace1024Block11))) (.node (.node (.leaf trace1024Block12) (.leaf trace1024Block13)) (.node (.leaf trace1024Block14) (.leaf trace1024Block15))))

theorem trace1024Tree_length : trace1024Tree.length = 1024 := by
  decide


/-- A kernel-efficient checker state.  The bit set is a natural-number bitset.
Blocked branches need only authenticated membership for recurrence soundness;
the decoded witness clock remains provenance data but is not carried through
every checkpoint. -/
structure BitTraceMachine where
  value : Nat
  seenBits : Nat

def initialBitTraceMachine : BitTraceMachine := ⟨0, 1⟩

/-- The semantic invariant for the kernel-efficient bitset state. -/
structure BitTraceMachine.Represents (machine : BitTraceMachine)
    (state : State) : Prop where
  value_eq : machine.value = state.value
  seen_iff : ∀ x, machine.seenBits.testBit x = true ↔ x ∈ state.seen

/-- Relate the efficient bitset state to the already-proved array checker
invariant.  This is the bridge by which the new checker reuses
`TraceMachine.Represents`. -/
structure BitTraceMachine.Refines (machine : BitTraceMachine)
    (traceMachine : TraceMachine) : Prop where
  value_eq : machine.value = traceMachine.value
  seen_iff : ∀ x,
    machine.seenBits.testBit x = true ↔
      traceMachine.seenValues[x]? = some true

theorem BitTraceMachine.Refines.represents {machine : BitTraceMachine}
    {traceMachine : TraceMachine} {state : State}
    (hrefines : machine.Refines traceMachine)
    (htrace : traceMachine.Represents state) : machine.Represents state := by
  exact ⟨hrefines.value_eq.trans htrace.value_eq,
    fun x => (hrefines.seen_iff x).trans (htrace.seen_iff x)⟩

private theorem one_testBit (index : Nat) :
    Nat.testBit 1 index = true ↔ index = 0 := by
  cases index <;> simp [Nat.testBit_succ, Nat.testBit_zero]

private theorem testBit_insert (bits next index : Nat) :
    ((bits ||| (1 <<< next)).testBit index = true) ↔
      index = next ∨ bits.testBit index = true := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  simp only [Bool.or_eq_true]
  by_cases hindex : index ≥ next
  · simp only [hindex, decide_true, Bool.true_and, one_testBit]
    have heq : index - next = 0 ↔ index = next := by omega
    rw [heq, or_comm]
  · simp only [hindex, decide_false, Bool.false_and, Bool.false_eq_true]
    have hne : index ≠ next := by omega
    simp [hne]

theorem initialBitTraceMachine_refines :
    initialBitTraceMachine.Refines (initialTraceMachine 1) := by
  refine ⟨rfl, ?_⟩
  intro x
  cases x <;> simp [initialBitTraceMachine, initialTraceMachine, one_testBit]

theorem initialBitTraceMachine_represents :
    initialBitTraceMachine.Represents initial := by
  apply initialBitTraceMachine_refines.represents
  exact initialTraceMachine_represents 1 (by decide)

def BitTraceMachine.record (machine : BitTraceMachine) (next : Nat) :
    BitTraceMachine where
  value := next
  seenBits := machine.seenBits ||| (1 <<< next)

theorem BitTraceMachine.record_represents {machine : BitTraceMachine}
    {state : State} (hrep : machine.Represents state) (next : Nat) :
    (machine.record next).Represents ⟨next, next :: state.seen⟩ := by
  refine ⟨rfl, ?_⟩
  intro x
  rw [show (machine.record next).seenBits =
      machine.seenBits ||| (1 <<< next) by rfl]
  rw [testBit_insert, hrep.seen_iff]
  simp only [List.mem_cons]

def applyBitTraceReason (clock : Nat) (machine : BitTraceMachine)
    (reason : TraceStepReason) : BitTraceMachine :=
  machine.record <| match reason with
    | .fresh => machine.value - clock
    | .nonpositive | .blocked _ => machine.value + clock

def ValidBitTraceStep (capacity clock : Nat) (machine : BitTraceMachine) :
    TraceStepReason → Prop
  | .fresh =>
      clock < machine.value ∧
      machine.value - clock < capacity ∧
      machine.seenBits.testBit (machine.value - clock) = false
  | .nonpositive =>
      ¬ clock < machine.value ∧ machine.value + clock < capacity
  | .blocked _ =>
      clock < machine.value ∧
      machine.seenBits.testBit (machine.value - clock) = true ∧
      machine.value + clock < capacity

instance (capacity clock : Nat) (machine : BitTraceMachine)
    (reason : TraceStepReason) :
    Decidable (ValidBitTraceStep capacity clock machine reason) := by
  cases reason <;> unfold ValidBitTraceStep <;> infer_instance

theorem applyBitTraceReason_represents_step {capacity clock : Nat}
    {machine : BitTraceMachine} {state : State} {reason : TraceStepReason}
    (hrep : machine.Represents state)
    (hvalid : ValidBitTraceStep capacity clock machine reason) :
    (applyBitTraceReason clock machine reason).Represents (step clock state) := by
  cases reason with
  | fresh =>
      rcases hvalid with ⟨hpositive, _, hfresh⟩
      have hpositive' : clock < state.value := by
        simpa [← hrep.value_eq] using hpositive
      have hfresh' : state.value - clock ∉ state.seen := by
        intro hmem
        have hseen : machine.seenBits.testBit (machine.value - clock) = true :=
          (hrep.seen_iff _).2 (by simpa [← hrep.value_eq] using hmem)
        rw [hfresh] at hseen
        contradiction
      rw [step_of_subtract ⟨hpositive', hfresh'⟩]
      simpa [applyBitTraceReason, hrep.value_eq] using
        machine.record_represents hrep (machine.value - clock)
  | nonpositive =>
      rcases hvalid with ⟨hnonpositive, _⟩
      have hnonpositive' : ¬ clock < state.value := by
        simpa [← hrep.value_eq] using hnonpositive
      rw [step_of_nonpositive hnonpositive']
      simpa [applyBitTraceReason, hrep.value_eq] using
        machine.record_represents hrep (machine.value + clock)
  | blocked witnessTime =>
      rcases hvalid with ⟨_, hseen, _⟩
      have hmem : state.value - clock ∈ state.seen := by
        apply (hrep.seen_iff _).1
        simpa [← hrep.value_eq] using hseen
      rw [step_of_seen hmem]
      simpa [applyBitTraceReason, hrep.value_eq] using
        machine.record_represents hrep (machine.value + clock)

def runCheckedBitTraceBlock (capacity : Nat) :
    Nat → BitTraceMachine → List Nat → Option BitTraceMachine
  | _, machine, [] => some machine
  | clock, machine, code :: codes =>
      let reason := decodeTraceReason code
      if ValidBitTraceStep capacity clock machine reason then
        runCheckedBitTraceBlock capacity (clock + 1)
          (applyBitTraceReason clock machine reason) codes
      else
        none

theorem runCheckedBitTraceBlock_represents {capacity clock : Nat}
    {machine output : BitTraceMachine} {state : State} {codes : List Nat}
    (hrep : machine.Represents state)
    (hrun : runCheckedBitTraceBlock capacity clock machine codes = some output) :
    output.Represents (runRecamanSteps clock state codes.length) := by
  induction codes generalizing clock machine state with
  | nil =>
      simp only [runCheckedBitTraceBlock, Option.some.injEq] at hrun
      subst output
      simpa [runRecamanSteps] using hrep
  | cons code codes ih =>
      simp only [runCheckedBitTraceBlock] at hrun
      split at hrun
      · rename_i hvalid
        have hnext := applyBitTraceReason_represents_step hrep hvalid
        simpa [runRecamanSteps] using ih hnext hrun
      · simp at hrun

namespace BalancedTrace

/-- Balanced one-pass evaluator using the compact bitset state. -/
def runBits (capacity : Nat) :
    Nat → BitTraceMachine → BalancedTrace → Option BitTraceMachine
  | start, machine, .leaf codes =>
      runCheckedBitTraceBlock capacity (start + 1) machine codes
  | start, machine, .node left right =>
      match left.runBits capacity start machine with
      | none => none
      | some checkpoint =>
          right.runBits capacity (start + left.length) checkpoint

/-- Validate the trace and its numeric endpoint in one kernel reduction. -/
def verifiesBitsValue (tree : BalancedTrace) (capacity start : Nat)
    (machine : BitTraceMachine) (expected : Nat) : Bool :=
  match tree.runBits capacity start machine with
  | none => false
  | some output => output.value == expected

theorem runBits_represents {capacity start : Nat}
    {machine output : BitTraceMachine} {tree : BalancedTrace}
    (hrep : machine.Represents (stateAt start))
    (hrun : tree.runBits capacity start machine = some output) :
    output.Represents (stateAt (start + tree.length)) := by
  induction tree generalizing start machine output with
  | leaf codes =>
      have hout := runCheckedBitTraceBlock_represents hrep hrun
      rw [← stateAt_add_eq_runRecamanSteps] at hout
      exact hout
  | node left right ihLeft ihRight =>
      simp only [runBits] at hrun
      generalize hcheckpoint : left.runBits capacity start machine = checkpoint at hrun
      cases checkpoint with
      | none => simp at hrun
      | some checkpoint =>
          have hleft := ihLeft hrep hcheckpoint
          have hright := ihRight hleft hrun
          simpa [BalancedTrace.length, Nat.add_assoc] using hright

theorem verifiesBitsValue_witness {tree : BalancedTrace}
    {capacity start expected : Nat} {machine : BitTraceMachine}
    (hverify : tree.verifiesBitsValue capacity start machine expected = true) :
    ∃ output, tree.runBits capacity start machine = some output ∧
      output.value = expected := by
  unfold verifiesBitsValue at hverify
  generalize hrun : tree.runBits capacity start machine = result at hverify
  cases result with
  | none => simp at hverify
  | some output =>
      refine ⟨output, rfl, ?_⟩
      simpa using hverify

theorem verified_bits_value {tree : BalancedTrace}
    {capacity start expected : Nat} {machine : BitTraceMachine}
    (hrep : machine.Represents (stateAt start))
    (hverify : tree.verifiesBitsValue capacity start machine expected = true) :
    a (start + tree.length) = expected := by
  rcases verifiesBitsValue_witness hverify with ⟨output, hrun, hvalue⟩
  have hout := runBits_represents hrep hrun
  unfold a
  rw [← hout.value_eq, hvalue]

end BalancedTrace

/-! ## A 4825-step certificate for the clock-112 obstruction

The first sixteen leaves are shared with `trace1024Tree`; sixty additional
64-step leaves (the final leaf has 25 steps) extend the same authenticated
orbit to the first occurrence of 371. -/

def trace4825Block16 : List Nat :=
  [0, 764, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block17 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block18 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block19 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 288, 1228, 0, 1222, 0, 1216, 0, 1210, 0, 1204, 0, 1198, 0, 1192, 0, 1186, 0, 1180, 0, 1174, 0, 1168, 0, 1162, 0, 984, 0, 978, 0, 972, 0, 966, 0, 960, 0, 954, 0, 948, 0, 842, 0, 836, 0, 830, 0, 824, 0, 818, 0, 812, 0, 806]

def trace4825Block20 : List Nat :=
  [0, 800, 0, 794, 0, 788, 0, 782, 0, 776, 0, 758, 0, 764, 0, 1030, 0, 0, 566, 0, 572, 0, 578, 678, 1295, 0, 0, 694, 0, 700, 0, 706, 0, 712, 0, 718, 0, 724, 0, 0, 668, 0, 674, 0, 171, 0, 165, 0, 159, 0, 153, 0, 147, 0, 141, 0, 187, 0, 105, 0, 111, 0, 121, 0]

def trace4825Block21 : List Nat :=
  [0, 1, 237, 1346, 1283, 0, 1289, 0, 1295, 0, 1309, 0, 1315, 0, 1321, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block22 : List Nat :=
  [0, 1, 309, 1410, 0, 1404, 0, 1398, 0, 1392, 0, 1386, 0, 1380, 0, 1374, 0, 1368, 0, 0, 124, 0, 130, 0, 140, 0, 146, 0, 152, 0, 158, 0, 164, 0, 170, 0, 36, 0, 369, 0, 375, 0, 381, 0, 387, 0, 393, 0, 399, 0, 405, 0, 63, 0, 57, 0, 51, 0, 45, 0, 39, 0, 81, 0]

def trace4825Block23 : List Nat :=
  [87, 0, 93, 0, 99, 0, 21, 0, 200, 0, 206, 0, 212, 0, 218, 0, 224, 0, 30, 0, 24, 0, 42, 0, 48, 0, 54, 0, 60, 0, 66, 0, 15, 0, 9, 0, 27, 0, 33, 0, 12, 0, 18, 0, 131, 0, 6, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block24 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block25 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block26 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 512, 1713, 0, 1707, 0, 1701, 0, 1695, 0, 1689, 0, 1683, 0, 1677, 0]

def trace4825Block27 : List Nat :=
  [1671, 0, 1665, 0, 1659, 0, 1653, 0, 1647, 0, 1641, 0, 1635, 0, 1629, 0, 1623, 0, 1617, 0, 1611, 0, 1605, 0, 1599, 0, 1593, 0, 1587, 0, 1581, 0, 1575, 0, 1569, 0, 1563, 0, 1557, 0, 1551, 0, 1545, 0, 1539, 0, 1533, 0, 1527, 0, 1521, 0, 1515, 0, 1509, 0, 1503, 0, 1497, 0, 1491, 0, 1485, 0]

def trace4825Block28 : List Nat :=
  [1479, 0, 1473, 0, 1467, 0, 1461, 0, 1455, 0, 1449, 0, 1415, 0, 1421, 0, 1427, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block29 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block30 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 306, 1587, 0, 1581, 0, 1575, 0, 1569, 0]

def trace4825Block31 : List Nat :=
  [1563, 0, 1557, 0, 1551, 0, 1545, 0, 1539, 0, 1533, 0, 1527, 0, 1521, 0, 1515, 0, 1509, 0, 1503, 0, 1497, 0, 1491, 0, 1485, 0, 1479, 0, 1473, 0, 1467, 0, 1461, 0, 1455, 0, 1449, 0, 1415, 0, 1421, 0, 1427, 0, 1813, 0, 0, 663, 0, 657, 0, 651, 0, 645, 0, 639, 0, 633, 0, 627, 0, 621]

def trace4825Block32 : List Nat :=
  [0, 615, 0, 609, 0, 603, 0, 597, 0, 591, 0, 585, 0, 511, 0, 453, 1231, 2004, 0, 2010, 0, 2016, 0, 2022, 0, 2028, 0, 2034, 0, 0, 1297, 0, 1311, 0, 1317, 0, 0, 843, 0, 341, 1363, 2084, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block33 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 289, 1287, 0, 1293, 0, 1299, 0, 1313, 0, 1319, 0, 2089, 0, 2107, 0, 2101, 0, 2095, 0, 0, 925, 0, 931, 0, 937, 0, 943, 0, 949, 0, 955, 0, 961]

def trace4825Block34 : List Nat :=
  [0, 967, 0, 973, 0, 979, 0, 985, 0, 231, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block35 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Block36 : List Nat :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 191, 2053, 0, 2059, 0, 2065, 0, 1235, 0, 1241, 0, 1247, 0, 1253, 0, 1259, 0, 1265, 0, 1271, 0, 1277, 0, 1283, 0, 1289, 0, 1295, 0, 1309, 0]

def trace4825Block37 : List Nat :=
  [1315, 0, 1321, 0, 1363, 0, 2105, 0, 2099, 0, 2217, 0, 2167, 0, 2173, 0, 2179, 0, 2185, 0, 0, 288, 0, 282, 0, 276, 0, 270, 0, 264, 0, 258, 0, 252, 0, 117, 0, 232, 0, 310, 0, 384, 0, 358, 0, 364, 0, 0, 1, 0, 1, 422, 2415, 2352, 0, 2358, 0, 2364, 0, 2370, 0, 2376, 0, 2382]

def trace4825Block38 : List Nat :=
  [0, 2388, 0, 0, 0, 484, 0, 490, 0, 496, 0, 502, 0, 508, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 116, 2493, 0]

def trace4825Block39 : List Nat :=
  [2487, 0, 2481, 0, 2475, 0, 2469, 0, 2463, 0, 2441, 0, 2447, 0, 0, 578, 0, 584, 0, 590, 0, 596, 0, 602, 0, 608, 0, 614, 0, 620, 0, 626, 0, 632, 0, 638, 0, 644, 0, 650, 0, 656, 0, 662, 0, 668, 0, 674, 0, 171, 0, 165, 0, 159, 0, 153, 0, 147, 0, 141, 0, 187, 0, 105]

def trace4825Block40 : List Nat :=
  [0, 111, 0, 121, 0, 1347, 0, 241, 0, 247, 0, 253, 0, 259, 0, 265, 0, 271, 0, 277, 0, 283, 0, 77, 0, 71, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1365]

def trace4825Block41 : List Nat :=
  [2555, 0, 2561, 0, 2567, 0, 2573, 0, 2579, 0, 2585, 0, 0, 327, 0, 333, 0, 339, 0, 98, 0, 92, 0, 70, 0, 76, 0, 0, 1, 736, 2653, 0, 0, 752, 0, 122, 0, 128, 0, 138, 0, 144, 0, 150, 0, 156, 0, 162, 0, 168, 0, 38, 0, 772, 0, 373, 0, 379, 0, 385, 0, 391, 0, 397]

def trace4825Block42 : List Nat :=
  [0, 403, 0, 65, 0, 59, 0, 53, 0, 47, 0, 37, 0, 79, 0, 85, 0, 91, 0, 97, 0, 23, 0, 198, 0, 204, 0, 210, 0, 216, 0, 222, 0, 32, 0, 22, 0, 40, 0, 46, 0, 52, 0, 58, 0, 64, 0, 17, 0, 11, 0, 25, 0, 31, 0, 10, 0, 16, 0, 5, 0, 4, 0, 1]

def trace4825Block43 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block44 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 987, 2868, 0, 2862, 0, 2856, 0, 2850, 0, 2844, 0, 2838]

def trace4825Block45 : List Nat :=
  [0, 2832, 0, 2826, 0, 2820, 0, 2814, 0, 2808, 0, 2802, 0, 2796, 0, 2790, 0, 2784, 0, 2778, 0, 2772, 0, 2766, 0, 2760, 0, 2754, 0, 2748, 0, 2742, 0, 2736, 0, 2730, 0, 2724, 0, 2718, 0, 2712, 0, 2706, 0, 2700, 0, 2694, 0, 2688, 0, 2682, 0, 2676, 0, 2670, 0, 2664, 0, 2658, 0, 2652, 0, 2630]

def trace4825Block46 : List Nat :=
  [0, 2636, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block47 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block48 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 775, 2768, 0, 2762, 0, 2756, 0, 2750, 0, 2744, 0, 2738, 0, 2732, 0, 2726, 0, 2720, 0, 2714, 0, 2708, 0, 2702, 0, 2696, 0, 2690, 0, 2684, 0, 2678, 0, 2672, 0, 2666, 0, 2656, 0, 2970, 0, 2628, 0, 2634, 0, 2952, 0, 0, 0, 1, 0, 1]

def trace4825Block49 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block50 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block51 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block52 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block53 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block54 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block55 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block56 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block57 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block58 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block59 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block60 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 527, 3868, 0, 3862, 0, 3856, 0, 3850, 0, 3844, 0, 3838, 0, 3832, 0, 3826, 0, 3820, 0, 3814, 0, 3808, 0, 3802, 0, 3796, 0, 3790, 0, 3784, 0, 3778, 0, 3772, 0, 3766]

def trace4825Block61 : List Nat :=
  [0, 3760, 0, 3754, 0, 3748, 0, 3742, 0, 3736, 0, 3730, 0, 3724, 0, 3718, 0, 3712, 0, 3706, 0, 3700, 0, 3694, 0, 3688, 0, 3682, 0, 3676, 0, 3670, 0, 3664, 0, 3658, 0, 3652, 0, 3646, 0, 3640, 0, 3634, 0, 3628, 0, 3622, 0, 3616, 0, 3610, 0, 3604, 0, 3598, 0, 3592, 0, 3586, 0, 3580, 0, 3574]

def trace4825Block62 : List Nat :=
  [0, 3568, 0, 3562, 0, 3556, 0, 1361, 0, 1355, 0, 3538, 0, 3532, 0, 3526, 0, 3520, 0, 3514, 0, 3508, 0, 3502, 0, 3496, 0, 3490, 0, 3484, 0, 3478, 0, 3472, 0, 3466, 0, 3460, 0, 3454, 0, 3448, 0, 3442, 0, 3436, 0, 3430, 0, 3424, 0, 3418, 0, 3412, 0, 3406, 0, 3400, 0, 3394, 0, 3388, 0, 3382]

def trace4825Block63 : List Nat :=
  [0, 3376, 0, 2866, 0, 2860, 0, 2854, 0, 1307, 0, 2842, 0, 2836, 0, 2830, 0, 2824, 0, 2818, 0, 2812, 0, 2806, 0, 2800, 0, 2794, 0, 2788, 0, 2782, 0, 2776, 0, 2770, 0, 2764, 0, 2758, 0, 2752, 0, 2746, 0, 2740, 0, 2734, 0, 2728, 0, 2722, 0, 2716, 0, 2710, 0, 2704, 0, 2698, 0, 2692, 0, 2686]

def trace4825Block64 : List Nat :=
  [0, 2680, 0, 2674, 0, 2668, 0, 2662, 0, 2972, 0, 2626, 0, 2632, 0, 2638, 0, 3136, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 420, 2632, 4057, 0, 4063, 0, 4069, 0, 4075, 0, 4081, 0, 4087, 0, 4093, 0, 4099, 0, 4105, 0, 4111, 0, 4117, 0]

def trace4825Block65 : List Nat :=
  [0, 2576, 0, 2570, 0, 2564, 0, 2558, 0, 2552, 0, 2546, 0, 2540, 0, 2534, 0, 2496, 0, 2502, 0, 2508, 0, 0, 1828, 0, 1834, 0, 1840, 0, 1846, 0, 1852, 0, 1858, 0, 1864, 0, 1870, 0, 1876, 0, 1882, 0, 1888, 0, 1894, 0, 1900, 0, 1906, 0, 1912, 0, 1918, 0, 1924, 0, 1930, 0, 1936, 0, 1942, 0]

def trace4825Block66 : List Nat :=
  [1948, 0, 1954, 0, 1960, 0, 1966, 0, 1972, 0, 306, 0, 300, 0, 294, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block67 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block68 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block69 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

def trace4825Block70 : List Nat :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 677, 2658, 0, 2652, 0, 2630, 0, 2636, 0, 2950, 0, 4120, 0, 4458, 0, 4452, 0, 4446, 0, 4440, 0, 4434, 0, 4428, 0, 4422, 0, 4416, 0, 4410, 0, 4404, 0, 4398, 0, 4392, 0, 4386, 0, 4380, 0, 2586, 0, 2580, 0, 2574, 0, 2568, 0, 2562]

def trace4825Block71 : List Nat :=
  [0, 2556, 0, 2550, 0, 2544, 0, 2538, 0, 2532, 0, 2498, 0, 2504, 0, 2510, 0, 4188, 0, 4194, 0, 4200, 0, 4206, 0, 4212, 0, 4218, 0, 4224, 0, 4230, 0, 4236, 0, 4242, 0, 0, 945, 0, 951, 0, 957, 0, 963, 0, 969, 0, 975, 0, 981, 0, 235, 2340, 4569, 0, 4575, 0, 4581, 0, 0, 2376, 0, 2382]

def trace4825Block72 : List Nat :=
  [0, 2388, 0, 2438, 0, 0, 2278, 0, 2284, 0, 2290, 0, 2296, 0, 2302, 0, 2308, 0, 2314, 0, 2320, 0, 2326, 0, 2332, 0, 2338, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 185, 4630, 4543, 0, 4549, 0, 4555, 0, 4561, 0, 4567, 0, 4573, 0, 4579, 0, 4625, 0, 4611, 0, 0, 0, 1131, 0, 1137, 0]

def trace4825Block73 : List Nat :=
  [1143, 0, 1149, 0, 1155, 0, 1161, 0, 1167, 0, 1173, 0, 1179, 0, 1185, 0, 1191, 0, 1197, 0, 1203, 0, 1209, 0, 1215, 0, 1221, 0, 1227, 0, 286, 0, 280, 0, 274, 0, 268, 0, 262, 0, 256, 0, 250, 0, 228, 0, 234, 0, 308, 0, 354, 0, 360, 0, 366, 0, 2420, 0, 426, 0, 432, 0, 438, 0]

def trace4825Block74 : List Nat :=
  [444, 0, 450, 0, 176, 0, 182, 0, 196, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 468, 4704, 0, 4710, 0, 4716, 0, 4722]

def trace4825Block75 : List Nat :=
  [0, 4728, 0, 4734, 0, 4740, 0, 4746, 0, 0, 2490, 0, 116, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

def trace4825Tree : BalancedTrace :=
  .node (.node (.node (.node (.node (.node (.leaf trace1024Block00) (.leaf trace1024Block01)) (.node (.leaf trace1024Block02) (.leaf trace1024Block03))) (.node (.node (.leaf trace1024Block04) (.leaf trace1024Block05)) (.node (.leaf trace1024Block06) (.node (.leaf trace1024Block07) (.leaf trace1024Block08))))) (.node (.node (.node (.leaf trace1024Block09) (.leaf trace1024Block10)) (.node (.leaf trace1024Block11) (.node (.leaf trace1024Block12) (.leaf trace1024Block13)))) (.node (.node (.leaf trace1024Block14) (.leaf trace1024Block15)) (.node (.leaf trace4825Block16) (.node (.leaf trace4825Block17) (.leaf trace4825Block18)))))) (.node (.node (.node (.node (.leaf trace4825Block19) (.leaf trace4825Block20)) (.node (.leaf trace4825Block21) (.leaf trace4825Block22))) (.node (.node (.leaf trace4825Block23) (.leaf trace4825Block24)) (.node (.leaf trace4825Block25) (.node (.leaf trace4825Block26) (.leaf trace4825Block27))))) (.node (.node (.node (.leaf trace4825Block28) (.leaf trace4825Block29)) (.node (.leaf trace4825Block30) (.node (.leaf trace4825Block31) (.leaf trace4825Block32)))) (.node (.node (.leaf trace4825Block33) (.leaf trace4825Block34)) (.node (.leaf trace4825Block35) (.node (.leaf trace4825Block36) (.leaf trace4825Block37))))))) (.node (.node (.node (.node (.node (.leaf trace4825Block38) (.leaf trace4825Block39)) (.node (.leaf trace4825Block40) (.leaf trace4825Block41))) (.node (.node (.leaf trace4825Block42) (.leaf trace4825Block43)) (.node (.leaf trace4825Block44) (.node (.leaf trace4825Block45) (.leaf trace4825Block46))))) (.node (.node (.node (.leaf trace4825Block47) (.leaf trace4825Block48)) (.node (.leaf trace4825Block49) (.node (.leaf trace4825Block50) (.leaf trace4825Block51)))) (.node (.node (.leaf trace4825Block52) (.leaf trace4825Block53)) (.node (.leaf trace4825Block54) (.node (.leaf trace4825Block55) (.leaf trace4825Block56)))))) (.node (.node (.node (.node (.leaf trace4825Block57) (.leaf trace4825Block58)) (.node (.leaf trace4825Block59) (.leaf trace4825Block60))) (.node (.node (.leaf trace4825Block61) (.leaf trace4825Block62)) (.node (.leaf trace4825Block63) (.node (.leaf trace4825Block64) (.leaf trace4825Block65))))) (.node (.node (.node (.leaf trace4825Block66) (.leaf trace4825Block67)) (.node (.leaf trace4825Block68) (.node (.leaf trace4825Block69) (.leaf trace4825Block70)))) (.node (.node (.leaf trace4825Block71) (.leaf trace4825Block72)) (.node (.leaf trace4825Block73) (.node (.leaf trace4825Block74) (.leaf trace4825Block75)))))))

theorem trace4825Tree_length : trace4825Tree.length = 4825 := by
  decide



set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem trace1024Bits_checked :
    trace1024Tree.verifiesBitsValue 4096 0 initialBitTraceMachine 3698 = true := by
  decide

theorem balanced_a_1024 : a 1024 = 3698 := by
  have hvalue := BalancedTrace.verified_bits_value
    initialBitTraceMachine_represents trace1024Bits_checked
  rw [trace1024Tree_length] at hvalue
  simpa using hvalue

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem trace4825Bits_checked :
    trace4825Tree.verifiesBitsValue 20000 0 initialBitTraceMachine 371 = true := by
  decide

theorem balanced_a_4825 : a 4825 = 371 := by
  have hvalue := BalancedTrace.verified_bits_value
    initialBitTraceMachine_represents trace4825Bits_checked
  rw [trace4825Tree_length] at hvalue
  simpa using hvalue

end Recaman
