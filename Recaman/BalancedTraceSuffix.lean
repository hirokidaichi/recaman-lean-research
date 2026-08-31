import Recaman.BalancedTraceCertificate

namespace Recaman

/-!
# Authenticated suffixes of a balanced trace

A successful balanced run contains authenticated checkpoints at every tree
boundary.  These lemmas expose the input of the rightmost leaf and split a
successful checked block at an arbitrary list boundary.  They allow several
nearby endpoint values to be recovered from one expensive deep certificate.
-/

namespace BalancedTrace

/-- Validate a balanced trace while also checking that `mex` is the least
value absent from the authenticated endpoint history. -/
def verifiesBitsMex (tree : BalancedTrace) (capacity start : Nat)
    (machine : BitTraceMachine) (mex : Nat) : Bool :=
  match tree.runBits capacity start machine with
  | none => false
  | some output =>
      (List.range mex).all (fun x => output.seenBits.testBit x) &&
        !output.seenBits.testBit mex

/-- Computational least-missing verification exposes the same successful
run together with all of its checked membership bits. -/
theorem verifiesBitsMex_witness {tree : BalancedTrace}
    {capacity start mex : Nat} {machine : BitTraceMachine}
    (hverify : tree.verifiesBitsMex capacity start machine mex = true) :
    ∃ output, tree.runBits capacity start machine = some output ∧
      (∀ x, x < mex → output.seenBits.testBit x = true) ∧
      output.seenBits.testBit mex = false := by
  unfold verifiesBitsMex at hverify
  generalize hrun : tree.runBits capacity start machine = result at hverify
  cases result with
  | none => simp at hverify
  | some output =>
      have hchecks := Bool.and_eq_true_iff.mp hverify
      refine ⟨output, rfl, ?_, by simpa using hchecks.2⟩
      intro x hx
      exact (List.all_eq_true.mp hchecks.1) x (List.mem_range.mpr hx)

/-- Soundness of a checked mex: every smaller value belongs to the actual
orbit history at the endpoint, while the mex itself does not. -/
theorem verified_bits_mex {tree : BalancedTrace}
    {capacity start mex : Nat} {machine : BitTraceMachine}
    (hrep : machine.Represents (stateAt start))
    (hverify : tree.verifiesBitsMex capacity start machine mex = true) :
    (∀ x, x < mex → x ∈ valuesThrough (start + tree.length)) ∧
      mex ∉ valuesThrough (start + tree.length) := by
  rcases verifiesBitsMex_witness hverify with
    ⟨output, hrun, hsmall, hmex⟩
  have hout := runBits_represents hrep hrun
  constructor
  · intro x hx
    change x ∈ (stateAt (start + tree.length)).seen
    exact (hout.seen_iff x).1 (hsmall x hx)
  · intro hmem
    change mex ∈ (stateAt (start + tree.length)).seen at hmem
    have hbit := (hout.seen_iff mex).2 hmem
    rw [hmex] at hbit
    contradiction

/-- Codes stored in the rightmost leaf. -/
def rightmostCodes : BalancedTrace → List Nat
  | .leaf codes => codes
  | .node _ right => right.rightmostCodes

/-- A successful balanced run exposes the authenticated input checkpoint and
absolute start time of its rightmost leaf. -/
theorem runBits_rightmostCheckpoint {capacity start : Nat}
    {machine output : BitTraceMachine} {tree : BalancedTrace}
    (hrep : machine.Represents (stateAt start))
    (hrun : tree.runBits capacity start machine = some output) :
    ∃ (leafStart : Nat) (checkpoint : BitTraceMachine),
      leafStart + tree.rightmostCodes.length = start + tree.length ∧
      checkpoint.Represents (stateAt leafStart) ∧
      runCheckedBitTraceBlock capacity (leafStart + 1) checkpoint
        tree.rightmostCodes = some output := by
  induction tree generalizing start machine output with
  | leaf codes =>
      refine ⟨start, machine, ?_, hrep, ?_⟩
      · simp [rightmostCodes, length]
      · simpa [runBits, rightmostCodes] using hrun
  | node left right _ihLeft ihRight =>
      simp only [runBits] at hrun
      generalize hleft : left.runBits capacity start machine = checkpoint
        at hrun
      cases checkpoint with
      | none => simp at hrun
      | some checkpoint =>
          have hleftRep := runBits_represents hrep hleft
          rcases ihRight hleftRep hrun with
            ⟨leafStart, leafCheckpoint, htime, hcheckpointRep, hleaf⟩
          refine ⟨leafStart, leafCheckpoint, ?_, hcheckpointRep, hleaf⟩
          simpa [rightmostCodes, length, Nat.add_assoc] using htime

end BalancedTrace

/-- Checked block execution sequences over list append. -/
theorem runCheckedBitTraceBlock_append (capacity clock : Nat)
    (machine : BitTraceMachine) (front back : List Nat) :
    runCheckedBitTraceBlock capacity clock machine (front ++ back) =
      match runCheckedBitTraceBlock capacity clock machine front with
      | none => none
      | some checkpoint =>
          runCheckedBitTraceBlock capacity (clock + front.length)
            checkpoint back := by
  induction front generalizing clock machine with
  | nil => simp [runCheckedBitTraceBlock]
  | cons code codes ih =>
      simp only [List.cons_append, runCheckedBitTraceBlock]
      split
      · simp only [ih, List.length_cons]
        simp [Nat.add_comm, Nat.add_left_comm]
      · rfl

/-- Successful execution of an appended block exposes the intermediate
authenticated machine at the split. -/
theorem runCheckedBitTraceBlock_append_witness {capacity clock : Nat}
    {machine output : BitTraceMachine} {front back : List Nat}
    (hrun : runCheckedBitTraceBlock capacity clock machine
      (front ++ back) = some output) :
    ∃ checkpoint : BitTraceMachine,
      runCheckedBitTraceBlock capacity clock machine front =
          some checkpoint ∧
        runCheckedBitTraceBlock capacity (clock + front.length)
          checkpoint back = some output := by
  rw [runCheckedBitTraceBlock_append] at hrun
  generalize hprefix :
      runCheckedBitTraceBlock capacity clock machine front = result at hrun
  cases result with
  | none => simp at hrun
  | some checkpoint =>
      exact ⟨checkpoint, rfl, hrun⟩

/-- Unchecked replay of the value updates encoded by a compact block. -/
def replayBitTraceBlock : Nat → BitTraceMachine → List Nat →
    BitTraceMachine
  | _, machine, [] => machine
  | clock, machine, code :: codes =>
      replayBitTraceBlock (clock + 1)
        (applyBitTraceReason clock machine (decodeTraceReason code)) codes

/-- A successful checked block has exactly the endpoint of unchecked replay;
validity controls soundness, while this equality exposes its arithmetic. -/
theorem runCheckedBitTraceBlock_eq_replay {capacity clock : Nat}
    {machine output : BitTraceMachine} {codes : List Nat}
    (hrun : runCheckedBitTraceBlock capacity clock machine codes =
      some output) :
    replayBitTraceBlock clock machine codes = output := by
  induction codes generalizing clock machine with
  | nil =>
      simpa [runCheckedBitTraceBlock, replayBitTraceBlock] using hrun
  | cons code codes ih =>
      simp only [runCheckedBitTraceBlock] at hrun
      split at hrun
      · simp only [replayBitTraceBlock]
        exact ih hrun
      · simp at hrun

end Recaman
