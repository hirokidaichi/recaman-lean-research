import Recaman.History

namespace Recaman

/-!
# Kernel-checkable chunked orbit traces

`stateAt` stores the whole visited prefix as a list.  Reducing a deep orbit
equality directly therefore repeats a linear membership search at every
subtraction step.  The checker below carries an authenticated bitmap beside
the ordinary state.  A fresh subtraction is checked by a `false` bitmap
entry, while an addition has either a nonpositive reason or an explicit
earlier clock whose value is the blocked subtraction candidate.

The bitmap and chronological value array are not trusted.  `Represents`
connects them to an ordinary `State`, and the soundness theorem preserves that
relation after every checked chunk.  Thus external code may produce the
certificate, but only the small checker and its proof are in the trusted
base.
-/

/-- Why the recurrence takes a particular branch.

The blocked constructor records an occurrence clock.  The checker verifies
both that value and the independently maintained visited-value bitmap. -/
inductive TraceStepReason where
  | fresh
  | nonpositive
  | blocked (witnessTime : Nat)
deriving Repr, DecidableEq

/-- Compact state used only by the trace checker.  `seenValues[x]` is the
authenticated membership bit for `x`; `values[t]` is the value recorded at
clock `t`. -/
structure TraceMachine where
  value : Nat
  seenValues : Array Bool
  values : Array Nat
deriving Repr, DecidableEq

/-- The initial compact state, with a caller-selected value capacity. -/
def initialTraceMachine (capacity : Nat) : TraceMachine where
  value := 0
  seenValues := (Array.replicate capacity false).setIfInBounds 0 true
  values := #[0]

/-- Record a checked next value.  The validity predicate guarantees that the
bitmap write is in bounds. -/
def TraceMachine.record (machine : TraceMachine) (next : Nat) : TraceMachine where
  value := next
  seenValues := machine.seenValues.setIfInBounds next true
  values := machine.values.push next

/-- Numeric value prescribed by a certificate reason. -/
def traceNextValue (clock : Nat) (machine : TraceMachine)
    (reason : TraceStepReason) : Nat :=
  match reason with
  | .fresh => machine.value - clock
  | .nonpositive | .blocked _ => machine.value + clock

/-- Apply a reason without trusting it.  Soundness is provided only after
`ValidTraceStep` has been checked. -/
def applyTraceReason (clock : Nat) (machine : TraceMachine)
    (reason : TraceStepReason) : TraceMachine :=
  machine.record (traceNextValue clock machine reason)

/-- The three branch checks are deliberately separate.

* `fresh` checks positivity and a `false` authenticated membership bit;
* `nonpositive` checks that subtraction cannot stay positive;
* `blocked witnessTime` checks the earlier trace value and a `true` bit.

Every branch also checks that the next value fits in the fixed bitmap. -/
def ValidTraceStep (clock : Nat) (machine : TraceMachine) :
    TraceStepReason → Prop
  | .fresh =>
      clock < machine.value ∧
      machine.value - clock < machine.seenValues.size ∧
      machine.seenValues[machine.value - clock]? = some false
  | .nonpositive =>
      ¬ clock < machine.value ∧
      machine.value + clock < machine.seenValues.size
  | .blocked witnessTime =>
      clock < machine.value ∧
      witnessTime < clock ∧
      machine.values[witnessTime]? = some (machine.value - clock) ∧
      machine.seenValues[machine.value - clock]? = some true ∧
      machine.value + clock < machine.seenValues.size

instance (clock : Nat) (machine : TraceMachine) (reason : TraceStepReason) :
    Decidable (ValidTraceStep clock machine reason) := by
  cases reason <;> unfold ValidTraceStep <;> infer_instance

/-- Recursive semantic validity of one certificate chunk. -/
def ValidTraceChunk : Nat → TraceMachine → List TraceStepReason → Prop
  | _, _, [] => True
  | clock, machine, reason :: reasons =>
      ValidTraceStep clock machine reason ∧
      ValidTraceChunk (clock + 1) (applyTraceReason clock machine reason) reasons

/-- Executable checker.  It performs constant-index bitmap/array checks rather
than searching the ordinary Recamán history list. -/
def checkTraceChunk : Nat → TraceMachine → List TraceStepReason → Bool
  | _, _, [] => true
  | clock, machine, reason :: reasons =>
      decide (ValidTraceStep clock machine reason) &&
        checkTraceChunk (clock + 1) (applyTraceReason clock machine reason) reasons

/-- Replay the certificate data after it has been checked. -/
def replayTraceChunk : Nat → TraceMachine → List TraceStepReason → TraceMachine
  | _, machine, [] => machine
  | clock, machine, reason :: reasons =>
      replayTraceChunk (clock + 1) (applyTraceReason clock machine reason) reasons

/-- Total number of steps in a list of independently checkable chunks. -/
def traceChunksLength : List (List TraceStepReason) → Nat
  | [] => 0
  | chunk :: chunks => chunk.length + traceChunksLength chunks

/-- Validate each chunk separately and carry the compact checkpoint to the
next chunk.  The recursive depth is bounded by the largest chunk rather than
the whole orbit prefix. -/
def checkTraceChunks : Nat → TraceMachine →
    List (List TraceStepReason) → Bool
  | _, _, [] => true
  | start, machine, chunk :: chunks =>
      checkTraceChunk (start + 1) machine chunk &&
        checkTraceChunks (start + chunk.length)
          (replayTraceChunk (start + 1) machine chunk) chunks

/-- Replay a list of chunks, preserving the same checkpoints used by the
checker. -/
def replayTraceChunks : Nat → TraceMachine →
    List (List TraceStepReason) → TraceMachine
  | _, machine, [] => machine
  | start, machine, chunk :: chunks =>
      replayTraceChunks (start + chunk.length)
        (replayTraceChunk (start + 1) machine chunk) chunks

/-- The corresponding ordinary-state iteration, starting with the supplied
clock as the next Recamán step. -/
def runRecamanSteps : Nat → State → Nat → State
  | _, state, 0 => state
  | clock, state, count + 1 =>
      runRecamanSteps (clock + 1) (step clock state) count

theorem checkTraceChunk_eq_true_iff (clock : Nat) (machine : TraceMachine)
    (reasons : List TraceStepReason) :
    checkTraceChunk clock machine reasons = true ↔
      ValidTraceChunk clock machine reasons := by
  induction reasons generalizing clock machine with
  | nil => simp [checkTraceChunk, ValidTraceChunk]
  | cons reason reasons ih =>
      simp [checkTraceChunk, ValidTraceChunk, ih, decide_eq_true_eq]

/-- Authentication invariant between compact checker data and the ordinary
state used by the sequence definition. -/
structure TraceMachine.Represents (machine : TraceMachine) (state : State) : Prop where
  value_eq : machine.value = state.value
  seen_iff : ∀ x,
    machine.seenValues[x]? = some true ↔ x ∈ state.seen
  values_reverse : machine.values.toList.reverse = state.seen

theorem initialTraceMachine_represents (capacity : Nat) (hcapacity : 0 < capacity) :
    (initialTraceMachine capacity).Represents initial := by
  refine ⟨rfl, ?_, rfl⟩
  intro x
  simp only [initialTraceMachine, Array.getElem?_setIfInBounds]
  by_cases hx : 0 = x
  · subst x
    simp [hcapacity, initial]
  · rw [if_neg hx]
    rw [Array.getElem?_replicate]
    have hx' : x ≠ 0 := Ne.symm hx
    split <;> simp [hx', initial]

theorem TraceMachine.record_represents {machine : TraceMachine} {state : State}
    (hrep : machine.Represents state) {next : Nat}
    (hnext : next < machine.seenValues.size) :
    (machine.record next).Represents ⟨next, next :: state.seen⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · intro x
    simp only [TraceMachine.record, Array.getElem?_setIfInBounds]
    by_cases hx : next = x
    · subst x
      simp [hnext]
    · rw [if_neg hx]
      simp only [List.mem_cons]
      constructor
      · intro hseen
        exact Or.inr ((hrep.seen_iff x).1 hseen)
      · rintro (heq | hseen)
        · exact False.elim (hx heq.symm)
        · exact (hrep.seen_iff x).2 hseen
  · simp [TraceMachine.record, hrep.values_reverse]

theorem applyTraceReason_represents_step {clock : Nat}
    {machine : TraceMachine} {state : State} {reason : TraceStepReason}
    (hrep : machine.Represents state)
    (hvalid : ValidTraceStep clock machine reason) :
    (applyTraceReason clock machine reason).Represents (step clock state) := by
  cases reason with
  | fresh =>
      rcases hvalid with ⟨hpositive, hbound, hfresh⟩
      have hpositive' : clock < state.value := by
        simpa [← hrep.value_eq] using hpositive
      have hfresh' : state.value - clock ∉ state.seen := by
        intro hmem
        have htrue : machine.seenValues[machine.value - clock]? = some true :=
          (hrep.seen_iff _).2 (by simpa [← hrep.value_eq] using hmem)
        rw [hfresh] at htrue
        contradiction
      have hcan : CanSubtract clock state := ⟨hpositive', hfresh'⟩
      rw [step_of_subtract hcan]
      simpa [applyTraceReason, traceNextValue, hrep.value_eq] using
        machine.record_represents hrep hbound
  | nonpositive =>
      rcases hvalid with ⟨hnonpositive, hbound⟩
      have hnonpositive' : ¬ clock < state.value := by
        simpa [← hrep.value_eq] using hnonpositive
      rw [step_of_nonpositive hnonpositive']
      simpa [applyTraceReason, traceNextValue, hrep.value_eq] using
        machine.record_represents hrep hbound
  | blocked witnessTime =>
      rcases hvalid with ⟨_, _, _, hseen, hbound⟩
      have hmem : state.value - clock ∈ state.seen := by
        have : machine.value - clock ∈ state.seen := (hrep.seen_iff _).1 hseen
        simpa [← hrep.value_eq] using this
      rw [step_of_seen hmem]
      simpa [applyTraceReason, traceNextValue, hrep.value_eq] using
        machine.record_represents hrep hbound

theorem validTraceChunk_represents {clock : Nat} {machine : TraceMachine}
    {state : State} {reasons : List TraceStepReason}
    (hrep : machine.Represents state)
    (hvalid : ValidTraceChunk clock machine reasons) :
    (replayTraceChunk clock machine reasons).Represents
      (runRecamanSteps clock state reasons.length) := by
  induction reasons generalizing clock machine state with
  | nil => simpa [replayTraceChunk, runRecamanSteps]
  | cons reason reasons ih =>
      rcases hvalid with ⟨hstep, htail⟩
      have hnext := applyTraceReason_represents_step hrep hstep
      simpa [replayTraceChunk, runRecamanSteps] using ih hnext htail

theorem stateAt_add_eq_runRecamanSteps (start count : Nat) :
    stateAt (start + count) =
      runRecamanSteps (start + 1) (stateAt start) count := by
  induction count generalizing start with
  | zero => simp [runRecamanSteps]
  | succ count ih =>
      rw [show start + (count + 1) = (start + 1) + count by omega]
      rw [ih]
      simp only [stateAt_succ]
      simp [runRecamanSteps, Nat.add_comm, Nat.add_left_comm]

/-- A checked chunk preserves a reusable authenticated checkpoint. -/
theorem checkedTraceChunk_represents {start : Nat} {machine : TraceMachine}
    {reasons : List TraceStepReason}
    (hstart : machine.Represents (stateAt start))
    (hcheck : checkTraceChunk (start + 1) machine reasons = true) :
    (replayTraceChunk (start + 1) machine reasons).Represents
      (stateAt (start + reasons.length)) := by
  have hvalid := (checkTraceChunk_eq_true_iff _ _ _).1 hcheck
  have hrep := validTraceChunk_represents hstart hvalid
  rw [← stateAt_add_eq_runRecamanSteps] at hrep
  exact hrep

/-- Kernel-sound endpoint equality extracted from a checked chunk. -/
theorem checkedTraceChunk_value {start : Nat} {machine : TraceMachine}
    {reasons : List TraceStepReason}
    (hstart : machine.Represents (stateAt start))
    (hcheck : checkTraceChunk (start + 1) machine reasons = true) :
    a (start + reasons.length) =
      (replayTraceChunk (start + 1) machine reasons).value := by
  exact (checkedTraceChunk_represents hstart hcheck).value_eq.symm

/-- Checked chunks compose without rebuilding the ordinary history at their
boundaries.  This is the reusable theorem needed for deep checkpoint chains. -/
theorem checkedTraceChunks_represents {start : Nat} {machine : TraceMachine}
    {chunks : List (List TraceStepReason)}
    (hstart : machine.Represents (stateAt start))
    (hcheck : checkTraceChunks start machine chunks = true) :
    (replayTraceChunks start machine chunks).Represents
      (stateAt (start + traceChunksLength chunks)) := by
  induction chunks generalizing start machine with
  | nil => simpa [checkTraceChunks, replayTraceChunks, traceChunksLength] using hstart
  | cons chunk chunks ih =>
      have hparts := Bool.and_eq_true_iff.mp hcheck
      have hcheckpoint := checkedTraceChunk_represents hstart hparts.1
      have htail := ih hcheckpoint hparts.2
      simpa [replayTraceChunks, traceChunksLength, Nat.add_assoc] using htail

/-- Endpoint equality for a composed list of checked chunks. -/
theorem checkedTraceChunks_value {start : Nat} {machine : TraceMachine}
    {chunks : List (List TraceStepReason)}
    (hstart : machine.Represents (stateAt start))
    (hcheck : checkTraceChunks start machine chunks = true) :
    a (start + traceChunksLength chunks) =
      (replayTraceChunks start machine chunks).value := by
  exact (checkedTraceChunks_represents hstart hcheck).value_eq.symm

/-- A checked blocked reason feeds directly into the existing `SeenBefore`
API.  The checker itself remains free of quantified history propositions. -/
theorem blockedTraceReason_seenBefore {n witnessTime : Nat}
    {machine : TraceMachine}
    (hrep : machine.Represents (stateAt n))
    (hvalid : ValidTraceStep (n + 1) machine (.blocked witnessTime)) :
    SeenBefore a (a n - (n + 1)) (n + 1) := by
  have hseen := hvalid.2.2.2.1
  apply seenBefore_succ_iff.mpr
  unfold a
  rw [← hrep.value_eq]
  exact (hrep.seen_iff _).1 hseen

/-- The same blocked bit can be converted through the existing history API
to a first-occurrence certificate. -/
theorem blockedTraceReason_has_firstAt {n witnessTime : Nat}
    {machine : TraceMachine}
    (hrep : machine.Represents (stateAt n))
    (hvalid : ValidTraceStep (n + 1) machine (.blocked witnessTime)) :
    ∃ firstTime, firstTime ≤ n ∧ FirstAt a (a n - (n + 1)) firstTime := by
  apply history_member_has_firstAt
  have hseen := hvalid.2.2.2.1
  unfold a
  rw [← hrep.value_eq]
  exact (hrep.seen_iff _).1 hseen

/-! ## Small kernel-checked prototype

The first fifteen transitions exercise all three reason constructors. The
proof uses ordinary kernel reduction through `decide`. -/

def firstFifteenTrace : List TraceStepReason :=
  [.nonpositive, .nonpositive, .nonpositive, .fresh, .nonpositive,
    .blocked 1, .blocked 3, .fresh, .blocked 2, .fresh,
    .nonpositive, .fresh, .nonpositive, .fresh, .nonpositive]

theorem firstFifteenTrace_checked :
    checkTraceChunk 1 (initialTraceMachine 64) firstFifteenTrace = true := by
  decide

theorem firstFifteenTrace_value : a 15 = 24 := by
  have hstart : (initialTraceMachine 64).Represents (stateAt 0) :=
    initialTraceMachine_represents 64 (by decide)
  have hvalue := checkedTraceChunk_value hstart firstFifteenTrace_checked
  simpa [firstFifteenTrace, replayTraceChunk, applyTraceReason,
    traceNextValue, TraceMachine.record, initialTraceMachine] using hvalue

/-- The same trace split into three independently checkable checkpoints. -/
def firstFifteenChunks : List (List TraceStepReason) :=
  [[.nonpositive, .nonpositive, .nonpositive, .fresh, .nonpositive],
    [.blocked 1, .blocked 3, .fresh, .blocked 2, .fresh],
    [.nonpositive, .fresh, .nonpositive, .fresh, .nonpositive]]

theorem firstFifteenChunks_checked :
    checkTraceChunks 0 (initialTraceMachine 64) firstFifteenChunks = true := by
  decide

theorem firstFifteenChunks_value : a 15 = 24 := by
  have hstart : (initialTraceMachine 64).Represents (stateAt 0) :=
    initialTraceMachine_represents 64 (by decide)
  have hvalue := checkedTraceChunks_value hstart firstFifteenChunks_checked
  simpa [firstFifteenChunks, traceChunksLength, replayTraceChunks,
    replayTraceChunk, applyTraceReason, traceNextValue, TraceMachine.record,
    initialTraceMachine] using hvalue



end Recaman
