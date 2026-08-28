import Std

namespace Recaman

/-- The current value together with the values that have already occurred.
The list is kept in reverse chronological order; multiplicities are harmless. -/
structure State where
  value : Nat
  seen : List Nat
deriving Repr, DecidableEq

/-- Initial state of the Recamán sequence: a₀ = 0. -/
def initial : State := ⟨0, [0]⟩

/-- At step n, subtraction is allowed precisely when it stays positive and
lands on a value that has not occurred before. -/
def CanSubtract (n : Nat) (state : State) : Prop :=
  n < state.value ∧ state.value - n ∉ state.seen

instance (n : Nat) (state : State) : Decidable (CanSubtract n state) :=
  by
    unfold CanSubtract
    infer_instance

/-- The numeric part of one Recamán step. -/
def nextValue (n : Nat) (state : State) : Nat :=
  if CanSubtract n state then state.value - n else state.value + n

/-- Perform step n and record the new value. -/
def step (n : Nat) (state : State) : State :=
  let value := nextValue n state
  ⟨value, value :: state.seen⟩

/-- State after n Recamán steps. -/
def stateAt : Nat → State
  | 0 => initial
  | n + 1 => step (n + 1) (stateAt n)

/-- The usual Recamán sequence. -/
def a (n : Nat) : Nat := (stateAt n).value

/-- The values a₀ through aₙ, in reverse chronological order. -/
def valuesThrough (n : Nat) : List Nat := (stateAt n).seen

@[simp] theorem stateAt_succ (n : Nat) :
    stateAt (n + 1) = step (n + 1) (stateAt n) := rfl

theorem recurrence (n : Nat) :
    a (n + 1) =
      if CanSubtract (n + 1) (stateAt n) then
        a n - (n + 1)
      else
        a n + (n + 1) := by
  rfl

@[simp] theorem initial_value : initial.value = 0 := rfl
@[simp] theorem initial_seen : initial.seen = [0] := rfl

@[simp] theorem step_seen (n : Nat) (state : State) :
    (step n state).seen = nextValue n state :: state.seen := rfl

theorem old_seen_mem_step_seen {x n : Nat} {state : State}
    (h : x ∈ state.seen) : x ∈ (step n state).seen := by
  simp only [step_seen, List.mem_cons]
  exact Or.inr h

@[simp] theorem step_value_mem_seen (n : Nat) (state : State) :
    (step n state).value ∈ (step n state).seen := by
  simp [step]

theorem current_mem_valuesThrough (n : Nat) : a n ∈ valuesThrough n := by
  cases n with
  | zero => simp [a, valuesThrough, stateAt, initial]
  | succ n =>
      simpa [a, valuesThrough, stateAt] using
        step_value_mem_seen (n + 1) (stateAt n)

theorem valuesThrough_persist {x n : Nat} (h : x ∈ valuesThrough n) :
    x ∈ valuesThrough (n + 1) := by
  simpa [valuesThrough, stateAt] using
    old_seen_mem_step_seen (n := n + 1) (state := stateAt n) h

theorem step_of_subtract {n : Nat} {state : State}
    (h : CanSubtract n state) :
    step n state = ⟨state.value - n, (state.value - n) :: state.seen⟩ := by
  simp [step, nextValue, h]

theorem step_of_seen {n : Nat} {state : State}
    (hseen : state.value - n ∈ state.seen) :
    step n state = ⟨state.value + n, (state.value + n) :: state.seen⟩ := by
  have hnot : ¬ CanSubtract n state := by
    intro h
    exact h.2 hseen
  simp [step, nextValue, hnot]

theorem step_of_nonpositive {n : Nat} {state : State}
    (h : ¬ n < state.value) :
    step n state = ⟨state.value + n, (state.value + n) :: state.seen⟩ := by
  have hnot : ¬ CanSubtract n state := by
    intro hcan
    exact h hcan.1
  simp [step, nextValue, hnot]

/-- Executable sanity check against the standard initial terms. -/
example : (List.range 16).map a =
    [0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24] := by
  decide

end Recaman
