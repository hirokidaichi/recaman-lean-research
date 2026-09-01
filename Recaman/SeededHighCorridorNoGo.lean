import Recaman.ForcedCandidateReuseBalance

namespace Recaman

/-! # Arbitrarily long seeded high-candidate corridors

The local `Basic.step` rule does not impose a uniform finite bound on a
high-candidate corridor.  For every requested length we can seed the finite
history with exactly the blockers needed by an all-addition trace.  Target
`1` remains absent, every exposed candidate is above it, and every transition
is a genuine forced `step` transition.

This construction is deliberately not claimed reachable from `initial`.
It isolates the global provenance of the standard history as the missing
input in any attempted eventual-high contradiction.
-/

/-- Candidate exposed at local time `time` by the intended all-addition
trace of requested length `length`. -/
def seededHighCandidate (length time : Nat) : Nat :=
  length + 2 + upperTri time - (time + 1)

/-- The finite seed contains the starting value and every blocker needed by
the requested trace. -/
def seededHighBaseSeen (length : Nat) : List Nat :=
  (length + 2) ::
    (List.range length).map (seededHighCandidate length)

/-- Initial seeded state for a corridor of the requested finite length. -/
def seededHighInitial (length : Nat) : State :=
  ⟨length + 2, seededHighBaseSeen length⟩

/-- Run the real `Basic.step` kernel at clocks `1,2,...` from the seed. -/
def seededHighState (length : Nat) : Nat → State
  | 0 => seededHighInitial length
  | time + 1 => step (time + 1) (seededHighState length time)

theorem seededHighCandidate_mem_baseSeen
    {length time : Nat} (htime : time < length) :
    seededHighCandidate length time ∈ seededHighBaseSeen length := by
  apply List.mem_cons.mpr
  right
  apply List.mem_map.mpr
  exact ⟨time, List.mem_range.mpr htime, rfl⟩

theorem one_lt_seededHighCandidate
    {length time : Nat} (htime : time < length) :
    1 < seededHighCandidate length time := by
  simp only [seededHighCandidate]
  omega

theorem one_not_mem_seededHighBaseSeen (length : Nat) :
    1 ∉ seededHighBaseSeen length := by
  intro hone
  rcases List.mem_cons.mp hone with honeStart | honeCandidate
  · omega
  · rcases List.mem_map.mp honeCandidate with ⟨time, htime, hone⟩
    have htime' := List.mem_range.mp htime
    have habove := one_lt_seededHighCandidate htime'
    omega

/-- Value, seed-history persistence, and target omission along the seeded
trace. -/
structure SeededHighInvariant (length time : Nat) : Prop where
  value_eq : (seededHighState length time).value =
    length + 2 + upperTri time
  base_seen : ∀ x, x ∈ seededHighBaseSeen length →
    x ∈ (seededHighState length time).seen
  one_missing : 1 ∉ (seededHighState length time).seen

theorem seededHighInvariant
    {length time : Nat} (htime : time ≤ length) :
    SeededHighInvariant length time := by
  induction time with
  | zero =>
      exact {
        value_eq := by simp [seededHighState, seededHighInitial, upperTri]
        base_seen := by
          intro x hx
          simpa [seededHighState, seededHighInitial] using hx
        one_missing := by
          simpa [seededHighState, seededHighInitial] using
            one_not_mem_seededHighBaseSeen length
      }
  | succ time ih =>
      have hprevious : time ≤ length := by omega
      have hstrict : time < length := by omega
      have previous := ih hprevious
      have hcandidateBase := seededHighCandidate_mem_baseSeen hstrict
      have hcandidateSeen := previous.base_seen _ hcandidateBase
      have hcandidateEquation :
          (seededHighState length time).value - (time + 1) =
            seededHighCandidate length time := by
        rw [previous.value_eq]
        rfl
      have hattemptSeen :
          (seededHighState length time).value - (time + 1) ∈
            (seededHighState length time).seen := by
        rw [hcandidateEquation]
        exact hcandidateSeen
      have hstep := step_of_seen (n := time + 1) hattemptSeen
      have hstate :
          seededHighState length (time + 1) =
            ⟨(seededHighState length time).value + (time + 1),
              ((seededHighState length time).value + (time + 1)) ::
                (seededHighState length time).seen⟩ := by
        simpa [seededHighState] using hstep
      constructor
      · rw [hstate]
        simp only
        rw [previous.value_eq, upperTri_succ]
        omega
      · intro x hx
        rw [hstate]
        exact List.mem_cons.mpr (Or.inr (previous.base_seen x hx))
      · rw [hstate]
        intro hone
        rcases List.mem_cons.mp hone with honeValue | honePrevious
        · have hvalue := previous.value_eq
          omega
        · exact previous.one_missing honePrevious

/-- For every finite requested length, target `1` stays missing and every
next candidate is positive, above the target, already in history, and hence
forces a genuine addition under `Basic.step`. -/
theorem arbitrarilyLong_seededHigh_forcedAdditionCorridor
    (length : Nat) :
    ∀ time, time < length →
      1 ∉ (seededHighState length time).seen ∧
      1 < (seededHighState length time).value - (time + 1) ∧
      ¬ CanSubtract (time + 1) (seededHighState length time) ∧
      (step (time + 1) (seededHighState length time)).value =
        (seededHighState length time).value + (time + 1) := by
  intro time htime
  have invariant := seededHighInvariant (Nat.le_of_lt htime)
  have hcandidateBase := seededHighCandidate_mem_baseSeen htime
  have hcandidateSeen := invariant.base_seen _ hcandidateBase
  have hcandidateEquation :
      (seededHighState length time).value - (time + 1) =
        seededHighCandidate length time := by
    rw [invariant.value_eq]
    rfl
  have hattemptSeen :
      (seededHighState length time).value - (time + 1) ∈
        (seededHighState length time).seen := by
    rw [hcandidateEquation]
    exact hcandidateSeen
  have hforced : ¬ CanSubtract (time + 1)
      (seededHighState length time) := by
    intro hcan
    exact hcan.2 hattemptSeen
  have hstep := step_of_seen (n := time + 1) hattemptSeen
  refine ⟨invariant.one_missing, ?_, hforced, ?_⟩
  · rw [hcandidateEquation]
    exact one_lt_seededHighCandidate htime
  · simpa using congrArg State.value hstep

end Recaman
