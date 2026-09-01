import Recaman.EventualHighCorridorSupply
import Recaman.CoordinateDynamics

namespace Recaman

/-! # Birth of corridor supplier values

The supplier theorem locates, for every late corridor forced addition whose
candidate clears the pre-cutoff value hull, a corridor-internal time that
carries exactly the candidate value.  This module sharpens that landing to
the candidate's *first* occurrence and then classifies the step that created
it.

First, the supplier upgrade: history membership yields a first occurrence,
and the same hull comparison that confined the supplier confines the birth
clock strictly past the cutoff, where the corridor value law and the hull
bound apply verbatim.  Second, an unconditional dichotomy: any value born at
a positive clock was produced by the actual step, so it is either the
subtraction candidate of the previous clock (and the subtraction was taken)
or the addition output `a t + (t + 1)`, which dominates its own clock.
Combining the two, every late forced addition's candidate was born inside
the corridor either by an earlier *taken* subtraction — re-exposing that
clock's own candidate — or as an addition output.

In the subtraction branch the birth equation says the candidate value equals
`nextSubtractionCandidate t` for the strictly earlier corridor clock `t`, so
the classification can in principle be iterated: each subtraction-born
candidate points at an earlier candidate, and the resulting candidate
ancestry chain walks backwards through the corridor until it exits through
an addition birth or through the finite pre-cutoff hull.  Formalizing that
iteration is the next research target; here we only record the single step.
-/

/-- **Birth supplier.**  A late corridor forced addition whose candidate
clears the pre-cutoff hull is supplied by the candidate's *first* occurrence,
and that birth clock lies strictly inside the corridor, obeys the corridor
value law, and is bounded by its own value hull. -/
theorem corridor_forcedAddition_birth
    {target cutoff n : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff + 1 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbig : upperTri cutoff < nextSubtractionCandidate n) :
    ∃ t, cutoff < t ∧ t ≤ n ∧
      FirstAt a (nextSubtractionCandidate n) t ∧
      t + 1 + target < nextSubtractionCandidate n ∧
      nextSubtractionCandidate n ≤ upperTri t := by
  classical
  have hseen := corridor_forcedAddition_candidate_seen hhigh hn hnot
  rcases history_member_has_firstAt hseen with ⟨f, hfn, hfirst⟩
  have hval : a f = nextSubtractionCandidate n := hfirst.1
  have hbound := a_le_upperTri f
  have hfcut : cutoff < f := by
    by_cases hle : f ≤ cutoff
    · exfalso
      have hmono := upperTri_mono hle
      omega
    · omega
  have hlaw := corridor_value_law hhigh hfcut
  exact ⟨f, hfcut, hfn, hfirst, by omega, by omega⟩

/-- **Birth-step dichotomy.**  A first occurrence at a positive clock was
produced by the actual step: either the step subtracted, and the value is
the previous clock's subtraction candidate, or the step added, and the value
is the addition output, which dominates its own clock. -/
theorem firstAt_succ_birth_dichotomy
    {v t : Nat}
    (hfirst : FirstAt a v (t + 1)) :
    (CanSubtract (t + 1) (stateAt t) ∧ v = nextSubtractionCandidate t) ∨
      (¬ CanSubtract (t + 1) (stateAt t) ∧ v = a t + (t + 1) ∧ t + 1 ≤ v) := by
  classical
  have hval := hfirst.1
  by_cases hcan : CanSubtract (t + 1) (stateAt t)
  · left
    refine ⟨hcan, ?_⟩
    have hstep := a_succ_of_canSubtract hcan
    simp only [nextSubtractionCandidate]
    omega
  · right
    have hstep := a_succ_of_not_canSubtract hcan
    exact ⟨hcan, by omega, by omega⟩

/-- **Corridor birth classification.**  Every late corridor forced addition
whose candidate clears the pre-cutoff hull traces back to a birth step at a
corridor-internal clock `t + 1`: the candidate is either the subtraction
candidate of clock `t` — and that subtraction was taken — or the addition
output of clock `t`.  Either way the birth clock sits strictly below the
candidate minus the missing target. -/
theorem corridor_forcedAddition_birth_classified
    {target cutoff n : Nat}
    (hhigh : ∀ m, cutoff ≤ m → target < nextSubtractionCandidate (m + 1))
    (hn : cutoff + 1 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hbig : upperTri cutoff < nextSubtractionCandidate n) :
    ∃ t, cutoff ≤ t ∧ t + 1 ≤ n ∧
      t + 2 + target < nextSubtractionCandidate n ∧
      ((CanSubtract (t + 1) (stateAt t) ∧
          nextSubtractionCandidate n = nextSubtractionCandidate t) ∨
        (¬ CanSubtract (t + 1) (stateAt t) ∧
          nextSubtractionCandidate n = a t + (t + 1))) := by
  rcases corridor_forcedAddition_birth hhigh hn hnot hbig with
    ⟨b, hbcut, hbn, hfirst, hcone, _hhull⟩
  obtain ⟨t, rfl⟩ : ∃ t, b = t + 1 := ⟨b - 1, by omega⟩
  rcases firstAt_succ_birth_dichotomy hfirst with hsub | hadd
  · exact ⟨t, by omega, hbn, by omega, Or.inl ⟨hsub.1, hsub.2⟩⟩
  · exact ⟨t, by omega, hbn, by omega, Or.inr ⟨hadd.1, hadd.2.1⟩⟩

end Recaman
