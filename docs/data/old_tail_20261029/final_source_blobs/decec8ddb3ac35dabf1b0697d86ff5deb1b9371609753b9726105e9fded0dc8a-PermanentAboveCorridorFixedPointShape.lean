import Recaman.PermanentAboveCorridorFixedPointFloor

namespace Recaman

noncomputable section

/-! # Shape lemmas of the fixed-point core

Node reproduction determines the parent completely: it is the ready-crossing
shape at its own crossing value.  Consequently all fixed-point cores over
one parent share the same crossing value — the parent anchor — even when
their crossing clocks differ, and any two clocks of cores over the same
parent carry equal orbit values.  These small lemmas are the working API
for analyzing repeated or coexisting fixed points.
-/

namespace TailFixedPointCore

variable {target : Nat} {parent : PhaseSearchNode} {crossingTime : Nat}

/-- The parent of a fixed-point core is the ready-crossing shape at its own
crossing value. -/
theorem parent_shape
    (core : TailFixedPointCore target parent crossingTime) :
    parent = ⟨parent.horizon, a crossingTime, .normal, a crossingTime⟩ :=
  core.node_reproduction.symm

/-- The parent phase is normal. -/
theorem parent_phase
    (core : TailFixedPointCore target parent crossingTime) :
    parent.phase = .normal := by
  have h := congrArg PhaseSearchNode.phase core.node_reproduction
  simpa [terminalPredecessorCrossingNode] using h.symm

/-- The parent local measure coincides with the anchor. -/
theorem parent_localMeasure
    (core : TailFixedPointCore target parent crossingTime) :
    parent.localMeasure = parent.anchorParent := by
  have hlocal := congrArg PhaseSearchNode.localMeasure
    core.node_reproduction
  have hanchor := core.anchor_eq
  have hvalue : a crossingTime = parent.localMeasure := by
    simpa [terminalPredecessorCrossingNode] using hlocal
  omega

/-- Any two fixed-point cores over the same parent carry the same crossing
value, even at different clocks. -/
theorem crossing_value_unique
    {otherTime : Nat}
    (core : TailFixedPointCore target parent crossingTime)
    (other : TailFixedPointCore target parent otherTime) :
    a crossingTime = a otherTime := by
  rw [core.anchor_eq, other.anchor_eq]

/-- Distinct clocks of two cores over one parent are an exact value
recurrence: the same below-target value crosses twice by forced addition. -/
theorem exists_value_recurrence
    {otherTime : Nat}
    (core : TailFixedPointCore target parent crossingTime)
    (other : TailFixedPointCore target parent otherTime)
    (hne : crossingTime ≠ otherTime) :
    a crossingTime = a otherTime ∧
      a (crossingTime + 1) ≠ a (otherTime + 1) := by
  refine ⟨core.crossing_value_unique other, ?_⟩
  have hforced := core.forced
  have hforced' := other.forced
  have hvalue := core.crossing_value_unique other
  intro hcontra
  rw [hforced, hforced', hvalue] at hcontra
  omega

end TailFixedPointCore

end

end Recaman
