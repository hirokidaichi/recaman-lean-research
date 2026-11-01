import Recaman.PermanentAboveCorridorIterationClosure

namespace Recaman

noncomputable section

/-! # Numeric pinning of the exact replay fixed point

An exact replay stores three equalities: the installed anchor equals the
parent anchor, the selected crossing time equals the old crossing time, and
the old crossing is chronologically eligible from the fresh downcross
endpoint.  Together with the certified selection bounds these force the
canonical return itself onto the old crossing: the discharge closes a
literal cycle `endpoint → return = old crossing`.

This module derives that cycle closure and its numeric consequences: the
crossing clock is strictly below the crossing value, the terminal blocker
first occurs strictly before the crossing, the crossing step is an explicit
forced addition across the target, and — because a ready crossing node is
determined by its horizon and anchor — the installed node is literally the
parent node.  The successor discharge therefore transports back onto the
same parent with the same old crossing cursor: the replay is a genuine
self-map fixed point at node level, not merely at rank level.
-/

/-- Discharges transport along node equalities without moving their old
crossing cursor. -/
theorem PermanentTailDischargeReturnCertificate.exists_transport_of_node_eq
    {target start : Nat} {nodeA nodeB : PhaseSearchNode}
    (hnode : nodeA = nodeB)
    (d : PermanentTailDischargeReturnCertificate target start nodeA) :
    ∃ d' : PermanentTailDischargeReturnCertificate target start nodeB,
      d'.oldCrossingTime = d.oldCrossingTime := by
  cases hnode
  exact ⟨d, rfl⟩

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- At an exact replay the canonical return time is the old crossing time. -/
theorem return_eq_oldCrossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    source.returnTime = source.oldCrossingTime := by
  have hle := source.returnTime_le_oldCrossingTime r.eligible
  have hcrossing := r.crossing.crossingTime_le_return
  have htime := r.time_eq
  omega

/-- Equivalently, the return time is the selected crossing time itself. -/
theorem return_eq_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    source.returnTime = r.crossingTime := by
  have hle := source.returnTime_le_oldCrossingTime r.eligible
  have hcrossing := r.crossing.crossingTime_le_return
  have htime := r.time_eq
  omega

/-- The fresh downcross endpoint sits at or before the selected crossing. -/
theorem endpoint_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    source.downTime + 1 ≤ r.crossingTime := by
  have heligible := r.eligible
  have htime := r.time_eq
  omega

/-- Cycle closure: the canonical first upcrossing from the fresh downcross
endpoint is exactly the old crossing. -/
theorem canonicalReturn_is_oldCrossing
    (r : TerminalExactDischargeReplayCertificate source) :
    FirstWeakUpcrossingStep target (source.downTime + 1)
      source.oldCrossingTime := by
  have h := source.return_crossing
  rwa [r.return_eq_oldCrossingTime] at h

/-- The terminal blocker first occurs strictly before the crossing. -/
theorem firstTime_lt_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    r.firstTime < r.crossingTime := by
  have hlt := r.historical.blocker.firstTime_lt_return
  have hret := r.return_eq_crossingTime
  omega

/-- The replay crossing carries a value strictly above its own clock. -/
theorem clock_lt_crossingValue
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime + 1 < a r.crossingTime := by
  have hpos := r.historical.blocker.candidate_positive
  have heq := r.historical.blocker.candidate_eq
  have hret := r.return_eq_crossingTime
  rw [hret] at heq
  omega

/-- The terminal blocker candidate is the exact subtraction defect at the
crossing clock. -/
theorem candidate_eq_at_crossing
    (r : TerminalExactDischargeReplayCertificate source) :
    r.candidate = a r.crossingTime - (r.crossingTime + 1) := by
  have heq := r.historical.blocker.candidate_eq
  have hret := r.return_eq_crossingTime
  rw [hret] at heq
  exact heq

/-- The crossing step is an explicit forced addition. -/
theorem forced_addition_at_crossing
    (r : TerminalExactDischargeReplayCertificate source) :
    a (r.crossingTime + 1) = a r.crossingTime + (r.crossingTime + 1) := by
  have h := source.old_crossing.forced_addition
  rw [← r.time_eq] at h
  exact a_succ_of_not_canSubtract h

/-- The crossing straddles the target: below before, at-or-above after. -/
theorem crossing_straddles_target
    (r : TerminalExactDischargeReplayCertificate source) :
    a r.crossingTime < target ∧ target ≤ a (r.crossingTime + 1) := by
  refine ⟨r.crossing.first_crossing.crossing.below, ?_⟩
  have h := source.old_crossing.endpoint_ge
  rwa [← r.time_eq] at h

/-- Node-level fixed point: a ready crossing node is determined by its
horizon and anchor, so the installed node is literally the parent. -/
theorem installed_node_eq
    (r : TerminalExactDischargeReplayCertificate source) :
    terminalPredecessorCrossingNode parent r.crossingTime = parent := by
  rcases source.combined.crossing.ready_crossing.crossing with
    ⟨oldAnchor, oldTime, quotient, remainder, hold⟩
  have hanchor : parent.anchorParent = a oldTime := by
    simpa using congrArg PhaseSearchNode.anchorParent hold.node_eq
  show (⟨parent.horizon, a r.crossingTime, .normal, a r.crossingTime⟩ :
    PhaseSearchNode) = parent
  rw [r.anchor_eq, hanchor]
  exact hold.node_eq.symm

/-- The successor discharge transports onto the very same parent node with
the same old crossing cursor: the replay is a self-map fixed point. -/
theorem exists_nextOnParent
    (r : TerminalExactDischargeReplayCertificate source) :
    ∃ next : PermanentTailDischargeReturnCertificate target start parent,
      next.oldCrossingTime = source.oldCrossingTime := by
  obtain ⟨d', hd'⟩ :=
    PermanentTailDischargeReturnCertificate.exists_transport_of_node_eq
      r.installed_node_eq r.next.discharge
  refine ⟨d', ?_⟩
  rw [hd', r.next.old_crossing_time_eq]
  exact r.time_eq

end TerminalExactDischargeReplayCertificate

end

end Recaman
