import Recaman.CrossingRefinedBoundary

namespace Recaman

/-! # Future-downcross exit from a ready crossing

The crossing rank boundary says that a non-crossing exit must consume a new
below-target history value.  A downcross after the stored crossing horizon
does exactly that: forced addition cannot move downward, so the endpoint is
a fresh legal-subtraction value below the target.  The resulting strict
budget drop permits an extended-history child whose representative is the
original above-target crossing endpoint.
-/

/-- A crossing certificate together with the target-ready clock retained by
all currently audited refined producers. -/
structure ReadyCrossingSearchInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop where
  crossing : CrossingSearchInvariant target node
  horizon_ready : target ≤ node.horizon + 1

/-- A genuine downcross transition no earlier than a stored history horizon. -/
structure FutureDowncrossStep
    (target historyHorizon time : Nat) : Prop where
  horizon_le_time : historyHorizon ≤ time
  start_at_or_above : target ≤ a time
  endpoint_below : a (time + 1) < target

/-- A future downcross endpoint is fresh relative to the old crossing
horizon, hence strictly lowers its missing-below-target budget. -/
theorem FutureDowncrossStep.strict_budget_drop
    {target historyHorizon time : Nat}
    (h : FutureDowncrossStep target historyHorizon time) :
    missingBelowCount target (time + 1) <
      missingBelowCount target historyHorizon := by
  have hcan : CanSubtract (time + 1) (stateAt time) := by
    by_cases hcan : CanSubtract (time + 1) (stateAt time)
    · exact hcan
    · have hadd := a_succ_of_not_canSubtract hcan
      have hstart := h.start_at_or_above
      have hendpoint := h.endpoint_below
      omega
  have hstep := a_succ_of_canSubtract hcan
  have hfreshAtTime : a (time + 1) ∉ valuesThrough time := by
    rw [hstep]
    exact hcan.2
  have hfreshAtHorizon : a (time + 1) ∉
      valuesThrough historyHorizon := by
    intro hseen
    exact hfreshAtTime (valuesThrough_mono h.horizon_le_time hseen)
  exact missingBelowCount_strict_of_new h.endpoint_below
    (Nat.le_trans h.horizon_le_time (by omega)) hfreshAtHorizon
    (current_mem_valuesThrough (time + 1))

/-- Once a ready crossing has a future downcross after its stored horizon,
it either hits the target at the downcross source or exits to an
extended-history normal child through the forced budget decrease. -/
theorem ReadyCrossingSearchInvariant.refinedStep_of_futureDowncross
    {target : Nat} {node : PhaseSearchNode} {time : Nat}
    (h : ReadyCrossingSearchInvariant target node)
    (hdown : FutureDowncrossStep target node.horizon time) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child node := by
  by_cases hequal : a time = target
  · exact Or.inl ⟨time, hequal⟩
  rcases h.crossing with
    ⟨oldAnchor, crossingTime, quotient, remainder, hcertificate⟩
  let child : PhaseSearchNode :=
    ⟨time + 1, a (crossingTime + 1), .normal,
      a (crossingTime + 1)⟩
  have hrepresentativeLe : crossingTime + 1 ≤ time + 1 := by
    exact Nat.le_trans
      (Nat.le_of_lt hcertificate.recovery.crossing_before_horizon)
      (Nat.le_trans hdown.horizon_le_time (by omega))
  have hextended : ExtendedHistoryNormalInvariant target child :=
    ⟨crossingTime + 1, quotient, remainder, {
      target_positive := hcertificate.target_positive
      node_eq := rfl
      representative_le_horizon := hrepresentativeLe
      horizon_time_ready := by
        have htimeReady : target ≤ time + 1 :=
          Nat.le_trans h.horizon_ready
            (Nat.add_le_add_right hdown.horizon_le_time 1)
        simpa [child] using Nat.le_trans htimeReady (by omega)
      target_le_value :=
        Nat.le_of_lt hcertificate.recovery.crossing.2.1
      coordinates := hcertificate.recovery.coordinates
    }⟩
  have hprogress : PhaseSearchProgress target child node := by
    exact Prod.Lex.left _ _ hdown.strict_budget_drop
  exact Or.inr ⟨child, Or.inr (Or.inl hextended), hprogress⟩

end Recaman
