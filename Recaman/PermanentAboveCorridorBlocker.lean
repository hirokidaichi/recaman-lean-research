import Recaman.PermanentAboveCorridorBalance

namespace Recaman

noncomputable section

/-! # The blocker behind the terminal forced crossing

The final return upcross is forced because its subtraction candidate is
either nonpositive or already present in the historical orbit.  In the
first case the strict crossing lies in an explicit double-clock strip.  In
the second case a positive, strictly smaller below-target value has a first
occurrence no later than the return predecessor.
-/

/-- Typed reason why the final subtraction of a strict terminal crossing is
blocked. -/
inductive StrictTerminalCrossingBalance.ForcedReason
    {target returnTime : Nat}
    (balance : StrictTerminalCrossingBalance target returnTime) : Prop
  | insufficient_value
      (predecessor_le_clock : a returnTime ≤ returnTime + 1)
      (endpoint_le_twice_clock :
        a (returnTime + 1) ≤ 2 * (returnTime + 1))
      (target_lt_twice_clock : target < 2 * (returnTime + 1)) :
      balance.ForcedReason
  | historical_blocker
      (candidate firstTime : Nat)
      (candidate_eq : candidate = a returnTime - (returnTime + 1))
      (candidate_positive : 0 < candidate)
      (candidate_first : FirstAt a candidate firstTime)
      (firstTime_lt_return : firstTime < returnTime)
      (candidate_below_predecessor : candidate < a returnTime)
      (candidate_below_target : candidate < target) :
      balance.ForcedReason

/-- Every strict terminal crossing exposes either the double-clock numeric
strip or a concrete earlier historical blocker. -/
theorem StrictTerminalCrossingBalance.forcedReason
    {target returnTime : Nat}
    (h : StrictTerminalCrossingBalance target returnTime) :
    h.ForcedReason := by
  have hpredecessorBelow := h.predecessor_below
  by_cases hpositive : returnTime + 1 < a returnTime
  · have hseen : a returnTime - (returnTime + 1) ∈
        valuesThrough returnTime := by
      have hstatePositive : returnTime + 1 < (stateAt returnTime).value := by
        simpa [a] using hpositive
      rcases (not_canSubtract_iff_nonpositive_or_seen.mp
          h.forced_addition) with hnonpositive | hseen
      · exact False.elim (hnonpositive hstatePositive)
      · simpa [a, valuesThrough] using hseen
    rcases history_member_has_firstAt hseen with
      ⟨firstTime, hfirstTimeLe, hfirst⟩
    have hcandidateBelow :
        a returnTime - (returnTime + 1) < a returnTime := by omega
    have hfirstTimeLt : firstTime < returnTime := by
      have hfirstTimeNe : firstTime ≠ returnTime := by
        intro hequal
        have hfirstValue := hfirst.1
        rw [hequal] at hfirstValue
        omega
      omega
    exact .historical_blocker
      (a returnTime - (returnTime + 1)) firstTime rfl (by omega)
      hfirst hfirstTimeLt hcandidateBelow (by omega)
  · have hpredecessorLe : a returnTime ≤ returnTime + 1 := by omega
    have hendpointLe : a (returnTime + 1) ≤
        2 * (returnTime + 1) := by
      rw [h.final_equation]
      omega
    have htargetLt : target < 2 * (returnTime + 1) :=
      Nat.lt_of_lt_of_le h.endpoint_above hendpointLe
    exact .insufficient_value hpredecessorLe hendpointLe htargetLt

/-- The normalized branch-independent terminal interface exposes the same
forced reason without reopening the immediate/all-forced split. -/
theorem NormalizedTerminalCrossingData.forcedReason
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : NormalizedTerminalCrossingData source) :
    h.balance.ForcedReason :=
  h.balance.forcedReason

/-- Direct discharge-level adapter for the terminal forced reason. -/
theorem PermanentTailDischargeReturnCertificate.terminalForcedReason
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    h.strictTerminalCrossingBalance.ForcedReason :=
  h.strictTerminalCrossingBalance.forcedReason

end

end Recaman
