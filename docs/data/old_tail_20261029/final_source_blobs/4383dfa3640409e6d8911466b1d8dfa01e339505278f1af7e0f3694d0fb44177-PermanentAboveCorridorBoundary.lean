import Recaman.PermanentAboveCorridorSuffix

namespace Recaman

noncomputable section

/-! # A legal final corridor step would hit the missing target

If a legal subtraction at time `n` is immediately followed by forced
addition at time `n+1`, the existing recurrence theorem gives
`a (n+2) = a n + 1`.  When `a n < target` but the second step is a weak
upcrossing, this successor is forced to equal the target.

Consequently, under missing-target provenance, no legal internal corridor
subtraction can land exactly on the canonical return predecessor.  Every
legal suffix child remains strictly before the return; if it has no later
legal endpoint, its remaining suffix is all-forced.
-/

/-- Exact-target consequence of a legal-subtraction / forced-addition
rebound from a below-target source. -/
theorem legalSubtraction_forcedAddition_crossing_hits_target
    {target time : Nat}
    (hbelow : a time < target)
    (hsub : CanSubtract (time + 1) (stateAt time))
    (hadd : ¬ CanSubtract (time + 2) (stateAt (time + 1)))
    (hcross : target ≤ a (time + 2)) :
    a (time + 2) = target := by
  have hrebound := a_sub_then_add_eq_succ hsub hadd
  omega

/-- A missing target forbids a legal internal subtraction from landing on
the canonical return time. -/
theorem CanonicalBelowCorridorSuffix.internalSubtraction_ne_return
    {target endpointTime returnTime time : Nat}
    (h : CanonicalBelowCorridorSuffix target endpointTime returnTime)
    (htargetMissing : ¬ ∃ witness, a witness = target)
    (hstart : endpointTime ≤ time)
    (hbefore : time < returnTime)
    (hcan : CanSubtract (time + 1) (stateAt time)) :
    time + 1 ≠ returnTime := by
  intro hlast
  have hsourceBelow := h.first_return.value_below_of_between
    h.endpoint_below hstart (Nat.le_of_lt hbefore)
  subst returnTime
  have hforced : ¬ CanSubtract (time + 2) (stateAt (time + 1)) := by
    simpa [Nat.add_assoc] using
      h.first_return.crossing.forced_addition
  have hcross : target ≤ a (time + 2) := by
    simpa [Nat.add_assoc] using
      h.first_return.crossing.endpoint_ge
  have hexact := legalSubtraction_forcedAddition_crossing_hits_target
    hsourceBelow hcan hforced hcross
  exact htargetMissing ⟨time + 2, hexact⟩

/-- Strong form: every legal internal endpoint lies strictly before the
return under missing-target provenance. -/
theorem CanonicalBelowCorridorSuffix.internalSubtraction_before_return
    {target endpointTime returnTime time : Nat}
    (h : CanonicalBelowCorridorSuffix target endpointTime returnTime)
    (htargetMissing : ¬ ∃ witness, a witness = target)
    (hstart : endpointTime ≤ time)
    (hbefore : time < returnTime)
    (hcan : CanSubtract (time + 1) (stateAt time)) :
    time + 1 < returnTime := by
  have hle : time + 1 ≤ returnTime := by omega
  have hne := h.internalSubtraction_ne_return htargetMissing
    hstart hbefore hcan
  omega

/-- A legal child in a missing-target corridor carries strict endpoint
separation, simultaneous budget/cursor descent, and a total remaining-suffix
classification. -/
theorem CanonicalBelowCorridorSuffix.child_of_internalSubtraction_missing
    {target endpointTime returnTime time : Nat}
    (h : CanonicalBelowCorridorSuffix target endpointTime returnTime)
    (htargetMissing : ¬ ∃ witness, a witness = target)
    (hstart : endpointTime ≤ time)
    (hbefore : time < returnTime)
    (hcan : CanSubtract (time + 1) (stateAt time)) :
    ∃ child : CanonicalBelowCorridorSuffix target (time + 1) returnTime,
      missingBelowCount target (time + 1) <
        missingBelowCount target time ∧
      CorridorSuffixProgress returnTime (time + 1) endpointTime ∧
      time + 1 < returnTime ∧
      ((∃ later, time + 1 ≤ later ∧ later < returnTime ∧
          CanSubtract (later + 1) (stateAt later)) ∨
        AllForcedAdditionSuffix child) := by
  rcases h.child_of_internalSubtraction hstart hbefore hcan with
    ⟨child, hbudget, hprogress⟩
  have hstrict := h.internalSubtraction_before_return htargetMissing
    hstart hbefore hcan
  refine ⟨child, hbudget, hprogress, hstrict, ?_⟩
  by_cases hnext : ∃ later, time + 1 ≤ later ∧ later < returnTime ∧
      CanSubtract (later + 1) (stateAt later)
  · exact Or.inl hnext
  · right
    intro later hlater hbeforeLater hcanLater
    exact hnext ⟨later, hlater, hbeforeLater, hcanLater⟩

/-- Applied to the hypothetical permanent tail, every legal endpoint child
is strictly nonterminal; if no further legal endpoint exists, the suffix is
the target-bounded all-forced residual. -/
theorem CanonicalReturnRebaseCertificate.legalSuffixChild_missingBoundary
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : CanonicalReturnRebaseCertificate source)
    {time : Nat}
    (hstart : h.discharge.downTime + 1 ≤ time)
    (hbefore : time < h.discharge.returnTime)
    (hcan : CanSubtract (time + 1) (stateAt time)) :
    ∃ child : CanonicalBelowCorridorSuffix target (time + 1)
        h.discharge.returnTime,
      time + 1 < h.discharge.returnTime ∧
      missingBelowCount target (time + 1) <
        missingBelowCount target time ∧
      ((∃ later, time + 1 ≤ later ∧ later < h.discharge.returnTime ∧
          CanSubtract (later + 1) (stateAt later)) ∨
        AllForcedAdditionSuffix child) := by
  let suffix := h.discharge.exists_belowCorridor.toSuffix
  rcases suffix.child_of_internalSubtraction_missing
      h.discharge.combined.tail.target_missing hstart hbefore hcan with
    ⟨child, hbudget, hprogress, hstrict, hremaining⟩
  exact ⟨child, hstrict, hbudget, hremaining⟩

end

end Recaman
