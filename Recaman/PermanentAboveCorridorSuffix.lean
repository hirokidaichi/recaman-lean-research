import Recaman.PermanentAboveCorridorRank

namespace Recaman

noncomputable section

/-! # Canonical suffixes consume legal corridor endpoints

The first weak upcrossing remains first when its below-target starting point
is moved later inside the same below corridor.  Hence every legal internal
subtraction creates a fresh later suffix endpoint for the same return
crossing.  The finite cursor `returnTime - endpointTime` strictly decreases
under this move.

Repeated suffix selection therefore ends at the return itself or at an
all-forced suffix.  This consumes internal legal endpoints, but the return
crossing is deliberately unchanged, so the outer stationary cycle remains.
-/

/-- Restricting the start of a first weak upcrossing to a later below-target
point preserves the same canonical return time. -/
theorem FirstWeakUpcrossingStep.suffix
    {target start suffixStart returnTime : Nat}
    (h : FirstWeakUpcrossingStep target start returnTime)
    (hstart : start ≤ suffixStart)
    (hfinish : suffixStart ≤ returnTime)
    (_hbelow : a suffixStart < target) :
    FirstWeakUpcrossingStep target suffixStart returnTime := {
  crossing := {
    start_le := hfinish
    below := h.crossing.below
    endpoint_ge := h.crossing.endpoint_ge
    forced_addition := h.crossing.forced_addition
  }
  first := by
    intro earlier hearlier hsuffixCrossing
    apply h.first earlier hearlier
    exact {
      start_le := Nat.le_trans hstart hsuffixCrossing.start_le
      below := hsuffixCrossing.below
      endpoint_ge := hsuffixCrossing.endpoint_ge
      forced_addition := hsuffixCrossing.forced_addition
    }
}

/-- A fresh below-target endpoint together with its first return crossing. -/
structure CanonicalBelowCorridorSuffix
    (target endpointTime returnTime : Nat) : Prop where
  endpoint_first : FirstAt a (a endpointTime) endpointTime
  endpoint_below : a endpointTime < target
  first_return : FirstWeakUpcrossingStep target endpointTime returnTime

/-- The historical corridor begins with a canonical suffix at its fresh
downcross endpoint. -/
theorem CanonicalBelowCorridorCertificate.toSuffix
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime) :
    CanonicalBelowCorridorSuffix target (downTime + 1) returnTime := {
  endpoint_first := h.endpoint_first
  endpoint_below := h.downcross.endpoint_below
  first_return := h.first_return
}

/-- Remaining distance from a suffix endpoint to the fixed return. -/
def corridorSuffixRemaining (returnTime endpointTime : Nat) : Nat :=
  returnTime - endpointTime

def CorridorSuffixProgress (returnTime : Nat)
    (childEndpoint parentEndpoint : Nat) : Prop :=
  corridorSuffixRemaining returnTime childEndpoint <
    corridorSuffixRemaining returnTime parentEndpoint

/-- The suffix endpoint cursor is well founded. -/
theorem corridorSuffixProgress_wellFounded (returnTime : Nat) :
    WellFounded (CorridorSuffixProgress returnTime) := by
  apply WellFounded.intro
  intro endpoint
  generalize hrank : corridorSuffixRemaining returnTime endpoint = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing endpoint with
  | intro rank _ ih =>
      apply Acc.intro endpoint
      intro child hchild
      have hrelation : corridorSuffixRemaining returnTime child < rank := by
        simpa [CorridorSuffixProgress, hrank] using hchild
      exact ih (corridorSuffixRemaining returnTime child) hrelation child rfl

/-- Moving to a strictly later endpoint before the return strictly lowers
the suffix cursor. -/
theorem corridorSuffixProgress_of_later
    {parentEndpoint childEndpoint returnTime : Nat}
    (hlater : parentEndpoint < childEndpoint)
    (hfinish : childEndpoint ≤ returnTime) :
    CorridorSuffixProgress returnTime childEndpoint parentEndpoint := by
  unfold CorridorSuffixProgress corridorSuffixRemaining
  omega

/-- A legal subtraction inside a suffix creates a fresh later suffix for the
same canonical return, with both history-budget and endpoint-cursor descent. -/
theorem CanonicalBelowCorridorSuffix.child_of_internalSubtraction
    {target endpointTime returnTime time : Nat}
    (h : CanonicalBelowCorridorSuffix target endpointTime returnTime)
    (hstart : endpointTime ≤ time)
    (hbefore : time < returnTime)
    (hcan : CanSubtract (time + 1) (stateAt time)) :
    ∃ _child : CanonicalBelowCorridorSuffix target (time + 1) returnTime,
      missingBelowCount target (time + 1) <
        missingBelowCount target time ∧
      CorridorSuffixProgress returnTime (time + 1) endpointTime := by
  have hchildBelow := h.first_return.value_below_of_between
    h.endpoint_below (show endpointTime ≤ time + 1 by omega)
    (show time + 1 ≤ returnTime by omega)
  have hchildFirst := firstAt_succ_of_canSubtract hcan
  have hchildReturn := h.first_return.suffix
    (show endpointTime ≤ time + 1 by omega)
    (show time + 1 ≤ returnTime by omega) hchildBelow
  have hbudget := missingBelowCount_strict_of_firstAt hchildBelow
    (show time < time + 1 by omega) hchildFirst
  have hprogress := corridorSuffixProgress_of_later
    (show endpointTime < time + 1 by omega)
    (show time + 1 ≤ returnTime by omega)
  exact ⟨{
    endpoint_first := hchildFirst
    endpoint_below := hchildBelow
    first_return := hchildReturn
  }, hbudget, hprogress⟩

/-- No legal subtraction remains inside this suffix. -/
def AllForcedAdditionSuffix
    {target endpointTime returnTime : Nat}
    (_suffix : CanonicalBelowCorridorSuffix target endpointTime returnTime) :
    Prop :=
  ∀ time, endpointTime ≤ time → time < returnTime →
    ¬ CanSubtract (time + 1) (stateAt time)

/-- A nonempty all-forced suffix still ends before the target clock. -/
theorem AllForcedAdditionSuffix.returnTime_lt_target
    {target endpointTime returnTime : Nat}
    {suffix : CanonicalBelowCorridorSuffix target endpointTime returnTime}
    (h : AllForcedAdditionSuffix suffix)
    (hnonempty : endpointTime < returnTime) :
    returnTime < target := by
  let lastTime := returnTime - 1
  have hstart : endpointTime ≤ lastTime := by
    dsimp [lastTime]
    omega
  have hbefore : lastTime < returnTime := by
    dsimp [lastTime]
    omega
  have hforced := h lastTime hstart hbefore
  have hequation := a_succ_of_not_canSubtract hforced
  have hreturnBelow := suffix.first_return.crossing.below
  dsimp [lastTime] at hequation
  have hpredSucc : returnTime - 1 + 1 = returnTime := by omega
  rw [hpredSucc] at hequation
  omega

/-- Total suffix outcome.  A nonterminal suffix either advances to a later
fresh legal endpoint or is all-forced and target-bounded. -/
inductive CanonicalBelowCorridorSuffixOutcome
    {target endpointTime returnTime : Nat}
    (suffix : CanonicalBelowCorridorSuffix target endpointTime returnTime) :
    Prop
  | at_return (endpoint_eq : endpointTime = returnTime) :
      CanonicalBelowCorridorSuffixOutcome suffix
  | later_legal_endpoint (time : Nat)
      (start_le : endpointTime ≤ time)
      (before_return : time < returnTime)
      (legal : CanSubtract (time + 1) (stateAt time))
      (child : CanonicalBelowCorridorSuffix target (time + 1) returnTime)
      (budget_drop : missingBelowCount target (time + 1) <
        missingBelowCount target time)
      (cursor_drop : CorridorSuffixProgress returnTime
        (time + 1) endpointTime) :
      CanonicalBelowCorridorSuffixOutcome suffix
  | all_forced
      (endpoint_before_return : endpointTime < returnTime)
      (forced : AllForcedAdditionSuffix suffix)
      (return_before_target : returnTime < target) :
      CanonicalBelowCorridorSuffixOutcome suffix

/-- Every canonical suffix has the total outcome above. -/
theorem CanonicalBelowCorridorSuffix.outcome
    {target endpointTime returnTime : Nat}
    (h : CanonicalBelowCorridorSuffix target endpointTime returnTime) :
    CanonicalBelowCorridorSuffixOutcome h := by
  by_cases hatReturn : endpointTime = returnTime
  · exact .at_return hatReturn
  · have hbeforeEndpoint : endpointTime < returnTime := by
      have hle := h.first_return.crossing.start_le
      omega
    by_cases hlegal : ∃ time,
        endpointTime ≤ time ∧ time < returnTime ∧
          CanSubtract (time + 1) (stateAt time)
    · rcases hlegal with ⟨time, hstart, hbefore, hcan⟩
      rcases h.child_of_internalSubtraction hstart hbefore hcan with
        ⟨child, hbudget, hprogress⟩
      exact .later_legal_endpoint time hstart hbefore hcan child
        hbudget hprogress
    · have hall : AllForcedAdditionSuffix h := by
        intro time hstart hbefore hcan
        exact hlegal ⟨time, hstart, hbefore, hcan⟩
      exact .all_forced hbeforeEndpoint hall
        (hall.returnTime_lt_target hbeforeEndpoint)

/-- The rebased stationary certificate exposes the suffix outcome at its
historical endpoint. -/
theorem CanonicalReturnRebaseCertificate.suffixOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : CanonicalReturnRebaseCertificate source) :
    CanonicalBelowCorridorSuffixOutcome
      h.discharge.exists_belowCorridor.toSuffix :=
  h.discharge.exists_belowCorridor.toSuffix.outcome

end

end Recaman
