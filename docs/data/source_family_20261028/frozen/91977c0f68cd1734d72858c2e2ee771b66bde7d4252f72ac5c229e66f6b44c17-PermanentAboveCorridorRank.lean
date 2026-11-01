import Recaman.PermanentAboveCorridor

namespace Recaman

noncomputable section

/-! # Finite rank for all-forced canonical corridors

Legal subtractions inside the canonical below corridor already decrease the
missing-below history budget.  This module packages the complementary case:
every internal transition is forced addition.  Such a delayed corridor ends
strictly before the fixed target clock, admits an exact telescoping addition
trace, and is traversed by the well-founded remaining-clock rank.

This closes the finite corridor traversal only.  It deliberately does not
claim that returning to the rebased crossing exits the outer stationary
cycle.
-/

/-- Every transition strictly before the canonical return is forced
addition. -/
def AllForcedAdditionCorridor
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (_certificate : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime) : Prop :=
  ∀ time, downTime + 1 ≤ time → time < returnTime →
    ¬ CanSubtract (time + 1) (stateAt time)

/-- A delayed all-forced corridor returns before the target clock. -/
theorem AllForcedAdditionCorridor.returnTime_lt_target
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    {certificate : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime}
    (h : AllForcedAdditionCorridor certificate)
    (hdelayed : downTime + 1 < returnTime) :
    returnTime < target := by
  let lastTime := returnTime - 1
  have hlastStart : downTime + 1 ≤ lastTime := by
    dsimp [lastTime]
    omega
  have hlastBefore : lastTime < returnTime := by
    dsimp [lastTime]
    omega
  have hbound := certificate.internalForced_clockBelowTarget
    hlastStart hlastBefore (h lastTime hlastStart hlastBefore)
  dsimp [lastTime] at hbound
  omega

/-- Therefore the corridor gap is also bounded by the finite target
interval remaining after the endpoint clock. -/
theorem AllForcedAdditionCorridor.gap_lt_targetGap
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    {certificate : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime}
    (h : AllForcedAdditionCorridor certificate)
    (hdelayed : downTime + 1 < returnTime) :
    returnTime - (downTime + 1) < target - (downTime + 1) := by
  have hreturn := h.returnTime_lt_target hdelayed
  omega

/-- Sum of the successive clocks added during a forced-addition run. -/
def forcedClockSum (start : Nat) : Nat → Nat
  | 0 => 0
  | steps + 1 => forcedClockSum start steps + (start + steps + 1)

/-- Exact telescoping value trace along an all-forced corridor. -/
theorem AllForcedAdditionCorridor.value_eq_add_forcedClockSum
    {target tailStart historicalFirstTime downTime returnTime steps : Nat}
    {certificate : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime}
    (h : AllForcedAdditionCorridor certificate)
    (hfinish : downTime + 1 + steps ≤ returnTime) :
    a (downTime + 1 + steps) =
      a (downTime + 1) + forcedClockSum (downTime + 1) steps := by
  induction steps with
  | zero => simp [forcedClockSum]
  | succ steps ih =>
      have hprevious : downTime + 1 + steps < returnTime := by omega
      have hstart : downTime + 1 ≤ downTime + 1 + steps := by omega
      have hforced := h (downTime + 1 + steps) hstart hprevious
      have hequation := a_succ_of_not_canSubtract hforced
      have ih' := ih (by omega)
      rw [forcedClockSum]
      calc
        a (downTime + 1 + (steps + 1)) =
            a (downTime + 1 + steps + 1) := by congr 1 <;> omega
        _ = a (downTime + 1 + steps) +
            (downTime + 1 + steps + 1) := hequation
        _ = (a (downTime + 1) +
              forcedClockSum (downTime + 1) steps) +
            (downTime + 1 + steps + 1) := by rw [ih']
        _ = a (downTime + 1) +
            (forcedClockSum (downTime + 1) steps +
              (downTime + 1 + steps + 1)) := by omega

/-- Every nonempty piece of an all-forced corridor strictly raises its orbit
value, even though this local growth is not an outer-cycle descent. -/
theorem AllForcedAdditionCorridor.value_strictMono
    {target tailStart historicalFirstTime downTime returnTime
      earlier later : Nat}
    {certificate : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime}
    (h : AllForcedAdditionCorridor certificate)
    (hstart : downTime + 1 ≤ earlier)
    (htimes : earlier < later)
    (hfinish : later ≤ returnTime) :
    a earlier < a later := by
  have aux : ∀ distance,
      0 < distance → earlier + distance ≤ returnTime →
      a earlier < a (earlier + distance) := by
    intro distance
    induction distance with
    | zero => intro hpositive; omega
    | succ distance ih =>
        intro hpositive hbound
        have htimeStart : downTime + 1 ≤ earlier + distance := by omega
        have htimeBefore : earlier + distance < returnTime := by omega
        have hforced := h (earlier + distance) htimeStart htimeBefore
        have hequation := a_succ_of_not_canSubtract hforced
        by_cases hzero : distance = 0
        · subst distance
          have hequation' : a (earlier + 1) =
              a earlier + (earlier + 1) := by
            simpa [Nat.add_assoc] using hequation
          have hstep : a earlier < a (earlier + 1) := by omega
          simpa using hstep
        · have hprevious := ih (by omega) (by omega)
          have hstep : a (earlier + distance) <
              a (earlier + distance + 1) := by omega
          simpa [Nat.add_assoc] using Nat.lt_trans hprevious hstep
  have hdistance : 0 < later - earlier := by omega
  have hbound : earlier + (later - earlier) ≤ returnTime := by omega
  have hresult := aux (later - earlier) hdistance hbound
  have htimeEq : earlier + (later - earlier) = later := by omega
  rw [htimeEq] at hresult
  exact hresult

/-- Remaining finite clock below the target. -/
def corridorClockRemaining (target time : Nat) : Nat := target - time

def CorridorClockProgress (target : Nat) (child parent : Nat) : Prop :=
  corridorClockRemaining target child < corridorClockRemaining target parent

/-- Pullback of natural-number descent along the remaining clock. -/
theorem corridorClockProgress_wellFounded (target : Nat) :
    WellFounded (CorridorClockProgress target) := by
  apply WellFounded.intro
  intro time
  generalize hrank : corridorClockRemaining target time = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing time with
  | intro rank _ ih =>
      apply Acc.intro time
      intro child hchild
      have hrelation : corridorClockRemaining target child < rank := by
        simpa [CorridorClockProgress, hrank] using hchild
      exact ih (corridorClockRemaining target child) hrelation child rfl

/-- Advancing one step while still strictly below the target decreases the
remaining-clock rank. -/
theorem corridorClockProgress_succ
    {target time : Nat}
    (hclock : time + 1 < target) :
    CorridorClockProgress target (time + 1) time := by
  unfold CorridorClockProgress corridorClockRemaining
  omega

/-- Exhaustive delayed-corridor outcome: find an internal legal subtraction
with strict history-budget drop, or certify the entire interval all-forced
and target-bounded. -/
inductive DelayedCanonicalCorridorOutcome
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (certificate : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime) : Prop
  | internal_subtraction (time : Nat)
      (start_le : downTime + 1 ≤ time)
      (before_return : time < returnTime)
      (legal : CanSubtract (time + 1) (stateAt time))
      (budget_drop : missingBelowCount target (time + 1) <
        missingBelowCount target time) :
      DelayedCanonicalCorridorOutcome certificate
  | all_forced
      (forced : AllForcedAdditionCorridor certificate)
      (return_before_target : returnTime < target)
      (gap_bound : returnTime - (downTime + 1) <
        target - (downTime + 1)) :
      DelayedCanonicalCorridorOutcome certificate

/-- Every delayed canonical corridor has one of the two strict finite
certificates above. -/
theorem CanonicalBelowCorridorCertificate.delayedOutcome
    {target tailStart historicalFirstTime downTime returnTime : Nat}
    (h : CanonicalBelowCorridorCertificate target tailStart
      historicalFirstTime downTime returnTime)
    (hdelayed : downTime + 1 < returnTime) :
    DelayedCanonicalCorridorOutcome h := by
  by_cases hlegal : ∃ time,
      downTime + 1 ≤ time ∧ time < returnTime ∧
        CanSubtract (time + 1) (stateAt time)
  · rcases hlegal with ⟨time, hstart, hbefore, hcan⟩
    exact .internal_subtraction time hstart hbefore hcan
      (h.internalSubtraction_budgetDrop hstart hbefore hcan)
  · have hall : AllForcedAdditionCorridor h := by
      intro time hstart hbefore hcan
      exact hlegal ⟨time, hstart, hbefore, hcan⟩
    exact .all_forced hall (hall.returnTime_lt_target hdelayed)
      (hall.gap_lt_targetGap hdelayed)

/-- A rebased stationary certificate therefore exposes either the exact
immediate valley or a delayed corridor carrying budget descent / finite
clock data.  This is the typed connection back to the stationary kernel. -/
theorem CanonicalReturnRebaseCertificate.corridorOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : CanonicalReturnRebaseCertificate source) :
    h.discharge.returnTime = h.discharge.downTime + 1 ∨
      DelayedCanonicalCorridorOutcome
        h.discharge.exists_belowCorridor := by
  by_cases himmediate :
      h.discharge.returnTime = h.discharge.downTime + 1
  · exact Or.inl himmediate
  · right
    apply CanonicalBelowCorridorCertificate.delayedOutcome
    have hstart := h.discharge.return_crossing.crossing.start_le
    omega

end

end Recaman
