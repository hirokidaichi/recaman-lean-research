import Recaman.DebtInvariant
import Recaman.DebtAddition

namespace Recaman

/-- The configurations not discharged by the present debt invariant.

There are two genuine crossings.  A legal subtraction can recover a
predecessor at or above the fixed anchor.  A forced addition can jump from a
predecessor below the target to a first-occurring value above it.  In the
latter case we retain the exact reason why subtraction was forced. -/
inductive DebtStepObstruction
    (target horizon anchor value firstTime : Nat) : Prop
  | legal_reaches_anchor
      (n : Nat)
      (htime : firstTime = n + 1)
      (hcan : CanSubtract (n + 1) (stateAt n))
      (hvalue : value = a n - (n + 1))
      (htargetBelowValue : target < value)
      (hanchor : anchor ≤ a n) :
      DebtStepObstruction target horizon anchor value firstTime
  | addition_nonpositive
      (n : Nat)
      (htime : firstTime = n + 1)
      (hforced : ¬ CanSubtract (n + 1) (stateAt n))
      (hvalue : value = a n + (n + 1))
      (htargetBelowValue : target < value)
      (hbelow : a n < target)
      (hnonpositive : a n ≤ n + 1) :
      DebtStepObstruction target horizon anchor value firstTime
  | addition_seen_below_target
      (n x fx : Nat)
      (htime : firstTime = n + 1)
      (hforced : ¬ CanSubtract (n + 1) (stateAt n))
      (hvalue : value = a n + (n + 1))
      (htargetBelowValue : target < value)
      (hbelow : a n < target)
      (hcandidate : x = a n - (n + 1))
      (hpositive : 0 < x)
      (hfirst : FirstAt a x fx)
      (htimeDrop : fx < firstTime)
      (hcandidateBelow : x < target)
      (halreadyInHorizon : x ∈ valuesThrough horizon) :
      DebtStepObstruction target horizon anchor value firstTime

/-- Strongest local outcome currently supplied by `DebtInvariant` and the
classification of the final transition of a first occurrence. -/
inductive DebtStepOutcome
    (target horizon anchor value firstTime : Nat) : Prop
  | target_occurs
      (witness : Nat)
      (hvalue : a witness = target) :
      DebtStepOutcome target horizon anchor value firstTime
  | exit_normal
      (childValue childTime : Nat)
      (htarget : target ≤ childValue)
      (hfirst : FirstAt a childValue childTime)
      (hprogress : PhaseSearchProgress target
        ⟨horizon, childValue, .normal, childValue⟩
        ⟨horizon, anchor, .debt, firstTime⟩) :
      DebtStepOutcome target horizon anchor value firstTime
  | continue_debt
      (childValue childTime : Nat)
      (hinvariant : DebtInvariant target
        ⟨horizon, anchor, .debt, childTime⟩ childValue childTime)
      (hprogress : PhaseSearchProgress target
        ⟨horizon, anchor, .debt, childTime⟩
        ⟨horizon, anchor, .debt, firstTime⟩) :
      DebtStepOutcome target horizon anchor value firstTime
  | crossing
      (hcrossing : DebtStepObstruction
        target horizon anchor value firstTime) :
      DebtStepOutcome target horizon anchor value firstTime

/-- An earlier first occurrence carried by debt is already present at the
fixed history horizon.  Consequently it is not a newly consumed missing
value at that horizon. -/
theorem debt_earlier_firstAt_mem_horizon
    {x fx firstTime horizon : Nat}
    (hfirst : FirstAt a x fx)
    (hfx : fx < firstTime)
    (horizonBound : firstTime < horizon) :
    x ∈ valuesThrough horizon := by
  apply mem_valuesThrough_iff.mpr
  exact ⟨fx, by omega, hfirst.1⟩

/-- Keeping the debt horizon fixed cannot lower the history-budget component,
even when the extracted value is below the target. -/
theorem debt_fixed_horizon_has_no_budget_drop
    {target horizon : Nat} :
    ¬ missingBelowCount target horizon < missingBelowCount target horizon := by
  exact Nat.lt_irrefl _

/-- Replacing the fixed horizon by the extracted earlier time points the
history budget in the wrong direction: an earlier horizon can have at least
as many missing values, never strictly fewer. -/
theorem debt_earlier_horizon_cannot_drop_budget
    {target earlierTime horizon : Nat}
    (htime : earlierTime ≤ horizon) :
    ¬ missingBelowCount target earlierTime <
      missingBelowCount target horizon := by
  have hmono := missingBelowCount_antitone (m := target) htime
  omega

/-- Every valid positive-target debt node has one of the three rank-decreasing
outcomes, witnesses the target, or exposes one of the explicit crossings
described by `DebtCrossing`. -/
theorem debtStep_classify
    {target horizon anchor value firstTime : Nat}
    (htargetPositive : 0 < target)
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    DebtStepOutcome target horizon anchor value firstTime := by
  by_cases htargetValue : target = value
  · exact .target_occurs firstTime (by
      rw [htargetValue]
      exact hinv.first.1)
  · have htargetLt : target < value :=
      Nat.lt_of_le_of_ne hinv.target_le htargetValue
    have htimePositive := debt_firstTime_pos htargetPositive hinv
    cases firstTime with
    | zero => omega
    | succ n =>
        rcases firstAt_succ_transition hinv.first with
          ⟨hcan, hvalue⟩ | ⟨hforced, hvalue⟩
        · rcases debt_legalSubtraction_earlierPredecessor hinv hcan with
            ⟨predecessorTime, hfirstPredecessor, htime,
              hvalueLt, hprogress⟩
          by_cases hanchor : a n < anchor
          · have hpreserved := debt_legalSubtraction_preservesInvariant
                hinv hcan hfirstPredecessor htime hanchor
            exact .continue_debt (a n) predecessorTime
              hpreserved.1 hpreserved.2
          · exact .crossing (.legal_reaches_anchor n rfl hcan hvalue htargetLt
              (Nat.le_of_not_gt hanchor))
        · rcases debt_forcedAddition_predecessor hinv hforced with
            ⟨predecessorTime, hfirstPredecessor, htime,
              hanchor, hbelow | habove⟩
          · rcases firstAt_forcedAddition_dichotomy hinv.first hforced with
              hnonpositive | ⟨x, fx, hcandidate, hxPositive,
                hfirstX, hfx, hxValue⟩
            · exact .crossing (.addition_nonpositive n rfl hforced hvalue
                htargetLt
                hbelow (Nat.le_of_not_gt hnonpositive))
            · have hxTarget : x < target :=
                Nat.lt_trans (by
                  rw [hcandidate]
                  omega) hbelow
              have hxHorizon : x ∈ valuesThrough horizon :=
                debt_earlier_firstAt_mem_horizon hfirstX hfx
                  hinv.firstTime_lt_horizon
              exact .crossing (.addition_seen_below_target
                n x fx rfl hforced hvalue htargetLt hbelow hcandidate hxPositive
                hfirstX hfx hxTarget hxHorizon)
          · have hexit := debt_forcedAddition_exitProgress
                hinv hforced hfirstPredecessor habove
            exact .exit_normal (a n) predecessorTime
              hexit.1 hexit.2.1 hexit.2.2

end Recaman
