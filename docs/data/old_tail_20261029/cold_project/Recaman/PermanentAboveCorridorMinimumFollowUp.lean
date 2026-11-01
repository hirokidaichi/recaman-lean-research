import Recaman.PermanentAboveCorridorMinimumShape

namespace Recaman

noncomputable section

/-! # Witnessed follow-up dichotomy of the minimum predecessor

The shape restriction leaves two follow-ups after the minimum predecessor's
first occurrence.  Both now carry explicit witnesses.  The predecessor
value exceeds the target and hence its own clock, so an immediate forced
addition can only be blocked by history: its subtraction defect is already
seen.  A double subtraction instead lands on a fresh value one clock later,
by the very freshness of a legal subtraction.

Every surviving replay therefore either stores a concrete early occurrence
of `a f - (f + 1)`, or produces a fresh first occurrence at `f + 1` —
local, checkable data on which the next epoch's clock-by-clock attack can
pivot.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The minimum predecessor value strictly exceeds its successor clock. -/
theorem minimum_predecessor_value_above_clock
    (r : TerminalExactDischargeReplayCertificate source) :
    source.historicalFirstTime + 1 < a source.historicalFirstTime := by
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hlt := r.crossingTime_lt_target
  have hpred := source.historical_minimum.predecessor_first
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have htgt := source.historical_minimum.target_lt_predecessor
  omega

/-- Witnessed dichotomy: the follow-up is a history-blocked immediate
addition, or a double subtraction whose first step lands fresh. -/
theorem minimum_predecessor_followUp
    (r : TerminalExactDischargeReplayCertificate source)
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    ((a source.historicalFirstTime - (source.historicalFirstTime + 1)) ∈
        valuesThrough source.historicalFirstTime ∧
      ¬ CanSubtract (source.historicalFirstTime + 1)
        (stateAt source.historicalFirstTime)) ∨
    (CanSubtract (source.historicalFirstTime + 1)
        (stateAt source.historicalFirstTime) ∧
      CanSubtract (source.historicalFirstTime + 2)
        (stateAt (source.historicalFirstTime + 1))) := by
  have habove := r.minimum_predecessor_value_above_clock
  by_cases hsub1 : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime)
  · right
    refine ⟨hsub1, ?_⟩
    rcases r.minimum_predecessor_shape hvalue horder with hnosub | hsub2
    · exact absurd hsub1 hnosub
    · exact hsub2
  · left
    refine ⟨?_, hsub1⟩
    by_cases hseen : (a source.historicalFirstTime -
        (source.historicalFirstTime + 1)) ∈
        valuesThrough source.historicalFirstTime
    · exact hseen
    · exact False.elim (hsub1 ⟨by
        show source.historicalFirstTime + 1 <
          (stateAt source.historicalFirstTime).value
        have hvalue' : (stateAt source.historicalFirstTime).value =
            a source.historicalFirstTime := rfl
        omega, hseen⟩)

end TerminalExactDischargeReplayCertificate

end

end Recaman
