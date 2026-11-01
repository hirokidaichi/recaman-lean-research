import Recaman.PermanentAboveCorridorPrefixSuccessorCoverage

namespace Recaman

noncomputable section

/-! # The remaining obstruction at replay clock 112

The prefix-successor sweep pins a clock-112 exact replay to minimum value
`371`, predecessor first time `108`, downcross time `109`, and target band
`(152, 261]`.  This module records what can be proved from that pin without
evaluating the deep orbit equality `a 4825 = 371`.
-/

/-- Exact deep freedom left by the clock-112 pin.  The tail minimum clock is
not an arbitrary late occurrence of 371: it must be the unique first
occurrence, created freshly by a legal subtraction from `minimumTime + 371`.
The target band is retained because the local fixed-cycle facts alone do not
select one missing target inside it. -/
structure Clock112FirstOccurrenceObstruction
    (target minimumTime : Nat) : Prop where
  target_lower : 152 < target
  target_upper : target ≤ 261
  minimumTime_after_checked_prefix : 371 < minimumTime
  minimum_first : FirstAt a 371 minimumTime
  incoming_subtraction :
    CanSubtract minimumTime (stateAt (minimumTime - 1))
  incoming_predecessor : a (minimumTime - 1) = minimumTime + 371

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- At clock 112 the predecessor follow-up is concretely the surviving
double-subtraction branch.  Thus the general follow-up dichotomy has no
remaining Boolean choice at this clock. -/
theorem clock112_minimum_predecessor_double_subtraction
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) :
    CanSubtract 109 (stateAt 108) ∧
      CanSubtract 110 (stateAt 109) := by
  have hfirst := r.historicalFirstTime_eq_108_of_crossingTime_eq_112 hclock
  have hminimum := r.historicalMinimumValue_eq_371_of_crossingTime_eq_112
    hclock
  have htail := r.tailStart_bound_deepest (by
    have htarget := r.clock112_historical_downcross_pins hclock
    omega)
  have hminimumTime := source.historical_minimum.minimum.start_le_time
  have hvalueOrder : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime := by
    rw [hfirst]
    have hvalue : a 108 = 370 := by
      set_option maxRecDepth 100000 in decide
    rw [hvalue]
    omega
  have htimeOrder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime := by omega
  rcases r.minimum_predecessor_followUp hvalueOrder htimeOrder with
    hblocked | hdouble
  · have hactual : CanSubtract 109 (stateAt 108) := by
      set_option maxRecDepth 100000 in decide
    have hnot : ¬ CanSubtract 109 (stateAt 108) := by
      simpa only [hfirst] using hblocked.2
    exact False.elim (hnot hactual)
  · simpa [hfirst] using hdouble

/-- Complete structural residual of a clock-112 replay.  No evaluation beyond
the already checked prefix at time 371 is used. -/
theorem clock112_firstOccurrenceObstruction
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) :
    Clock112FirstOccurrenceObstruction target
      source.historicalMinimumTime := by
  have hpins := r.clock112_historical_downcross_pins hclock
  have hminimum := r.historicalMinimumValue_eq_371_of_crossingTime_eq_112
    hclock
  have htail := r.tailStart_bound_deepest (by omega)
  have hminimumStart := source.historical_minimum.minimum.start_le_time
  have hminimumTime : 371 < source.historicalMinimumTime := by omega
  have hpositive : 0 < source.historicalMinimumTime := by omega
  have hsucc : source.historicalMinimumTime - 1 + 1 =
      source.historicalMinimumTime := by omega
  have hincoming : CanSubtract (source.historicalMinimumTime - 1 + 1)
      (stateAt (source.historicalMinimumTime - 1)) := by
    by_cases hcan : CanSubtract (source.historicalMinimumTime - 1 + 1)
        (stateAt (source.historicalMinimumTime - 1))
    · exact hcan
    · have hadd := a_succ_of_not_canSubtract hcan
      rw [hsucc, hminimum] at hadd
      have hnonnegative : 0 ≤ a (source.historicalMinimumTime - 1) :=
        Nat.zero_le _
      omega
  have hfirst := firstAt_succ_of_canSubtract hincoming
  have hstep := a_succ_of_canSubtract hincoming
  have hentryPositive := hincoming.1
  have hentryValue : (stateAt (source.historicalMinimumTime - 1)).value =
      a (source.historicalMinimumTime - 1) := rfl
  refine {
    target_lower := hpins.2.2.1
    target_upper := hpins.2.2.2
    minimumTime_after_checked_prefix := hminimumTime
    minimum_first := ?_
    incoming_subtraction := ?_
    incoming_predecessor := ?_
  }
  · rw [hsucc] at hfirst
    simpa only [hminimum] using hfirst
  · simpa only [hsucc] using hincoming
  · rw [hsucc, hminimum] at hstep
    rw [hentryValue] at hentryPositive
    omega

/-- Consequently the minimum clock is no longer a free replay parameter:
all clock-112 replay certificates, even over different discharge sources,
select the same first occurrence of 371. -/
theorem clock112_historicalMinimumTime_unique
    {target₁ target₂ start₁ start₂ : Nat}
    {parent₁ parent₂ : PhaseSearchNode}
    {source₁ : PermanentTailDischargeReturnCertificate target₁ start₁
      parent₁}
    {source₂ : PermanentTailDischargeReturnCertificate target₂ start₂
      parent₂}
    (r₁ : TerminalExactDischargeReplayCertificate source₁)
    (r₂ : TerminalExactDischargeReplayCertificate source₂)
    (hclock₁ : r₁.crossingTime = 112)
    (hclock₂ : r₂.crossingTime = 112) :
    source₁.historicalMinimumTime = source₂.historicalMinimumTime := by
  have h₁ := (r₁.clock112_firstOccurrenceObstruction hclock₁).minimum_first
  have h₂ := (r₂.clock112_firstOccurrenceObstruction hclock₂).minimum_first
  exact h₁.unique h₂

end TerminalExactDischargeReplayCertificate

end


end Recaman
