import Recaman.PermanentAboveCorridorReplayFloorFour

namespace Recaman

noncomputable section

/-! # Prefix-successor coverage of a replay clock

The clock-by-clock replay sweep repeatedly uses the same global mechanism.
The first occurrence of the predecessor of the permanent-tail minimum lies
before the replay clock.  If the successor of every larger prefix value has
already occurred before a later low orbit witness, then the tail minimum is
a forbidden late revisit.

This module packages that mechanism as `ReplayPrefixSuccessorCoverage`.  It
also allows one exceptional successor.  For clock 112, kernel computation
through time 371 proves that the unique exception is 371.  Consequently the
formerly informal fourth deep straggler is now pinned exactly: a clock-112
replay has tail minimum 371, predecessor first time 108, historical downcross
time 109, and target in `(152, 261]`.
-/

/-- Every prefix value above the replay anchor has its numeric successor
already witnessed by `cutoff`; both the witness time and value are bounded by
the cutoff so a later tail minimum cannot revisit it. -/
def ReplayPrefixSuccessorCoverage (clock cutoff : Nat) : Prop :=
  ∀ time, time < clock → a clock < a time →
    ∃ witness, witness ≤ cutoff ∧ a witness = a time + 1 ∧
      a witness ≤ cutoff

/-- The same coverage condition with one explicitly named uncovered
successor. -/
def ReplayPrefixSuccessorCoverageExcept
    (clock cutoff exceptional : Nat) : Prop :=
  ∀ time, time < clock → a clock < a time →
    (∃ witness, witness ≤ cutoff ∧ a witness = a time + 1 ∧
      a witness ≤ cutoff) ∨
    a time + 1 = exceptional

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Any orbit value at or below the missing target must occur before the
strict-above tail begins. -/
theorem tailStart_after_lowWitness
    (_r : TerminalExactDischargeReplayCertificate source)
    {witness : Nat} (hlow : a witness ≤ target) :
    witness < source.tailStart := by
  by_cases hbefore : witness < source.tailStart
  · exact hbefore
  · have habove := source.historical_tail.strictly_above witness
      (Nat.le_of_not_gt hbefore)
    omega

/-- A low witness also precedes the selected minimum time of that tail. -/
theorem historicalMinimumTime_after_lowWitness
    (r : TerminalExactDischargeReplayCertificate source)
    {witness : Nat} (hlow : a witness ≤ target) :
    witness < source.historicalMinimumTime := by
  have htail := r.tailStart_after_lowWitness hlow
  have hminimum := source.historical_minimum.minimum.start_le_time
  omega

/-- Full prefix-successor coverage is incompatible with an exact replay.
The historical minimum predecessor supplies a covered prefix value, while a
later low witness pushes the minimum clock beyond both its old occurrence and
its value. -/
theorem replay_impossible_of_prefixSuccessorCoverage
    (r : TerminalExactDischargeReplayCertificate source)
    {cutoff : Nat}
    (hlow : a cutoff ≤ target)
    (hcoverage : ReplayPrefixSuccessorCoverage r.crossingTime cutoff) :
    False := by
  have hminimumAfter := r.historicalMinimumTime_after_lowWitness hlow
  have hfirstBefore : source.historicalFirstTime < r.crossingTime := by
    have hdown := source.downcross.horizon_le_time
    have hendpoint := r.endpoint_le_crossingTime
    omega
  have hpredecessor := source.historical_minimum.predecessor_first.1
  have htargetPredecessor :=
    source.historical_minimum.target_lt_predecessor
  have hanchorBelow := r.crossing_straddles_target.1
  have hprefixAbove :
      a r.crossingTime < a source.historicalFirstTime := by
    omega
  rcases hcoverage source.historicalFirstTime hfirstBefore hprefixAbove with
    ⟨witness, hwitnessTime, hwitnessValue, hwitnessBound⟩
  have hwitnessBefore : witness < source.historicalMinimumTime := by omega
  have hvalueBefore : a witness < source.historicalMinimumTime := by omega
  have hminimumValue :
      a source.historicalMinimumTime = a witness := by
    omega
  exact value_no_late_recurrence (w := witness)
    (m := source.historicalMinimumTime) rfl hwitnessBefore hvalueBefore
    hminimumValue

/-- Uniform coverage over a clock interval raises the replay floor in one
step, without a separate theorem for each mechanically impossible clock. -/
theorem crossingTime_ge_of_prefixSuccessorCoverage
    (r : TerminalExactDischargeReplayCertificate source)
    {floor ceiling cutoff : Nat}
    (hfloor : floor ≤ r.crossingTime)
    (hlow : a cutoff ≤ target)
    (hcoverage : ∀ clock, floor ≤ clock → clock < ceiling →
      ReplayPrefixSuccessorCoverage clock cutoff) :
    ceiling ≤ r.crossingTime := by
  by_cases hceiling : ceiling ≤ r.crossingTime
  · exact hceiling
  · have hlt : r.crossingTime < ceiling := Nat.lt_of_not_ge hceiling
    exact False.elim
      (r.replay_impossible_of_prefixSuccessorCoverage hlow
        (hcoverage r.crossingTime hfloor hlt))

/-- If prefix coverage has one exception, the historical tail minimum is
forced to equal that exceptional successor. -/
theorem historicalMinimumValue_eq_of_prefixSuccessorCoverageExcept
    (r : TerminalExactDischargeReplayCertificate source)
    {cutoff exceptional : Nat}
    (hlow : a cutoff ≤ target)
    (hcoverage : ReplayPrefixSuccessorCoverageExcept r.crossingTime cutoff
      exceptional) :
    a source.historicalMinimumTime = exceptional := by
  have hminimumAfter := r.historicalMinimumTime_after_lowWitness hlow
  have hfirstBefore : source.historicalFirstTime < r.crossingTime := by
    have hdown := source.downcross.horizon_le_time
    have hendpoint := r.endpoint_le_crossingTime
    omega
  have hpredecessor := source.historical_minimum.predecessor_first.1
  have htargetPredecessor :=
    source.historical_minimum.target_lt_predecessor
  have hanchorBelow := r.crossing_straddles_target.1
  have hprefixAbove :
      a r.crossingTime < a source.historicalFirstTime := by
    omega
  rcases hcoverage source.historicalFirstTime hfirstBefore hprefixAbove with
    hcovered | hexceptional
  · rcases hcovered with
      ⟨witness, hwitnessTime, hwitnessValue, hwitnessBound⟩
    have hwitnessBefore : witness < source.historicalMinimumTime := by omega
    have hvalueBefore : a witness < source.historicalMinimumTime := by omega
    have hminimumValue :
        a source.historicalMinimumTime = a witness := by
      omega
    exact False.elim
      (value_no_late_recurrence (w := witness)
        (m := source.historicalMinimumTime) rfl hwitnessBefore hvalueBefore
        hminimumValue)
  · omega

end TerminalExactDischargeReplayCertificate

/-- Through clock 112 and cutoff 371, every prefix value above the anchor
152 has its successor covered except the predecessor value 370, whose
successor is the exceptional value 371. -/
theorem prefixSuccessorCoverageExcept_onehundredtwelve :
    ReplayPrefixSuccessorCoverageExcept 112 371 371 := by
  intro time htime habove
  have hall : ∀ t : Fin 112,
      (∃ witness : Fin 372, a witness = a t + 1 ∧ a witness ≤ 371) ∨
        a t + 1 = 371 ∨ a t ≤ 152 := by
    set_option maxRecDepth 100000 in decide
  rcases hall ⟨time, htime⟩ with hcovered | hexceptional | hsmall
  · rcases hcovered with ⟨witness, hwitnessValue, hwitnessBound⟩
    exact Or.inl ⟨witness, by omega, by simpa using hwitnessValue,
      by simpa using hwitnessBound⟩
  · exact Or.inr (by simpa using hexceptional)
  · have hanchor : a 112 = 152 := by
      set_option maxRecDepth 100000 in decide
    have hsmall' : a time ≤ 152 := by simpa using hsmall
    omega

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- Clock 112 pins the formerly informal deep straggler exactly: the
permanent-tail minimum value is 371. -/
theorem historicalMinimumValue_eq_371_of_crossingTime_eq_112
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) :
    a source.historicalMinimumTime = 371 := by
  have htarget := r.onehundredfourteen_le_target
  have hlow : a 371 ≤ target := by
    have hvalue : a 371 = 108 := by
      set_option maxRecDepth 100000 in decide
    omega
  apply r.historicalMinimumValue_eq_of_prefixSuccessorCoverageExcept hlow
  simpa [hclock] using prefixSuccessorCoverageExcept_onehundredtwelve

/-- The predecessor of the pinned minimum 371 first occurs at clock 108. -/
theorem historicalFirstTime_eq_108_of_crossingTime_eq_112
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) :
    source.historicalFirstTime = 108 := by
  have hminimum := r.historicalMinimumValue_eq_371_of_crossingTime_eq_112
    hclock
  have hfirst := source.historical_minimum.predecessor_first
  have hfirst370 : FirstAt a 370 source.historicalFirstTime := by
    simpa [hminimum] using hfirst
  have hactual : FirstAt a 370 108 := by
    refine ⟨by set_option maxRecDepth 100000 in decide, ?_⟩
    intro earlier hearlier
    have hall : ∀ t, t < 108 → a t ≠ 370 := by
      set_option maxRecDepth 100000 in decide
    exact hall earlier hearlier
  exact hfirst370.unique hactual

/-- At clock 112 the historical downcross is the second subtraction after
the predecessor: it occurs at time 109, lands freshly on 151 at time 110,
and narrows the missing target to `(152, 261]`. -/
theorem clock112_historical_downcross_pins
    (r : TerminalExactDischargeReplayCertificate source)
    (hclock : r.crossingTime = 112) :
    source.downTime = 109 ∧ a (source.downTime + 1) = 151 ∧
      152 < target ∧ target ≤ 261 := by
  have hfirst := r.historicalFirstTime_eq_108_of_crossingTime_eq_112 hclock
  have hdownLower := source.downcross.horizon_le_time
  have hendpoint := r.endpoint_le_crossingTime
  have htargetLower := r.crossing_straddles_target.1
  have htargetUpper := r.crossing_straddles_target.2
  rw [hclock] at hendpoint htargetLower htargetUpper
  have hanchor : a 112 = 152 := by
    set_option maxRecDepth 100000 in decide
  have hcrossingEndpoint : a 113 = 265 := by
    set_option maxRecDepth 100000 in decide
  rw [hanchor] at htargetLower
  rw [hcrossingEndpoint] at htargetUpper
  have hdownCases : source.downTime = 108 ∨ source.downTime = 109 ∨
      source.downTime = 110 ∨ source.downTime = 111 := by
    omega
  rcases hdownCases with h108 | h109 | h110 | h111
  · have hbelow := source.downcross.endpoint_below
    rw [h108] at hbelow
    have hvalue : a 109 = 261 := by
      set_option maxRecDepth 100000 in decide
    rw [hvalue] at hbelow
    have htargetCases : target = 262 ∨ target = 263 ∨ target = 264 ∨
        target = 265 := by
      omega
    rcases htargetCases with rfl | rfl | rfl | rfl
    · exact False.elim
        (r.target_missing ⟨107,
          by set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim
        (r.target_missing ⟨105,
          by set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim
        (r.target_missing ⟨103,
          by set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim
        (r.target_missing ⟨101,
          by set_option maxRecDepth 100000 in decide⟩)
  · refine ⟨h109, ?_, by omega, ?_⟩
    · rw [h109]
      set_option maxRecDepth 100000 in decide
    · have hstart := source.downcross.start_at_or_above
      rw [h109] at hstart
      have hvalue : a 109 = 261 := by
        set_option maxRecDepth 100000 in decide
      rw [hvalue] at hstart
      omega
  · have hstart := source.downcross.start_at_or_above
    rw [h110] at hstart
    have hvalue : a 110 = 151 := by
      set_option maxRecDepth 100000 in decide
    omega
  · have hstart := source.downcross.start_at_or_above
    rw [h111] at hstart
    have hvalue : a 111 = 40 := by
      set_option maxRecDepth 100000 in decide
    omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
