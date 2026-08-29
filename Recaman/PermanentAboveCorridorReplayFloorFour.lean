import Recaman.PermanentAboveCorridorCrossingRecord

namespace Recaman

noncomputable section

/-! # Fourth kernel floor of the replay fixed point

With the deep stragglers nineteen and sixty-one eliminated, the clock
floor thirty-two can be raised by the same three mechanical tools, now
unconditionally.  Record clocks (33, 66, 101) die because a replay
crossing is never an orbit record.  Clocks whose actual orbit step
subtracts or whose value fails the clock bound die by kernel computation.
The eleven genuine survivors (32, 35, 65, 68, 70, 72, 74, 100, 103, 105,
107) die by revisit elimination: the downcross pins the stored history
below the clock, the permanent tail must begin after a late low orbit
visit (values 47, 110, 109, 108 at times 222, 367, 369, 371), and every
candidate minimum-predecessor value has its successor seen early — a seen
value can never recur at the pinned minimum clock beyond the tail start.
Clock thirty-two alone is handled by straddle-band enumeration, using the
downcross prefix bound to shrink its band to `(46, 63]` and occurrence
witnesses through time 222.

The sweep stops at clock one hundred twelve: its wide band `(152, 265]`
re-admits the whole historical comb as minimum predecessors, and among
them the value 370 has minimum successor 371, whose first orbit
occurrence at time 4825 lies far beyond kernel range — a fourth deep
straggler.  Hence the crossing clock is at least one hundred twelve and
the missing target is at least one hundred fourteen.
-/

/-- A value already seen before a clock cannot recur at that clock when
the clock exceeds the value: subtraction demands freshness and addition
overshoots. -/
theorem value_no_late_recurrence {v w m : Nat}
    (hwit : a w = v) (hwm : w < m) (hvm : v < m)
    (hmin : a m = v) : False := by
  have hmem : v ∈ valuesThrough w :=
    mem_valuesThrough_iff.mpr ⟨w, Nat.le_refl _, hwit⟩
  have hseen : v ∈ valuesThrough (m - 1) :=
    valuesThrough_mono (by omega) hmem
  have hsucc : m - 1 + 1 = m := by omega
  have hgoal : a (m - 1 + 1) = v := by
    rw [hsucc]
    exact hmin
  exact (a_succ_ne_of_seen hseen (by omega)) hgoal

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- A replay whose target exceeds forty-seven has its permanent tail begin
after time 222, where the orbit still visits forty-seven. -/
theorem tailStart_bound_mid
    (_r : TerminalExactDischargeReplayCertificate source)
    (hdeep : 47 < target) : 222 < source.tailStart := by
  by_cases hbound : 222 < source.tailStart
  · exact hbound
  · have hle : source.tailStart ≤ 222 := by omega
    have habove := source.historical_tail.strictly_above 222 hle
    have hval : a 222 = 47 := by
      set_option maxRecDepth 100000 in decide
    omega

/-- A replay whose target exceeds one hundred ten has its permanent tail
begin after time 367, where the orbit still visits one hundred ten. -/
theorem tailStart_bound_deep
    (_r : TerminalExactDischargeReplayCertificate source)
    (hdeep : 110 < target) : 367 < source.tailStart := by
  by_cases hbound : 367 < source.tailStart
  · exact hbound
  · have hle : source.tailStart ≤ 367 := by omega
    have habove := source.historical_tail.strictly_above 367 hle
    have hval : a 367 = 110 := by
      set_option maxRecDepth 100000 in decide
    omega

/-- A replay whose target exceeds one hundred nine has its permanent tail
begin after time 369, where the orbit still visits one hundred nine. -/
theorem tailStart_bound_deeper
    (_r : TerminalExactDischargeReplayCertificate source)
    (hdeep : 109 < target) : 369 < source.tailStart := by
  by_cases hbound : 369 < source.tailStart
  · exact hbound
  · have hle : source.tailStart ≤ 369 := by omega
    have habove := source.historical_tail.strictly_above 369 hle
    have hval : a 369 = 109 := by
      set_option maxRecDepth 100000 in decide
    omega

/-- A replay whose target exceeds one hundred eight has its permanent tail
begin after time 371, where the orbit still visits one hundred eight. -/
theorem tailStart_bound_deepest
    (_r : TerminalExactDischargeReplayCertificate source)
    (hdeep : 108 < target) : 371 < source.tailStart := by
  by_cases hbound : 371 < source.tailStart
  · exact hbound
  · have hle : source.tailStart ≤ 371 := by omega
    have habove := source.historical_tail.strictly_above 371 hle
    have hval : a 371 = 108 := by
      set_option maxRecDepth 100000 in decide
    omega

/-- Clock thirty-two straddles the band `(46, 79]`, but the downcross
prefix bound caps the target at sixty-three.  Sixty-one is already
eliminated and every other member occurs in the orbit by time 222. -/
theorem crossingTime_ne_thirtytwo
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 32 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hmissing := r.target_missing
  have hlow : 46 < target := by
    have hvalue : a 32 = 46 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have helig := r.eligible
  have htime := r.time_eq
  have habove := source.downcross.start_at_or_above
  have hdlt : source.downTime < 32 := by omega
  have hall : ∀ t', t' < 32 → a t' ≤ 63 := by
    set_option maxRecDepth 100000 in decide
  have hdown := hall source.downTime hdlt
  have hhigh : target ≤ 63 := by omega
  have hne61 := r.target_ne_sixtyone
  have hcases : target = 47 ∨ target = 48 ∨ target = 49 ∨ target = 50 ∨
      target = 51 ∨ target = 52 ∨ target = 53 ∨ target = 54 ∨
      target = 55 ∨ target = 56 ∨ target = 57 ∨ target = 58 ∨
      target = 59 ∨ target = 60 ∨ target = 62 ∨ target = 63 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ⟨222, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨220, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨218, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨216, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨214, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨212, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨210, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨208, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨206, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨204, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨202, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨200, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨198, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨196, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨19, by set_option maxRecDepth 100000 in decide⟩ hmissing
  · exact absurd ⟨21, by set_option maxRecDepth 100000 in decide⟩ hmissing

/-- Clock thirty-three is a running orbit record (`a 33 = 79`), which a
replay crossing can never be. -/
theorem crossingTime_ne_thirtythree
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 33 := by
  intro heq
  rcases r.crossingTime_not_record with ⟨t, htlt, hgt⟩
  rw [heq] at htlt hgt
  have hall : ∀ t', t' < 33 → a t' < a 33 := by
    set_option maxRecDepth 100000 in decide
  have := hall t htlt
  omega

/-- Clock thirty-five straddles `(78, 114]`.  Its history is pinned below
clock thirty-five, so the minimum predecessor value is at most 79 — too
small — or exactly 113, whose successor 114 is seen at time 36 while the
pinned minimum clock lies beyond time 222. -/
theorem crossingTime_ne_thirtyfive
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 35 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 78 < target := by
    have hvalue : a 35 = 78 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 222 < source.tailStart := r.tailStart_bound_mid (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin222 : 222 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 35 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 35 → a t' ≤ 79 ∨ a t' = 113 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with hle | h113
  · omega
  · have hmin : a source.historicalMinimumTime = 114 := by omega
    have hwit : a 36 = 114 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clocks thirty-four and thirty-six through sixty-four die mechanically:
the actual orbit step subtracts at the high clocks and the descending low
rail fails the clock bound at the even clocks from thirty-eight on. -/
theorem sixtyfive_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    65 ≤ r.crossingTime := by
  have hfloor := r.thirtytwo_le_crossingTime
  by_cases hbig : 65 ≤ r.crossingTime
  · exact hbig
  · have hne32 := r.crossingTime_ne_thirtytwo
    have hne33 := r.crossingTime_ne_thirtythree
    have hne35 := r.crossingTime_ne_thirtyfive
    have hforced := r.forced_addition_at_crossing
    have hclock := r.clock_lt_crossingValue
    have hcases : r.crossingTime = 34 ∨ r.crossingTime = 36 ∨
        r.crossingTime = 37 ∨ r.crossingTime = 38 ∨
        r.crossingTime = 39 ∨ r.crossingTime = 40 ∨
        r.crossingTime = 41 ∨ r.crossingTime = 42 ∨
        r.crossingTime = 43 ∨ r.crossingTime = 44 ∨
        r.crossingTime = 45 ∨ r.crossingTime = 46 ∨
        r.crossingTime = 47 ∨ r.crossingTime = 48 ∨
        r.crossingTime = 49 ∨ r.crossingTime = 50 ∨
        r.crossingTime = 51 ∨ r.crossingTime = 52 ∨
        r.crossingTime = 53 ∨ r.crossingTime = 54 ∨
        r.crossingTime = 55 ∨ r.crossingTime = 56 ∨
        r.crossingTime = 57 ∨ r.crossingTime = 58 ∨
        r.crossingTime = 59 ∨ r.crossingTime = 60 ∨
        r.crossingTime = 61 ∨ r.crossingTime = 62 ∨
        r.crossingTime = 63 ∨ r.crossingTime = 64 := by omega
    rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq |
      heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq |
      heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)

/-- Clock sixty-five straddles `(91, 157]`.  The pinned minimum
predecessor is at most 92 — too small — or one of 113, 114, whose
successors 114, 115 are seen by time 170 while the pinned minimum clock
lies beyond time 222. -/
theorem crossingTime_ne_sixtyfive
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 65 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 91 < target := by
    have hvalue : a 65 = 91 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 222 < source.tailStart := r.tailStart_bound_mid (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin222 : 222 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 65 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 65 → a t' ≤ 92 ∨ a t' = 113 ∨ a t' = 114 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with hle | h113 | h114
  · omega
  · have hmin : a source.historicalMinimumTime = 114 := by omega
    have hwit : a 36 = 114 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 115 := by omega
    have hwit : a 170 = 115 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clock sixty-six is a running orbit record (`a 66 = 157`), which a
replay crossing can never be. -/
theorem crossingTime_ne_sixtysix
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 66 := by
  intro heq
  rcases r.crossingTime_not_record with ⟨t, htlt, hgt⟩
  rw [heq] at htlt hgt
  have hall : ∀ t', t' < 66 → a t' < a 66 := by
    set_option maxRecDepth 100000 in decide
  have := hall t htlt
  omega

/-- Clock sixty-eight straddles `(156, 225]`.  The pinned minimum
predecessor is at most 157 — too small — or exactly 224, whose successor
225 is seen at time 69 while the pinned minimum clock lies beyond time
367. -/
theorem crossingTime_ne_sixtyeight
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 68 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 156 < target := by
    have hvalue : a 68 = 156 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 367 < source.tailStart := r.tailStart_bound_deep (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin367 : 367 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 68 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 68 → a t' ≤ 157 ∨ a t' = 224 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with hle | h224
  · omega
  · have hmin : a source.historicalMinimumTime = 225 := by omega
    have hwit : a 69 = 225 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clock seventy straddles `(155, 226]`.  The pinned minimum predecessor
is at most 156 — too small — or one of 157, 224, 225, whose successors
158, 225, 226 are seen by time 88 while the pinned minimum clock lies
beyond time 367. -/
theorem crossingTime_ne_seventy
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 70 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 155 < target := by
    have hvalue : a 70 = 155 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 367 < source.tailStart := r.tailStart_bound_deep (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin367 : 367 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 70 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 70 → a t' ≤ 156 ∨ a t' = 157 ∨ a t' = 224 ∨
      a t' = 225 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with
    hle | h157 | h224 | h225
  · omega
  · have hmin : a source.historicalMinimumTime = 158 := by omega
    have hwit : a 88 = 158 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 225 := by omega
    have hwit : a 69 = 225 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 226 := by omega
    have hwit : a 71 = 226 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clock seventy-two straddles `(154, 227]`.  The pinned minimum
predecessor is at most 155 — too small — or one of 156, 157, 224, 225,
226, whose successors are all seen by time 88 while the pinned minimum
clock lies beyond time 367. -/
theorem crossingTime_ne_seventytwo
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 72 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 154 < target := by
    have hvalue : a 72 = 154 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 367 < source.tailStart := r.tailStart_bound_deep (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin367 : 367 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 72 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 72 → a t' ≤ 155 ∨ a t' = 156 ∨ a t' = 157 ∨
      a t' = 224 ∨ a t' = 225 ∨ a t' = 226 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with
    hle | h156 | h157 | h224 | h225 | h226
  · omega
  · have hmin : a source.historicalMinimumTime = 157 := by omega
    have hwit : a 66 = 157 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 158 := by omega
    have hwit : a 88 = 158 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 225 := by omega
    have hwit : a 69 = 225 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 226 := by omega
    have hwit : a 71 = 226 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 227 := by omega
    have hwit : a 73 = 227 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clock seventy-four straddles `(153, 228]`.  The pinned minimum
predecessor is at most 154 — too small — or one of 155, 156, 157, 224,
225, 226, 227, whose successors are all seen by time 88 while the pinned
minimum clock lies beyond time 367. -/
theorem crossingTime_ne_seventyfour
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 74 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 153 < target := by
    have hvalue : a 74 = 153 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 367 < source.tailStart := r.tailStart_bound_deep (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin367 : 367 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 74 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 74 → a t' ≤ 154 ∨ a t' = 155 ∨ a t' = 156 ∨
      a t' = 157 ∨ a t' = 224 ∨ a t' = 225 ∨ a t' = 226 ∨
      a t' = 227 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with
    hle | h155 | h156 | h157 | h224 | h225 | h226 | h227
  · omega
  · have hmin : a source.historicalMinimumTime = 156 := by omega
    have hwit : a 68 = 156 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 157 := by omega
    have hwit : a 66 = 157 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 158 := by omega
    have hwit : a 88 = 158 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 225 := by omega
    have hwit : a 69 = 225 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 226 := by omega
    have hwit : a 71 = 226 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 227 := by omega
    have hwit : a 73 = 227 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 228 := by omega
    have hwit : a 75 = 228 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Unconditional fourth floor: past the seven genuine survivors the comb
is mechanical up to clock ninety-nine, so the replay crossing clock is at
least one hundred. -/
theorem onehundred_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    100 ≤ r.crossingTime := by
  have hfloor := r.sixtyfive_le_crossingTime
  by_cases hbig : 100 ≤ r.crossingTime
  · exact hbig
  · have hne65 := r.crossingTime_ne_sixtyfive
    have hne66 := r.crossingTime_ne_sixtysix
    have hne68 := r.crossingTime_ne_sixtyeight
    have hne70 := r.crossingTime_ne_seventy
    have hne72 := r.crossingTime_ne_seventytwo
    have hne74 := r.crossingTime_ne_seventyfour
    have hforced := r.forced_addition_at_crossing
    have hclock := r.clock_lt_crossingValue
    have hcases : r.crossingTime = 67 ∨ r.crossingTime = 69 ∨
        r.crossingTime = 71 ∨ r.crossingTime = 73 ∨
        r.crossingTime = 75 ∨ r.crossingTime = 76 ∨
        r.crossingTime = 77 ∨ r.crossingTime = 78 ∨
        r.crossingTime = 79 ∨ r.crossingTime = 80 ∨
        r.crossingTime = 81 ∨ r.crossingTime = 82 ∨
        r.crossingTime = 83 ∨ r.crossingTime = 84 ∨
        r.crossingTime = 85 ∨ r.crossingTime = 86 ∨
        r.crossingTime = 87 ∨ r.crossingTime = 88 ∨
        r.crossingTime = 89 ∨ r.crossingTime = 90 ∨
        r.crossingTime = 91 ∨ r.crossingTime = 92 ∨
        r.crossingTime = 93 ∨ r.crossingTime = 94 ∨
        r.crossingTime = 95 ∨ r.crossingTime = 96 ∨
        r.crossingTime = 97 ∨ r.crossingTime = 98 ∨
        r.crossingTime = 99 := by omega
    rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq |
      heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq |
      heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)

/-- Clock one hundred straddles `(164, 265]`.  The pinned minimum
predecessor is at most 165 — too small — or one of 224 through 228, whose
successors are seen by time 285 while the pinned minimum clock lies
beyond time 367. -/
theorem crossingTime_ne_onehundred
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 100 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 164 < target := by
    have hvalue : a 100 = 164 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 367 < source.tailStart := r.tailStart_bound_deep (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin367 : 367 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 100 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 100 → a t' ≤ 165 ∨ a t' = 224 ∨ a t' = 225 ∨
      a t' = 226 ∨ a t' = 227 ∨ a t' = 228 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with
    hle | h224 | h225 | h226 | h227 | h228
  · omega
  · have hmin : a source.historicalMinimumTime = 225 := by omega
    have hwit : a 69 = 225 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 226 := by omega
    have hwit : a 71 = 226 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 227 := by omega
    have hwit : a 73 = 227 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 228 := by omega
    have hwit : a 75 = 228 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 229 := by omega
    have hwit : a 285 = 229 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clock one hundred one is a running orbit record (`a 101 = 265`),
which a replay crossing can never be. -/
theorem crossingTime_ne_onehundredone
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 101 := by
  intro heq
  rcases r.crossingTime_not_record with ⟨t, htlt, hgt⟩
  rw [heq] at htlt hgt
  have hall : ∀ t', t' < 101 → a t' < a 101 := by
    set_option maxRecDepth 100000 in decide
  have := hall t htlt
  omega

/-- Clock one hundred three straddles `(264, 368]`.  The pinned minimum
predecessor is at most 265 — too small — or exactly 367, whose successor
368 is seen at time 104 while the pinned minimum clock lies beyond time
369. -/
theorem crossingTime_ne_onehundredthree
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 103 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 264 < target := by
    have hvalue : a 103 = 264 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 369 < source.tailStart :=
    r.tailStart_bound_deeper (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin369 : 369 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 103 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 103 → a t' ≤ 265 ∨ a t' = 367 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with hle | h367
  · omega
  · have hmin : a source.historicalMinimumTime = 368 := by omega
    have hwit : a 104 = 368 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clock one hundred five straddles `(263, 369]`.  The pinned minimum
predecessor is at most 264 — too small — or one of 265, 367, 368, whose
successors 266, 368, 369 are seen by time 187 while the pinned minimum
clock lies beyond time 369. -/
theorem crossingTime_ne_onehundredfive
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 105 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 263 < target := by
    have hvalue : a 105 = 263 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 369 < source.tailStart :=
    r.tailStart_bound_deeper (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin369 : 369 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 105 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 105 → a t' ≤ 264 ∨ a t' = 265 ∨ a t' = 367 ∨
      a t' = 368 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with
    hle | h265 | h367 | h368
  · omega
  · have hmin : a source.historicalMinimumTime = 266 := by omega
    have hwit : a 187 = 266 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 368 := by omega
    have hwit : a 104 = 368 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 369 := by omega
    have hwit : a 106 = 369 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clock one hundred seven straddles `(262, 370]`.  The pinned minimum
predecessor is at most 263 — too small — or one of 264, 265, 367, 368,
369, whose successors are seen by time 187 while the pinned minimum clock
lies beyond time 371. -/
theorem crossingTime_ne_onehundredseven
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 107 := by
  intro heq
  have hstraddle := r.crossing_straddles_target
  rw [heq] at hstraddle
  have hlow : 262 < target := by
    have hvalue : a 107 = 262 := by
      set_option maxRecDepth 100000 in decide
    have := hstraddle.1
    omega
  have htail : 371 < source.tailStart :=
    r.tailStart_bound_deepest (by omega)
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin371 : 371 < source.historicalMinimumTime := by omega
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hfbound : source.historicalFirstTime < 107 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have hall : ∀ t', t' < 107 → a t' ≤ 263 ∨ a t' = 264 ∨ a t' = 265 ∨
      a t' = 367 ∨ a t' = 368 ∨ a t' = 369 := by
    set_option maxRecDepth 100000 in decide
  rcases hall source.historicalFirstTime hfbound with
    hle | h264 | h265 | h367 | h368 | h369
  · omega
  · have hmin : a source.historicalMinimumTime = 265 := by omega
    have hwit : a 101 = 265 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 266 := by omega
    have hwit : a 187 = 266 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 368 := by omega
    have hwit : a 104 = 368 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 369 := by omega
    have hwit : a 106 = 369 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin
  · have hmin : a source.historicalMinimumTime = 370 := by omega
    have hwit : a 108 = 370 := by
      set_option maxRecDepth 100000 in decide
    exact value_no_late_recurrence hwit (by omega) (by omega) hmin

/-- Clocks one hundred two through one hundred eleven die mechanically:
the actual orbit step subtracts everywhere except clock one hundred
eleven, whose low value forty fails the clock bound.  Hence the replay
crossing clock is at least one hundred twelve. -/
theorem onehundredtwelve_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    112 ≤ r.crossingTime := by
  have hfloor := r.onehundred_le_crossingTime
  by_cases hbig : 112 ≤ r.crossingTime
  · exact hbig
  · have hne100 := r.crossingTime_ne_onehundred
    have hne101 := r.crossingTime_ne_onehundredone
    have hne103 := r.crossingTime_ne_onehundredthree
    have hne105 := r.crossingTime_ne_onehundredfive
    have hne107 := r.crossingTime_ne_onehundredseven
    have hforced := r.forced_addition_at_crossing
    have hclock := r.clock_lt_crossingValue
    have hcases : r.crossingTime = 102 ∨ r.crossingTime = 104 ∨
        r.crossingTime = 106 ∨ r.crossingTime = 108 ∨
        r.crossingTime = 109 ∨ r.crossingTime = 110 ∨
        r.crossingTime = 111 := by omega
    rcases hcases with heq | heq | heq | heq | heq | heq | heq
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hforced
      exact absurd hforced (by set_option maxRecDepth 100000 in decide)
    · rw [heq] at hclock
      exact absurd hclock (by set_option maxRecDepth 100000 in decide)

/-- The replay target is at least one hundred fourteen. -/
theorem onehundredfourteen_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    114 ≤ target := by
  have hclock := r.crossingTime_lt_target
  have hfloor := r.onehundredtwelve_le_crossingTime
  omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
