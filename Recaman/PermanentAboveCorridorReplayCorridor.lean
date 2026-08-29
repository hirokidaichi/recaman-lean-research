import Recaman.PermanentAboveCorridorReplayPinning

namespace Recaman

noncomputable section

/-! # Finite corridor band of the replay fixed point

The pinned replay cycle confines every stored cursor of the self-recurrent
discharge to an initial segment of the orbit.  The crossing clock is
strictly below the crossing value, which is itself below the target, so the
crossing time — and with it the return, the old crossing, the downcross
endpoint, the blocker first time, and the fresh endpoint — all live strictly
below `target`.  Between the downcross endpoint and the crossing the orbit
never reaches the target, so the whole cycle is a below-target corridor.

Small clocks are excluded by kernel computation: `a 0 = 0`, `a 1 = 1`, and
`a 2 = 3` all fail `time + 1 < a time`, so a replay crossing needs clock at
least three and hence target at least five.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The replay crossing clock lies strictly below the target. -/
theorem crossingTime_lt_target
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime + 1 < target := by
  have hclock := r.clock_lt_crossingValue
  have hbelow := r.crossing_straddles_target.1
  omega

/-- The whole cycle from the downcross endpoint to the crossing stays
strictly below the target. -/
theorem all_below_up_to_crossing
    (r : TerminalExactDischargeReplayCertificate source) :
    ∀ t, source.downTime + 1 ≤ t → t ≤ r.crossingTime → a t < target := by
  intro t hstart hfinish
  by_cases hbelow : a t < target
  · exact hbelow
  · have hge : target ≤ a t := Nat.le_of_not_lt hbelow
    rcases exists_weakUpcrossingStep_between hstart
        source.downcross.endpoint_below hge with
      ⟨witness, hwitness, hwitnessBefore⟩
    have hfirst := r.canonicalReturn_is_oldCrossing
    have hbeforeCrossing : witness < source.oldCrossingTime := by
      have htime := r.time_eq
      omega
    exact False.elim (hfirst.first witness hbeforeCrossing hwitness)

/-- Every stored time cursor of the self-recurrent discharge lies strictly
below the target. -/
theorem cursor_band
    (r : TerminalExactDischargeReplayCertificate source) :
    source.downTime + 1 < target ∧ source.returnTime < target ∧
      source.oldCrossingTime < target ∧ r.firstTime < target ∧
      r.freshEndpoint < target := by
  have hclock := r.crossingTime_lt_target
  have htime := r.time_eq
  have hreturn := r.return_eq_crossingTime
  have hendpoint := r.endpoint_le_crossingTime
  have hfirstTime := r.firstTime_lt_crossingTime
  have hfresh := r.historical.fresh.fresh_le_return
  omega

/-- The replay crossing anchor is one of the finitely many strict-crossing
anchor candidates. -/
theorem anchor_mem_candidates
    (r : TerminalExactDischargeReplayCertificate source) :
    parent.anchorParent ∈ terminalCrossingAnchorCandidates target := by
  rw [mem_terminalCrossingAnchorCandidates_iff, ← r.anchor_eq]
  exact r.crossing_straddles_target.1

/-- Kernel computation excludes clocks below three. -/
theorem three_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    3 ≤ r.crossingTime := by
  have hclock := r.clock_lt_crossingValue
  by_cases hlarge : 3 ≤ r.crossingTime
  · exact hlarge
  · have hcases : r.crossingTime = 0 ∨ r.crossingTime = 1 ∨
        r.crossingTime = 2 := by omega
    rcases hcases with heq | heq | heq <;> rw [heq] at hclock <;>
      exact absurd hclock (by decide)

/-- Hence a replay fixed point forces the target to be at least five. -/
theorem five_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    5 ≤ target := by
  have hclock := r.crossingTime_lt_target
  have hthree := r.three_le_crossingTime
  omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
