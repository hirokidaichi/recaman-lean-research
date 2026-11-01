import Recaman.PermanentAboveCorridorMinimumFollowUp

namespace Recaman

noncomputable section

/-! # A replay crossing is never an orbit record

The discharge downcross starts at or above the missing target, and the
straddle keeps the crossing value strictly below it.  So every replay
crossing is dominated by an earlier orbit value: it can never be a running
maximum.  Record-setting forced additions — the upper teeth of the
Recamán comb, where the orbit first exceeds all previous values — are
thereby excluded as replay clocks wholesale, without inspecting their
straddle bands.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The downcross value strictly dominates the replay crossing value. -/
theorem crossing_below_downcross
    (r : TerminalExactDischargeReplayCertificate source) :
    a r.crossingTime < a source.downTime := by
  have hstraddle := r.crossing_straddles_target.1
  have habove := source.downcross.start_at_or_above
  omega

/-- A replay crossing is dominated by a strictly earlier orbit value, so it
is never a running maximum. -/
theorem crossingTime_not_record
    (r : TerminalExactDischargeReplayCertificate source) :
    ∃ t, t < r.crossingTime ∧ a r.crossingTime < a t := by
  have heligible := r.eligible
  have htime := r.time_eq
  exact ⟨source.downTime, by omega, r.crossing_below_downcross⟩

end TerminalExactDischargeReplayCertificate

end

end Recaman
