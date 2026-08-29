import Recaman.PermanentAboveCorridorNineteenTail

namespace Recaman

noncomputable section

/-! # The nineteen counterexample forces a twenty-one revisit

The pinned tail minimum turns the nineteen counterexample into a concrete
prediction about the future orbit: its permanent tail attains the minimum
value twenty-one at some time after 131.  In the kernel-checked prefix the
orbit visits twenty-one exactly once, at time nine, so the counterexample
demands a genuine second visit far beyond everything verified so far.

Contrapositively, if twenty-one never recurs after time 131 then no
nineteen replay exists at all.  The nineteen question is thereby wedged
between two concrete orbit events: the empirical first occurrence of
nineteen at time 99734, and the recurrence of twenty-one after the
verified prefix.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The nineteen counterexample forces the orbit to revisit twenty-one
after time 131. -/
theorem nineteen_forces_twentyone_revisit
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    ∃ t, 131 < t ∧ a t = 21 := by
  have hmin := r.nineteen_minimum_pins h19
  have htail := r.nineteen_tailStart_bound h19
  have hle := source.historical_minimum.minimum.start_le_time
  exact ⟨source.historicalMinimumTime, by omega, hmin.2⟩

/-- Contrapositive: without a late twenty-one revisit there is no nineteen
replay. -/
theorem target_ne_nineteen_of_no_twentyone_revisit
    (r : TerminalExactDischargeReplayCertificate source)
    (hno : ¬ ∃ t, 131 < t ∧ a t = 21) :
    target ≠ 19 :=
  fun h19 => hno (r.nineteen_forces_twentyone_revisit h19)

end TerminalExactDischargeReplayCertificate

end

end Recaman
