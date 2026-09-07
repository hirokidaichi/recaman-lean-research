import Recaman.PermanentAboveClock112FirstOccurrence
import Recaman.DeepNineteenTraceCertificate

namespace Recaman

/-!
# Closing the clock-112 replay obstruction

The certified first occurrence of 371 pins the historical minimum at
clock 4825. A clock-112 replay therefore forbids any later value at or
below its target. The independently kernel-checked value 19 at clock
99734 contradicts that prohibition, since every replay target is at
least 114.

This closes the finite obligation in issue #61. It excludes clock 112
for the full permanent-tail replay certificate; the ordinary canonical
orbit still has the local crossing 152 < 223 <= 265 at that clock.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- No extra low-witness, coverage, or oracle hypothesis is needed to
exclude the clock-112 replay. -/
theorem crossingTime_ne_onehundredtwelve
    (r : TerminalExactDischargeReplayCertificate source) :
    r.crossingTime ≠ 112 := by
  intro hclock
  have htarget := r.onehundredfourteen_le_target
  apply r.no_low_witness_at_or_after_4825_of_crossingTime_eq_112
    hclock 99734 (by decide)
  rw [GeneratedBalancedTrace99734.generated_value]
  omega

/-- The existing replay floor rises strictly above 112. -/
theorem onehundredthirteen_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    113 ≤ r.crossingTime := by
  have hfloor := r.onehundredtwelve_le_crossingTime
  have hne := r.crossingTime_ne_onehundredtwelve
  omega

/-- The corresponding target floor follows from the existing strict
clock/target separation. -/
theorem onehundredfifteen_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    115 ≤ target := by
  have hclock := r.onehundredthirteen_le_crossingTime
  have htarget := r.crossingTime_lt_target
  omega

end TerminalExactDischargeReplayCertificate
end Recaman
