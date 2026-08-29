import Recaman.PermanentAboveCorridorNineteenMinimum

namespace Recaman

noncomputable section

/-! # Tail bounds of the nineteen counterexample

The permanent tail of a nineteen counterexample must sit strictly above
nineteen forever, but the actual orbit still visits four at time 131.  The
tail therefore cannot start before time 132, and with it the tail start,
the certificate start, and the history horizon are all pushed beyond the
kernel-checked prefix.

Combined with the earlier pins this leaves a striking split: every stored
historical component of the nineteen counterexample lives at clock at most
nine, while its permanent tail begins after time 131 — beyond every low
value the kernel can reach — and its first genuinely unknown ingredient is
whether the orbit returns below twenty after that prefix.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The nineteen tail starts after time 131: the orbit still visits four
there. -/
theorem nineteen_tailStart_bound
    (_r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    131 < source.tailStart := by
  by_cases hbound : 131 < source.tailStart
  · exact hbound
  · have hle : source.tailStart ≤ 131 := by omega
    have habove := source.historical_tail.strictly_above 131 hle
    have hval : a 131 = 4 := by
      set_option maxRecDepth 100000 in decide
    omega

/-- Start and horizon of the nineteen counterexample lie beyond the
kernel-checked prefix as well. -/
theorem nineteen_horizon_bounds
    (r : TerminalExactDischargeReplayCertificate source)
    (h19 : target = 19) :
    131 < start ∧ 132 < parent.horizon := by
  have htail := r.nineteen_tailStart_bound h19
  have _ := r
  have hstart := source.tailStart_le_start
  have hhorizon :=
    source.combined.crossing.tail_strictly_before_horizon
  omega

end TerminalExactDischargeReplayCertificate

end

end Recaman
