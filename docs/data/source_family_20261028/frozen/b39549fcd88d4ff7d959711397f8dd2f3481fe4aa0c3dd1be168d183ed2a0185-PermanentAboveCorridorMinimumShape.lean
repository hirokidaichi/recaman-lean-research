import Recaman.PermanentAboveCorridorSixtyoneElimination

namespace Recaman

noncomputable section

/-! # General shape restriction of the minimum predecessor

The nineteen and sixty-one eliminations both exploited one pattern: a
subtraction immediately repaid by a forced addition after the minimum
predecessor's first occurrence reproduces the tail minimum value early, and
the late revisit is then dynamically impossible.  This module states the
pattern once, for every surviving replay.

Whenever the early clock and value stay below the minimum time — which the
tail-start bounds provide in every concrete case — the two steps after the
predecessor first occurrence cannot subtract and then add.  The surviving
replays are thereby restricted to predecessors whose follow-up either adds
immediately or subtracts twice, a purely local dichotomy that the next
epoch can attack clock by clock.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- General elimination template: a subtract-then-add follow-up of the
minimum predecessor reproduces the tail minimum value early, which the
revisit dynamics forbid. -/
theorem no_subAdd_minimum_predecessor
    (_r : TerminalExactDischargeReplayCertificate source)
    (hsub : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime))
    (hadd : ¬ CanSubtract (source.historicalFirstTime + 2)
      (stateAt (source.historicalFirstTime + 1)))
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    False := by
  have hearly := a_sub_then_add_eq_succ hsub hadd
  have hpred := source.historical_minimum.predecessor_first
  have hp1 : a source.historicalFirstTime =
      a source.historicalMinimumTime - 1 := hpred.1
  have htgt := source.historical_minimum.target_lt_predecessor
  have hmin : a (source.historicalFirstTime + 2) =
      a source.historicalMinimumTime := by omega
  have hmem : a source.historicalMinimumTime ∈
      valuesThrough (source.historicalFirstTime + 2) := by
    rw [← hmin]
    exact mem_valuesThrough_iff.mpr
      ⟨source.historicalFirstTime + 2, Nat.le_refl _, rfl⟩
  have hseen : a source.historicalMinimumTime ∈
      valuesThrough (source.historicalMinimumTime - 1) :=
    valuesThrough_mono (by omega) hmem
  have hsucc : source.historicalMinimumTime - 1 + 1 =
      source.historicalMinimumTime := by omega
  have hgoal : a (source.historicalMinimumTime - 1 + 1) =
      a source.historicalMinimumTime := by
    rw [hsucc]
  exact (a_succ_ne_of_seen hseen (by omega)) hgoal

/-- Shape restriction: under the order bounds, the minimum predecessor's
follow-up adds immediately or subtracts twice. -/
theorem minimum_predecessor_shape
    (r : TerminalExactDischargeReplayCertificate source)
    (hvalue : a source.historicalFirstTime + 1 <
      source.historicalMinimumTime)
    (horder : source.historicalFirstTime + 2 <
      source.historicalMinimumTime) :
    ¬ CanSubtract (source.historicalFirstTime + 1)
        (stateAt source.historicalFirstTime) ∨
      CanSubtract (source.historicalFirstTime + 2)
        (stateAt (source.historicalFirstTime + 1)) := by
  by_cases hsub : CanSubtract (source.historicalFirstTime + 1)
      (stateAt source.historicalFirstTime)
  · by_cases hadd : CanSubtract (source.historicalFirstTime + 2)
        (stateAt (source.historicalFirstTime + 1))
    · exact Or.inr hadd
    · exact False.elim
        (r.no_subAdd_minimum_predecessor hsub hadd hvalue horder)
  · exact Or.inl hsub

end TerminalExactDischargeReplayCertificate

end

end Recaman
