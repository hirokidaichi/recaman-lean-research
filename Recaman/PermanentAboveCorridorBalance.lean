import Recaman.PermanentAboveCorridorTerminal

namespace Recaman

noncomputable section

/-! # Common crossing balance of both terminal corridor shapes

The immediate historical valley and the terminal all-forced window have a
common final transition: a forced strict upcrossing of a missing target.
The target gap below and overshoot above partition the final addition clock.
This gives both branches the same positive, clock-bounded arithmetic data.
-/

/-- Arithmetic shared by every forced strict crossing of a missing target. -/
structure StrictTerminalCrossingBalance
    (target returnTime : Nat) : Prop where
  target_missing : ¬ ∃ witness, a witness = target
  predecessor_below : a returnTime < target
  endpoint_above : target < a (returnTime + 1)
  forced_addition : ¬ CanSubtract (returnTime + 1)
    (stateAt returnTime)
  final_equation : a (returnTime + 1) =
    a returnTime + (returnTime + 1)
  target_gap_positive : 0 < target - a returnTime
  overshoot_positive : 0 < a (returnTime + 1) - target
  gap_add_overshoot :
    (target - a returnTime) + (a (returnTime + 1) - target) =
      returnTime + 1
  target_gap_le_clock : target - a returnTime ≤ returnTime
  overshoot_le_clock : a (returnTime + 1) - target ≤ returnTime

/-- Missing-target provenance makes every weak forced upcrossing strict and
its two positive sides partition the addition clock. -/
theorem WeakUpcrossingStep.strictTerminalCrossingBalance
    {target start returnTime : Nat}
    (h : WeakUpcrossingStep target start returnTime)
    (htargetMissing : ¬ ∃ witness, a witness = target) :
    StrictTerminalCrossingBalance target returnTime := by
  have hendpointNe : a (returnTime + 1) ≠ target := by
    intro hequal
    exact htargetMissing ⟨returnTime + 1, hequal⟩
  have hendpointAbove : target < a (returnTime + 1) :=
    Nat.lt_of_le_of_ne h.endpoint_ge (Ne.symm hendpointNe)
  have hequation := a_succ_of_not_canSubtract h.forced_addition
  have hbelow := h.below
  have hgapPositive : 0 < target - a returnTime := by omega
  have hoverPositive : 0 < a (returnTime + 1) - target := by omega
  have hpartition :
      (target - a returnTime) + (a (returnTime + 1) - target) =
        returnTime + 1 := by
    omega
  have hgapLe : target - a returnTime ≤ returnTime := by omega
  have hoverLe : a (returnTime + 1) - target ≤ returnTime := by omega
  exact {
    target_missing := htargetMissing
    predecessor_below := h.below
    endpoint_above := hendpointAbove
    forced_addition := h.forced_addition
    final_equation := hequation
    target_gap_positive := hgapPositive
    overshoot_positive := hoverPositive
    gap_add_overshoot := hpartition
    target_gap_le_clock := hgapLe
    overshoot_le_clock := hoverLe
  }

/-- Common terminal data: a fresh below-target endpoint, its canonical first
return, and the branch-independent strict crossing balance. -/
structure NormalizedTerminalCrossingData
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop where
  fresh_endpoint : ∃ freshEndpoint,
    source.downTime + 1 ≤ freshEndpoint ∧
    freshEndpoint ≤ source.returnTime ∧
    FirstAt a (a freshEndpoint) freshEndpoint ∧
    a freshEndpoint < target ∧
    FirstWeakUpcrossingStep target freshEndpoint source.returnTime
  balance : StrictTerminalCrossingBalance target source.returnTime

/-- Either normalized terminal branch yields the same fresh-endpoint and
gap-partition interface. -/
theorem PermanentTailDischargeTerminalShape.normalizedCrossingData
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : PermanentTailDischargeTerminalShape source) :
    NormalizedTerminalCrossingData source := by
  cases h with
  | immediate_valley certificate =>
      exact {
        fresh_endpoint := ⟨source.downTime + 1, Nat.le_refl _,
          Nat.le_of_eq (Eq.symm certificate.return_eq),
          source.endpoint_first, certificate.endpoint_below,
          source.return_crossing⟩
        balance := source.return_crossing.crossing
          |>.strictTerminalCrossingBalance certificate.target_missing
      }
  | finite_crossing_window terminalEndpoint origin_le window =>
      exact {
        fresh_endpoint := ⟨terminalEndpoint, origin_le,
          Nat.le_of_lt window.certificate.endpoint_before_return,
          window.certificate.suffix.endpoint_first,
          window.certificate.suffix.endpoint_below,
          window.certificate.suffix.first_return⟩
        balance := window.certificate.suffix.first_return.crossing
          |>.strictTerminalCrossingBalance
            window.certificate.target_missing
      }

/-- The common balance is available directly from every typed discharge;
the terminal normalization additionally records its final fresh endpoint. -/
theorem PermanentTailDischargeReturnCertificate.strictTerminalCrossingBalance
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    StrictTerminalCrossingBalance target h.returnTime :=
  h.return_crossing.crossing.strictTerminalCrossingBalance
    h.combined.tail.target_missing

/-- Strong normalization packages the common balance together with the final
fresh below-target endpoint. -/
theorem PermanentTailDischargeReturnCertificate.normalizedTerminalCrossingData
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    NormalizedTerminalCrossingData h :=
  h.terminalShape.normalizedCrossingData

end

end Recaman
