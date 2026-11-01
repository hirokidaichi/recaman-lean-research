import Recaman.PermanentAboveCorridorHistoryLanding

namespace Recaman

noncomputable section

/-! # Horizon bounds for anchored fresh landings

The anchored interface recovers a fresh below-target landing behind every
history edge, but by itself the landing time carries no horizon bound, so
it cannot yet be mounted on the parent's history node.

The permanent-tail context supplies the bound after the fact.  Every value
below the missing target already occurs by the tail start, and the first
occurrence is minimal, so the landing lies at or before the tail start.
Because the tail is strictly above the target from its start, a weak
upcrossing exists between the landing and the start, and the canonical
first crossing is no later.  The start itself precedes the parent horizon.
Hence both the landing and its restart crossing live strictly inside the
parent's history — exactly the shape required by the installed crossing
node `⟨parent.horizon, a c, .normal, a c⟩`.
-/

/-- Anchored interface with horizon bounds: the fresh landing and its
restart crossing are certified historical events of the parent node. -/
inductive PermanentTailTerminalHorizonAnchoredOutcome
    (target start : Nat) (parent : PhaseSearchNode) : Prop
  | fresh_landing
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime)
      (value landingTime nextCrossingTime : Nat)
      (value_below : value < target)
      (after_parent : parentTime < landingTime)
      (before_child : landingTime ≤ childTime)
      (landing_first : FirstAt a value landingTime)
      (next_crossing : FirstWeakUpcrossingStep target landingTime
        nextCrossingTime)
      (landing_before_start : landingTime < start)
      (crossing_before_start : nextCrossingTime + 1 ≤ start)
      (crossing_before_horizon : nextCrossingTime + 1 < parent.horizon)
      (landing_cursor : TerminalHistoryCursor target landingTime) :
      PermanentTailTerminalHorizonAnchoredOutcome target start parent
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailTerminalHorizonAnchoredOutcome target start parent
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      PermanentTailTerminalHorizonAnchoredOutcome target start parent

/-- The permanent-tail coverage and strict-above fields bound every anchored
landing inside the parent history, without touching any upstream theorem. -/
theorem PermanentTailCombinedCertificate.terminalHorizonAnchoredOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    PermanentTailTerminalHorizonAnchoredOutcome target start parent := by
  cases h.terminalAnchoredOutcome with
  | fresh_landing childTime parentTime progress value landingTime
      nextCrossingTime hvalue hafter hbefore hfirst hnext hcursor =>
      have hmem := h.tail.below_covered value hvalue
      rcases mem_valuesThrough_iff.mp hmem with ⟨t, ht, hvalueEq⟩
      have hlandingLe : landingTime ≤ start := by
        by_cases hle : landingTime ≤ t
        · omega
        · exact False.elim (hfirst.2 t (by omega) hvalueEq)
      have hbelow : a landingTime < target := by
        rw [hfirst.1]
        exact hvalue
      have habove := h.tail.strictly_above start (Nat.le_refl _)
      have hlandingLt : landingTime < start := by
        by_cases heq : landingTime = start
        · rw [heq] at hbelow
          omega
        · omega
      rcases exists_weakUpcrossingStep_between (Nat.le_of_lt hlandingLt)
          hbelow (Nat.le_of_lt habove) with
        ⟨witness, hwitness, hwitnessBefore⟩
      have hcrossLe : nextCrossingTime ≤ witness := hnext.time_le hwitness
      have hcrossStart : nextCrossingTime + 1 ≤ start := by omega
      have hcrossHorizon : nextCrossingTime + 1 < parent.horizon :=
        Nat.lt_of_le_of_lt hcrossStart
          h.crossing.tail_strictly_before_horizon
      exact .fresh_landing childTime parentTime progress value landingTime
        nextCrossingTime hvalue hafter hbefore hfirst hnext hlandingLt
        hcrossStart hcrossHorizon hcursor
  | semantic_progress stepParent child semantic progress =>
      exact .semantic_progress stepParent child semantic progress
  | exact_replay replayParent replaySource replay =>
      exact .exact_replay replayParent replaySource replay

end

end Recaman
