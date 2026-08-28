import Recaman.ReadyDebtRefined

namespace Recaman

/-! # Crossing-frontier refinement at a ready debt source

The current/debt split for a successful crossing-frontier first occurrence
has one genuine two-clock middle interval.  That interval is neither a future
current node nor an earlier debt node.  A ready debt source nevertheless
supplies exactly the clock fact needed to retain it as an extended-history
normal node at the unchanged horizon.
-/

/-- Promote every crossing-frontier outcome from a ready debt source to the
refined domain.  The middle interval retains the first occurrence as its
representative and inherits horizon readiness from the source debt node. -/
theorem CrossingFrontierCurrentDebtOutcome.toReadyRefinedStep
    {target historyHorizon debtAnchor debtValue debtTime : Nat}
    (htarget : 0 < target)
    (hsource : ReadyDebtInvariant target
      ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ debtValue debtTime)
    (h : CrossingFrontierCurrentDebtOutcome target historyHorizon debtAnchor
      debtTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | current_child value firstTime hcurrent =>
      exact Or.inr ⟨targetStartNode firstTime,
        Or.inl (Or.inl hcurrent.invariant), hcurrent.progress⟩
  | debt_child value firstTime hdebt =>
      have hready : ReadyDebtInvariant target
          ⟨historyHorizon, debtAnchor, .debt, firstTime⟩ value firstTime := {
        debt := hdebt.invariant
        horizon_ready := hsource.horizon_ready
      }
      exact Or.inr
        ⟨⟨historyHorizon, debtAnchor, .debt, firstTime⟩,
          Or.inl (Or.inr ⟨value, firstTime, hready⟩), hdebt.progress⟩
  | middle_residual value firstTime hmiddle =>
      have hfirstPositive : 0 < firstTime := by
        by_cases hzero : firstTime = 0
        · have hfirstZero : FirstAt a value 0 := by
            simpa [hzero] using hmiddle.first
          have hvalueZero := firstAt_time_zero_value hfirstZero
          have htargetZero : target < 0 := by
            simpa [hvalueZero] using hmiddle.target_lt_value
          exact False.elim (Nat.not_lt_zero target htargetZero)
        · omega
      rcases exists_coordinatesAt hfirstPositive with
        ⟨quotient, remainder, hcoordinates⟩
      let child : PhaseSearchNode :=
        ⟨historyHorizon, a firstTime, .normal, a firstTime⟩
      have hextended : ExtendedHistoryNormalInvariant target child :=
        ⟨firstTime, quotient, remainder, {
          target_positive := htarget
          node_eq := rfl
          representative_le_horizon := Nat.le_of_lt
            hmiddle.first_time_lt_horizon
          horizon_time_ready := by
            simpa [child] using hsource.horizon_ready
          target_le_value := by
            rw [hmiddle.first.1]
            exact Nat.le_of_lt hmiddle.target_lt_value
          coordinates := hcoordinates
        }⟩
      have hprogress : PhaseSearchProgress target child
          ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ := by
        have hanchorDrop : a firstTime < debtAnchor := by
          rw [hmiddle.first.1]
          exact hmiddle.anchor_drop
        exact phaseSearch_exitDebt_of_anchorDrop hanchorDrop
      exact Or.inr ⟨child, Or.inr (Or.inl hextended), hprogress⟩

/-- A successful first occurrence discovered at the crossing frontier has a
residual-free refined step whenever the source debt horizon is target-ready. -/
theorem ReadyDebtInvariant.crossingFrontierFirstAt_refinedStep
    {target historyHorizon debtAnchor debtValue debtTime value firstTime : Nat}
    (htarget : 0 < target)
    (hsource : ReadyDebtInvariant target
      ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ debtValue debtTime)
    (htargetValue : target ≤ value)
    (hfirst : FirstAt a value firstTime)
    (hanchor : value < debtAnchor) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ := by
  have houtcome := crossingFrontierFirstAt_currentOrDebt_or_middle
    htarget hsource.horizon_ready hsource.debt htargetValue hfirst hanchor
  exact houtcome.toReadyRefinedStep htarget hsource

end Recaman
