import Recaman.OrbitReadyDirectRefined

namespace Recaman

/-! # Ready debt in the refined domain

Ordinary debt continuation remains ready debt.  The two forced-addition
obstructions are genuine strict crossings and therefore enter the dedicated
crossing-recovery constructor directly.  A legal subtraction which reaches
the fixed anchor is the two-clock middle boundary; only there do we use the
debt value's now-safe horizon-ready extended-history certificate.
-/

/-- A ready debt value has a proof-carrying extended-history exit.  Unlike the
old broad normal self-exit, this certificate remembers the representative
time, its coordinates, and readiness at the fixed history horizon. -/
theorem ReadyDebtInvariant.extendedHistoryExit
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    ∃ child, OrbitReadyRefinedInvariant target child ∧
      PhaseSearchProgress target child
        ⟨horizon, anchor, .debt, firstTime⟩ := by
  have htimePositive := debt_firstTime_pos htarget h.debt
  rcases exists_coordinatesAt htimePositive with
    ⟨quotient, remainder, hcoordinates⟩
  let child : PhaseSearchNode :=
    ⟨horizon, a firstTime, .normal, a firstTime⟩
  have hextended : ExtendedHistoryNormalInvariant target child :=
    ⟨firstTime, quotient, remainder, {
      target_positive := htarget
      node_eq := rfl
      representative_le_horizon := Nat.le_of_lt h.debt.firstTime_lt_horizon
      horizon_time_ready := by
        simpa [child] using h.horizon_ready
      target_le_value := by
        rw [h.debt.first.1]
        exact h.debt.target_le
      coordinates := hcoordinates
    }⟩
  have hanchorDrop : a firstTime < anchor := by
    rw [h.debt.first.1]
    exact h.debt.value_lt_anchor
  exact ⟨child, Or.inr (Or.inl hextended),
    phaseSearch_exitDebt_of_anchorDrop hanchorDrop⟩

/-- Refine a ready-debt obstruction.  Forced additions retain their exact
crossing certificate.  The legal anchor-reaching boundary uses the typed
extended-history exit above, which is necessary because its first occurrence
equals the debt local time and is earlier than the history horizon. -/
theorem ReadyDebtInvariant.obstruction_refinedStep
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime)
    (hobstruction : DebtStepObstruction target horizon anchor value
      firstTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, firstTime⟩ := by
  cases hobstruction with
  | legal_reaches_anchor n htime hcan hvalue htargetValue hanchor =>
      exact Or.inr (h.extendedHistoryExit htarget)
  | addition_nonpositive n htime hforced hvalue htargetValue hbelow
      hnonpositive =>
      subst firstTime
      rcases debtCrossing_enters_recovery h.debt hforced hbelow with
        hoccurs | ⟨quotient, remainder, hrecovery, hprogress⟩
      · exact Or.inl hoccurs
      · let child : PhaseSearchNode :=
          ⟨horizon, a n, .normal, a n⟩
        have hcrossing : CrossingSearchInvariant target child :=
          ⟨anchor, n, quotient, remainder, {
            target_positive := htarget
            node_eq := rfl
            recovery := hrecovery
          }⟩
        exact Or.inr ⟨child, Or.inr (Or.inr hcrossing), hprogress⟩
  | addition_seen_below_target n candidate candidateTime htime hforced
      hvalue htargetValue hbelow hcandidate hpositive hfirst htimeDrop
      hcandidateBelow halready =>
      subst firstTime
      rcases debtCrossing_enters_recovery h.debt hforced hbelow with
        hoccurs | ⟨quotient, remainder, hrecovery, hprogress⟩
      · exact Or.inl hoccurs
      · let child : PhaseSearchNode :=
          ⟨horizon, a n, .normal, a n⟩
        have hcrossing : CrossingSearchInvariant target child :=
          ⟨anchor, n, quotient, remainder, {
            target_positive := htarget
            node_eq := rfl
            recovery := hrecovery
          }⟩
        exact Or.inr ⟨child, Or.inr (Or.inr hcrossing), hprogress⟩

/-- Ready debt has a residual-free step in the refined domain.  The normal
continuation path stays in ready debt; only explicit obstructions are routed
through the theorem above. -/
theorem ReadyDebtInvariant.refinedStep
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (h : ReadyDebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨horizon, anchor, .debt, firstTime⟩ := by
  rcases h.readyCurrentOrDebtStep_or_obstruction htarget with
    hoccurs | ⟨child, hchild, hprogress⟩ | hobstruction
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child, Or.inl hchild, hprogress⟩
  · exact h.obstruction_refinedStep htarget hobstruction

end Recaman
