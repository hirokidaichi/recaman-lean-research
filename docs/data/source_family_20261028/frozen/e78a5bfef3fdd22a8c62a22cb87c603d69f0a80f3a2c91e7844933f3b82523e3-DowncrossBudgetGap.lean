import Recaman.TypedNormalProvenance

namespace Recaman

noncomputable section

/-! # Closing the downcross budget gap

A downcross restart is precisely the bad transport case for the generic
extended-history theorem: its history budget has already fallen strictly
between the representative time and the historical horizon.  The mechanism
also retains more information than the generic certificate, however.  Its
actual endpoint is below the target.

Starting there, the real orbit must make a future upward crossing.  The value
immediately before that crossing is below the target and hence strictly below
the old representative anchor.  Storing the crossing through the existing
`crossing_recovery` semantic constructor therefore decreases the anchor
component of the existing four-component rank.  No new phase or rank is
needed for this provenance mechanism.
-/

/-- One forced-addition transition from below the target to at least the
target.  The start bound makes it a future recovery from a chosen endpoint. -/
structure WeakUpcrossingStep (target start time : Nat) : Prop where
  start_le : start ≤ time
  below : a time < target
  endpoint_ge : target ≤ a (time + 1)
  forced_addition : ¬ CanSubtract (time + 1) (stateAt time)

/-- On any finite segment from below the target to at-or-above the target,
some adjacent pair is a forced-addition upcrossing. -/
theorem exists_weakUpcrossingStep_between
    {target start finish : Nat}
    (htime : start ≤ finish)
    (hstart : a start < target)
    (hfinish : target ≤ a finish) :
    ∃ time, WeakUpcrossingStep target start time ∧ time + 1 ≤ finish := by
  have aux : ∀ distance : Nat,
      target ≤ a (start + distance) →
      ∃ time, WeakUpcrossingStep target start time ∧
        time + 1 ≤ start + distance := by
    intro distance
    induction distance with
    | zero =>
        intro habove
        simp only [Nat.add_zero] at habove
        exact False.elim (by omega)
    | succ distance ih =>
        intro habove
        by_cases hprevious : target ≤ a (start + distance)
        · rcases ih hprevious with ⟨time, hcrossing, hbound⟩
          exact ⟨time, hcrossing, by omega⟩
        · have hbelow : a (start + distance) < target :=
            Nat.lt_of_not_ge hprevious
          have hforced :
              ¬ CanSubtract (start + distance + 1)
                (stateAt (start + distance)) := by
            intro hcan
            have hstep := a_succ_of_canSubtract hcan
            have hnextLe :
                a (start + distance + 1) ≤ a (start + distance) := by
              omega
            have : a (start + distance + 1) < target :=
              Nat.lt_of_le_of_lt hnextLe hbelow
            exact (Nat.not_lt_of_ge (by simpa [Nat.add_assoc] using habove))
              this
          refine ⟨start + distance, {
            start_le := by omega
            below := hbelow
            endpoint_ge := ?_
            forced_addition := hforced
          }, by omega⟩
          simpa [Nat.add_assoc] using habove
  have hfinishEq : start + (finish - start) = finish := by omega
  have hresult := aux (finish - start)
  rw [hfinishEq] at hresult
  exact hresult hfinish

/-- Every below-target endpoint has a finite future upcrossing.

If the current clock is already target-ready, the next transition is forced
addition.  Otherwise the canonical target-ready state at time `target-1` or
`target` is strictly later, and the finite-segment theorem finds a crossing
on the way to it. -/
theorem exists_weakUpcrossingStep_from_below
    {target start : Nat}
    (htarget : 0 < target)
    (hstart : a start < target) :
    ∃ time, WeakUpcrossingStep target start time := by
  by_cases hclock : target ≤ start + 1
  · have hforced : ¬ CanSubtract (start + 1) (stateAt start) := by
      intro hcan
      have hpositive := hcan.1
      change start + 1 < a start at hpositive
      omega
    have hstep := a_succ_of_not_canSubtract hforced
    exact ⟨start, {
      start_le := Nat.le_refl _
      below := hstart
      endpoint_ge := by omega
      forced_addition := hforced
    }⟩
  · rcases exists_targetReady_state_of_pos htarget with
      ⟨finish, quotient, remainder, firstTime, hfinishTime,
        _hfinishReady, hfinishValue, _hcoordinates, _hfirstTime,
        _hfirst⟩
    have hstartFinish : start ≤ finish := by
      rcases hfinishTime with htime | htime <;> omega
    rcases exists_weakUpcrossingStep_between hstartFinish hstart
        hfinishValue with ⟨time, hcross, _⟩
    exact ⟨time, hcross⟩

/-- The generic extended-history analysis exposes exactly the expected
budget-transport residual for a downcross whenever its representative state
is time-ready.  This theorem deliberately retains the representative local
child: the mechanism-specific closure below takes a different route through
the below-target endpoint. -/
theorem DowncrossRestartNormalProvenance.representativeStep_or_budgetTransport
    {target : Nat} {parent child : PhaseSearchNode}
    (h : DowncrossRestartNormalProvenance target parent child)
    (hhorizonReady : target ≤ h.certificate.historyHorizon + 1)
    (hrepresentativeReady :
      target ≤ h.certificate.representativeTime + 1) :
    (∃ witness, a witness = target) ∨
      ∃ next,
        PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next
          (extendedHistoryRepresentativeNode
            h.certificate.representativeTime) ∧
        ExtendedHistoryNormalResidual target child := by
  let hext := h.certificate.toExtendedHistory hhorizonReady
  have horbit := hext.toOrbitReadyAtRepresentative hrepresentativeReady
  rcases horbit.phaseSemanticStep with hoccurs |
      ⟨next, hsemantic, hprogress⟩
  · exact Or.inl hoccurs
  · have hchildHorizon : child.horizon =
        h.certificate.historyHorizon := by
      simpa using congrArg PhaseSearchNode.horizon h.certificate.node_eq
    have hgap : missingBelowCount target child.horizon <
        missingBelowCount target h.certificate.representativeTime := by
      rw [hchildHorizon]
      exact h.budget_drop
    exact Or.inr ⟨next, hsemantic, hprogress,
      .budget_transport h.certificate.representativeTime
        h.certificate.quotient h.certificate.remainder hext
        hrepresentativeReady next hsemantic hprogress hgap⟩

/-- Mechanism-specific total semantic step for a downcross restart.

The future weak crossing either lands exactly on the target, finds that the
target was already present, or is strict.  In the strict case the
pre-crossing value becomes a `crossing_recovery` anchor at an enlarged real
history horizon.  It is below the target while the old representative value
is at least the target, so the normal-to-normal anchor component decreases. -/
theorem DowncrossRestartNormalProvenance.phaseSemanticStep
    {target : Nat} {parent child : PhaseSearchNode}
    (h : DowncrossRestartNormalProvenance target parent child) :
    (∃ witness, a witness = target) ∨
      ∃ next, PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next child := by
  rcases exists_weakUpcrossingStep_from_below
      h.certificate.target_positive h.endpoint_below_target with
    ⟨time, hcross⟩
  by_cases hseen : target ∈ valuesThrough time
  · rcases mem_valuesThrough_iff.mp hseen with ⟨witness, _, hvalue⟩
    exact Or.inl ⟨witness, hvalue⟩
  by_cases hequal : a (time + 1) = target
  · exact Or.inl ⟨time + 1, hequal⟩
  have hstrict : target < a (time + 1) :=
    Nat.lt_of_le_of_ne hcross.endpoint_ge (Ne.symm hequal)
  have hstep := a_succ_of_not_canSubtract hcross.forced_addition
  have hdebtCrossing : DebtCrossing target (a (time + 1)) time :=
    ⟨hcross.below, hstrict, hstep⟩
  rcases exists_coordinatesAt (n := time + 1) (by omega) with
    ⟨quotient, remainder, hcoordinates⟩
  let next : PhaseSearchNode :=
    ⟨time + 2, a time, .normal, a time⟩
  have hrecovery : CrossingRecoveryInvariant target (time + 2)
      h.certificate.value time quotient remainder := {
    target_missing := hseen
    forced_addition := hcross.forced_addition
    crossing := hdebtCrossing
    coordinates := hcoordinates
    crossing_before_horizon := by omega
    predecessor_lt_anchor := by
      exact Nat.lt_of_lt_of_le hcross.below h.certificate.target_le_value
  }
  have hsemantic : PhaseSemanticInvariant target next := by
    apply PhaseSemanticInvariant.crossing_recovery
    exact ⟨h.certificate.value, time, quotient, remainder, {
      target_positive := h.certificate.target_positive
      node_eq := rfl
      recovery := hrecovery
    }⟩
  have hprogress : PhaseSearchProgress target next child := by
    rw [h.certificate.node_eq]
    apply phaseSearchProgress_of_horizonAndAnchor
    · exact Nat.le_trans hcross.start_le (by omega)
    · exact Nat.lt_of_lt_of_le hcross.below
        h.certificate.target_le_value
  exact Or.inr ⟨next, hsemantic, hprogress⟩

/-- The same recovery also composes all the way back to the provenance
source.  Here the original `budget_drop` is used through `rank_edge`, while
the new recovery contributes the subsequent anchor decrease. -/
theorem DowncrossRestartNormalProvenance.phaseSemanticStep_from_source
    {target : Nat} {parent child : PhaseSearchNode}
    (h : DowncrossRestartNormalProvenance target parent child) :
    (∃ witness, a witness = target) ∨
      ∃ next, PhaseSemanticInvariant target next ∧
        PhaseSearchProgress target next parent := by
  rcases h.phaseSemanticStep with hoccurs |
      ⟨next, hsemantic, hnext⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨next, hsemantic, hnext.trans h.rank_edge⟩

/-- The smallest actual downcross illustrates the completed mechanism.
For target four, the historical restart stores `a 3 = 6` at horizon four,
where `a 4 = 2`.  The next forced addition crosses to seven, and the semantic
recovery node uses the strictly smaller pre-crossing anchor two. -/
theorem downcross_four_actual_crossingRecovery :
    let parent : PhaseSearchNode := ⟨3, a 3, .normal, a 3⟩
    let child : PhaseSearchNode := ⟨4, a 3, .normal, a 3⟩
    let next : PhaseSearchNode := ⟨6, a 4, .normal, a 4⟩
    Nonempty (DowncrossRestartNormalProvenance 4 parent child) ∧
      CrossingSearchInvariant 4 next ∧
      PhaseSearchProgress 4 next child := by
  let parent : PhaseSearchNode := ⟨3, a 3, .normal, a 3⟩
  let child : PhaseSearchNode := ⟨4, a 3, .normal, a 3⟩
  let next : PhaseSearchNode := ⟨6, a 4, .normal, a 4⟩
  have hfirst : FirstAt a (a 3) 3 := by
    constructor
    · rfl
    · intro u hu
      have hcases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases hcases with h | h | h <;> subst u <;> decide
  have hcurrent : ProvenancedNormalInvariant 4 parent := by
    apply ProvenancedNormalInvariant.current
    exact ⟨3, 2, 0, {
      target_positive := by decide
      node_eq := rfl
      time_ready := by decide
      target_le_value := by decide
      coordinates := by constructor <;> decide
    }⟩
  let hdown : DowncrossRestartNormalProvenance 4 parent child :=
    downcrossRestartNormalProvenance_of_budgetDrop
      (by decide) hcurrent (by decide) hfirst (by decide)
      (show CoordinatesAt 3 2 0 by constructor <;> decide)
      (by decide) (by decide) (by decide)
  have hrecovery : CrossingRecoveryInvariant 4 6 6 4 1 2 := {
    target_missing := by decide
    forced_addition := by decide
    crossing := by
      unfold DebtCrossing
      exact ⟨by decide, by decide, by decide⟩
    coordinates := by constructor <;> decide
    crossing_before_horizon := by decide
    predecessor_lt_anchor := by decide
  }
  have hcrossing : CrossingSearchInvariant 4 next :=
    ⟨6, 4, 1, 2, {
      target_positive := by decide
      node_eq := rfl
      recovery := hrecovery
    }⟩
  have hprogress : PhaseSearchProgress 4 next child := by
    exact phaseSearchProgress_of_horizonAndAnchor (by decide) (by decide)
  exact ⟨⟨hdown⟩, hcrossing, hprogress⟩

end

end Recaman
