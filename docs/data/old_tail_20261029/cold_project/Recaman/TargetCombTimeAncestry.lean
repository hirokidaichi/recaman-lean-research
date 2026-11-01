import Recaman.TargetCombMacro

namespace Recaman

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! # Time-only ancestry of above-target first occurrences

Value monotonicity is unnecessary for following first-occurrence provenance
back to the finite pre-tail prefix.  If an above-target value first appears
after the permanent tail has started, the transition predecessor is again
above the target and has a strictly earlier first occurrence.  This holds for
both legal-subtraction and forced-addition origins.

The result is deliberately only a routing lemma.  It supplies no injectivity
or capacity bound on the ancestry tree.
-/

/-- An above-target first occurrence is already in the finite pre-tail prefix,
or its actual transition predecessor is above the target and has a strictly
earlier first occurrence. -/
theorem FirstAt.preTail_or_aboveTarget_parent
    {target tailStart value firstTime : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htarget : target < value)
    (hfirst : FirstAt a value firstTime) :
    firstTime ≤ tailStart ∨
      ∃ parent parentFirstTime,
        target < parent ∧
        FirstAt a parent parentFirstTime ∧
        parentFirstTime < firstTime := by
  by_cases hpreTail : firstTime ≤ tailStart
  · exact Or.inl hpreTail
  · apply Or.inr
    have hpositive : 0 < firstTime := by
      by_cases hzero : firstTime = 0
      · subst firstTime
        have hvalue := firstAt_time_zero_value hfirst
        omega
      · omega
    have hclock : firstTime - 1 + 1 = firstTime := by omega
    have hfirst' : FirstAt a value (firstTime - 1 + 1) := by
      simpa only [hclock] using hfirst
    rcases firstAt_succ_transition hfirst' with hsubtract | hadd
    · rcases hsubtract with ⟨hcan, hvalue⟩
      rcases history_member_has_firstAt
          (current_mem_valuesThrough (firstTime - 1)) with
        ⟨parentFirstTime, hparentTime, hparentFirst⟩
      refine ⟨a (firstTime - 1), parentFirstTime, ?_,
        hparentFirst, by omega⟩
      have hvalue' : value = a (firstTime - 1) - firstTime := by
        simpa only [hclock] using hvalue
      have hparentPositive : firstTime < a (firstTime - 1) := by
        simpa only [hclock, a] using hcan.1
      omega
    · rcases hadd with ⟨_hforced, _hvalue⟩
      rcases history_member_has_firstAt
          (current_mem_valuesThrough (firstTime - 1)) with
        ⟨parentFirstTime, hparentTime, hparentFirst⟩
      refine ⟨a (firstTime - 1), parentFirstTime, ?_,
        hparentFirst, by omega⟩
      have htailTime : tailStart ≤ firstTime - 1 := by omega
      exact htail.strictly_above (firstTime - 1) htailTime

/-- Iterating time-only provenance reaches an above-target first occurrence
whose first time lies in the finite pre-tail prefix. -/
theorem FirstAt.exists_preTail_aboveTarget_ancestor
    {target tailStart value firstTime : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htarget : target < value)
    (hfirst : FirstAt a value firstTime) :
    ∃ root rootFirstTime,
      target < root ∧
      FirstAt a root rootFirstTime ∧
      rootFirstTime ≤ tailStart := by
  induction firstTime using Nat.strongRecOn generalizing value with
  | ind firstTime ih =>
      rcases hfirst.preTail_or_aboveTarget_parent htail htarget with
        hpreTail | ⟨parent, parentFirstTime, hparentTarget,
          hparentFirst, hparentTime⟩
      · exact ⟨value, firstTime, htarget, hfirst, hpreTail⟩
      · exact ih parentFirstTime hparentTime hparentTarget hparentFirst

/-- A first occurrence in a finite time prefix is bounded by the standard
triangular orbit ceiling at the end of that prefix. -/
theorem FirstAt.value_le_upperTri_of_time_le
    {value firstTime bound : Nat}
    (hfirst : FirstAt a value firstTime)
    (htime : firstTime ≤ bound) :
    value ≤ upperTri bound := by
  have horbit : a firstTime ≤ upperTri firstTime := a_le_upperTri firstTime
  have hmono : upperTri firstTime ≤ upperTri bound := upperTri_mono htime
  rw [← hfirst.1]
  exact Nat.le_trans horbit hmono

/-- Rank-facing threshold refinement of time-only ancestry.

Starting from an above-target first occurrence which is not below the active
anchor, follow actual first-occurrence predecessors.  Either the ancestry
reaches the pre-tail prefix without ever crossing the anchor, leaving one
explicit finite-prefix obstruction, or the first crossing below the anchor
is a strong debt value.  In the latter case, debt-time descent followed by
the anchor drop gives a direct normal `PhaseSearchProgress` edge from the
original debt-shaped node.

This theorem does not bound or consume the pre-tail roots in the first
branch; it only isolates them as the exact residual of the existing rank. -/
theorem FirstAt.preTail_anchorObstruction_or_normalProgress
    {target tailStart horizon anchor value firstTime : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htarget : target < value)
    (hanchor : anchor ≤ value)
    (hfirst : FirstAt a value firstTime)
    (hhorizon : firstTime < horizon) :
    (∃ root rootFirstTime,
      target < root ∧
      anchor ≤ root ∧
      FirstAt a root rootFirstTime ∧
      rootFirstTime ≤ tailStart) ∨
    ∃ child childFirstTime,
      target < child ∧
      child < anchor ∧
      FirstAt a child childFirstTime ∧
      childFirstTime < firstTime ∧
      DebtInvariant target
        ⟨horizon, anchor, .debt, childFirstTime⟩ child childFirstTime ∧
      PhaseSearchProgress target
        ⟨horizon, child, .normal, child⟩
        ⟨horizon, anchor, .debt, firstTime⟩ := by
  induction firstTime using Nat.strongRecOn generalizing value with
  | ind firstTime ih =>
      rcases hfirst.preTail_or_aboveTarget_parent htail htarget with
        hpreTail | ⟨parent, parentFirstTime, hparentTarget,
          hparentFirst, hparentTime⟩
      · exact Or.inl ⟨value, firstTime, htarget, hanchor, hfirst,
          hpreTail⟩
      · by_cases hparentAnchor : parent < anchor
        · have hparentHorizon : parentFirstTime < horizon :=
            Nat.lt_trans hparentTime hhorizon
          have hdebt : DebtInvariant target
              ⟨horizon, anchor, .debt, parentFirstTime⟩
              parent parentFirstTime := {
            phase_eq := rfl
            local_eq := rfl
            target_le := Nat.le_of_lt hparentTarget
            first := hparentFirst
            firstTime_lt_horizon := hparentHorizon
            value_lt_anchor := hparentAnchor
          }
          have hexit : PhaseSearchProgress target
              ⟨horizon, parent, .normal, parent⟩
              ⟨horizon, anchor, .debt, parentFirstTime⟩ :=
            phaseSearch_exitDebt_of_anchorDrop hparentAnchor
          have htimeDrop : PhaseSearchProgress target
              ⟨horizon, anchor, .debt, parentFirstTime⟩
              ⟨horizon, anchor, .debt, firstTime⟩ :=
            phaseSearch_debtTimeDrop hparentTime
          exact Or.inr ⟨parent, parentFirstTime, hparentTarget,
            hparentAnchor, hparentFirst, hparentTime, hdebt,
            hexit.trans htimeDrop⟩
        · have hparentAnchor' : anchor ≤ parent :=
            Nat.le_of_not_gt hparentAnchor
          rcases ih parentFirstTime hparentTime hparentTarget
              hparentAnchor' hparentFirst
              (Nat.lt_trans hparentTime hhorizon) with
            hroot | ⟨child, childFirstTime, hchildTarget,
              hchildAnchor, hchildFirst, hchildTime, hchildDebt,
              hchildProgress⟩
          · exact Or.inl hroot
          · have htimeDrop : PhaseSearchProgress target
                ⟨horizon, anchor, .debt, parentFirstTime⟩
                ⟨horizon, anchor, .debt, firstTime⟩ :=
              phaseSearch_debtTimeDrop hparentTime
            exact Or.inr ⟨child, childFirstTime, hchildTarget,
              hchildAnchor, hchildFirst, Nat.lt_trans hchildTime hparentTime,
              hchildDebt, hchildProgress.trans htimeDrop⟩

/-- Once an active anchor clears the finite triangular ceiling of the
pre-tail prefix, the residual branch of
`preTail_anchorObstruction_or_normalProgress` is impossible.  Time-only
ancestry must cross strictly below the anchor and therefore produces an
ordinary normal rank child. -/
theorem FirstAt.normalProgress_of_preTailCeiling_lt_anchor
    {target tailStart horizon anchor value firstTime : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hceiling : upperTri tailStart < anchor)
    (htarget : target < value)
    (hanchor : anchor ≤ value)
    (hfirst : FirstAt a value firstTime)
    (hhorizon : firstTime < horizon) :
    ∃ child childFirstTime,
      target < child ∧
      child < anchor ∧
      FirstAt a child childFirstTime ∧
      childFirstTime < firstTime ∧
      DebtInvariant target
        ⟨horizon, anchor, .debt, childFirstTime⟩ child childFirstTime ∧
      PhaseSearchProgress target
        ⟨horizon, child, .normal, child⟩
        ⟨horizon, anchor, .debt, firstTime⟩ := by
  rcases hfirst.preTail_anchorObstruction_or_normalProgress
      htail htarget hanchor hhorizon with
    ⟨root, rootFirstTime, _hrootTarget, hrootAnchor,
      hrootFirst, hrootTime⟩ | hprogress
  · have hrootCeiling :=
      hrootFirst.value_le_upperTri_of_time_le hrootTime
    omega
  · exact hprogress

/-- A completed comb inside a missing permanent tail already has the exact
strong-debt representative needed by the phase rank: its terminal blocker
itself.

The final fresh landing is `blocker + 1` and lies in the strict-above tail,
so the blocker is at least the target.  Equality is impossible because the
blocker is certified historical while the target is globally missing.  The
comb equations also put the blocker strictly below the entry value `a s`.
Thus no traversal of the blocker's subtraction-origin predecessor is needed
when the active anchor is the natural terminal-gate anchor `a s`. -/
theorem HistoryTerminatedComb.tail_blocker_debtNormalProgress
    {target tailStart s k blocker : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart ≤ s)
    (hcomb : HistoryTerminatedComb s k blocker) :
    ∃ firstTime,
      target < blocker ∧
      FirstAt a blocker firstTime ∧
      firstTime < s ∧
      blocker < a s ∧
      DebtInvariant target
        ⟨s, a s, .debt, firstTime⟩ blocker firstTime ∧
      PhaseSearchProgress target
        ⟨s, blocker, .normal, blocker⟩ (targetStartNode s) := by
  have hfinalTime : tailStart ≤ s + 2 * k := by omega
  have hfinalAbove := htail.strictly_above (s + 2 * k) hfinalTime
  have htargetLeBlocker : target ≤ blocker := by
    rw [hcomb.blocker_eq] at hfinalAbove
    omega
  have htargetNeBlocker : target ≠ blocker := by
    intro heq
    subst blocker
    rcases mem_valuesThrough_iff.mp hcomb.blocker_seen with
      ⟨witness, _hwitnessTime, hwitnessValue⟩
    exact htail.target_missing ⟨witness, hwitnessValue⟩
  have htargetBlocker : target < blocker := by omega
  have hexit := hcomb.episode.run.exit_value
  have hblockerEntry : blocker < a s := by
    rw [hcomb.blocker_eq] at hexit
    omega
  rcases hcomb.blocker_has_firstAt_before_entry with
    ⟨firstTime, hfirstTime, hfirst⟩
  have hdebt : DebtInvariant target
      ⟨s, a s, .debt, firstTime⟩ blocker firstTime := {
    phase_eq := rfl
    local_eq := rfl
    target_le := Nat.le_of_lt htargetBlocker
    first := hfirst
    firstTime_lt_horizon := hfirstTime
    value_lt_anchor := hblockerEntry
  }
  have hprogress : PhaseSearchProgress target
      ⟨s, blocker, .normal, blocker⟩ (targetStartNode s) := by
    exact phaseSearchProgress_of_horizonAndAnchor
      (Nat.le_refl s) hblockerEntry
  exact ⟨firstTime, htargetBlocker, hfirst, hfirstTime,
    hblockerEntry, hdebt, hprogress⟩

/-! ## Exact prefix warning for subtraction-origin ancestry -/

private theorem historyTerminatedComb_734_10_138 :
    HistoryTerminatedComb 734 10 138 := by
  refine {
    episode := {
      entry_first := ?_
      run := ?_
    }
    final_forced := by decide
    blocker_eq := by decide
    blocker_seen := by decide
  }
  · simpa using firstAt_succ_of_canSubtract
      (n := 733) (by decide : CanSubtract 734 (stateAt 733))
  · intro i hi
    have hcases :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by
      omega
    rcases hcases with h | h | h | h | h | h | h | h | h | h <;>
      subst i <;> constructor <;> decide

/-- Terminal-gate and positive-origin data alone do not force the
subtraction predecessor's ancestry below the comb entry.  On the exact
standard orbit, the target-19 H-to-L gate at time 734 terminates at blocker
138.  That blocker was first created by `258 - 120 = 138`, and the older
value 258 is already a first occurrence before the empirical strict-tail
boundary 132 while remaining above the entry 149.

Thus the correct local adapter is `tail_blocker_debtNormalProgress`, which
uses the blocker itself, or the ceiling theorem above after mounting a larger
external anchor. -/
theorem terminalGate_subtractionOrigin_preTailHigh_counterexample :
    ∃ hcomb : HistoryTerminatedComb 734 10 138,
      PositiveTerminalBlockerOrigin hcomb ∧
      FirstAt a 258 119 ∧
      119 ≤ 132 ∧
      a 734 ≤ 258 ∧
      19 < nextSubtractionCandidate 733 ∧
      nextSubtractionCandidate 734 < 19 := by
  let hcomb : HistoryTerminatedComb 734 10 138 :=
    historyTerminatedComb_734_10_138
  have hblockerFirst : FirstAt a 138 120 := by
    have hfirst := firstAt_succ_of_canSubtract
      (n := 119) (by decide : CanSubtract 120 (stateAt 119))
    have hvalue : a 120 = 138 := by decide
    rw [hvalue] at hfirst
    exact hfirst
  have hparentFirst : FirstAt a 258 119 := by
    have hfirst := firstAt_succ_of_canSubtract
      (n := 118) (by decide : CanSubtract 119 (stateAt 118))
    have hvalue : a 119 = 258 := by decide
    rw [hvalue] at hfirst
    exact hfirst
  have horigin : PositiveTerminalBlockerOrigin hcomb :=
    .legal_subtraction 120 (by decide) hblockerFirst (by decide)
      (by decide) 119 hparentFirst (by decide) (by decide)
  exact ⟨hcomb, horigin, hparentFirst, by decide, by decide,
    by decide, by decide⟩

end Recaman
