import Recaman.CoverageDebtBridge
import Recaman.TypedNormalProvenance
import Recaman.DebtStep

namespace Recaman

private theorem historicalBridge_firstTime_pos
    {target value firstTime : Nat}
    (htarget : 0 < target)
    (htargetValue : target ≤ value)
    (hfirst : FirstAt a value firstTime) :
    0 < firstTime := by
  by_cases hzero : firstTime = 0
  · subst firstTime
    have hvalueZero := firstAt_time_zero_value hfirst
    omega
  · omega

/-! # Avoiding historical normal children with debt

A first-occurring anchor below a current normal parent admits the same sharp
time split as a coverage blocker.  A future first occurrence is an actual
orbit-ready normal child; an earlier first occurrence is a strong debt child.

For a debt parent, its history horizon and debt local time are different.
The analogous split therefore leaves a genuine interval
`debtTime ≤ firstTime < historyHorizon`.  This module records that interval
explicitly and also shows that ordinary debt evolution need not use the
historical self-exit at all.
-/

/-! ## Parent-drop bridge -/

structure ParentDropCurrentChildCertificate
    (target parentTime activeParent value firstTime : Nat) : Prop where
  target_lt_value : target < value
  first : FirstAt a value firstTime
  parent_time_le : parentTime ≤ firstTime
  anchor_drop : value < activeParent
  invariant : OrbitReadyNormalInvariant target (targetStartNode firstTime)
  progress : PhaseSearchProgress target (targetStartNode firstTime)
    ⟨parentTime, activeParent, .normal, a parentTime⟩

structure ParentDropDebtChildCertificate
    (target parentTime activeParent value firstTime : Nat) : Prop where
  target_lt_value : target < value
  first : FirstAt a value firstTime
  first_time_lt_parent : firstTime < parentTime
  anchor_drop : value < activeParent
  invariant : DebtInvariant target
    ⟨parentTime, activeParent, .debt, firstTime⟩ value firstTime
  progress : PhaseSearchProgress target
    ⟨parentTime, activeParent, .debt, firstTime⟩
    ⟨parentTime, activeParent, .normal, a parentTime⟩

/-- A parent-drop from a time-ready current normal source never needs a
historical normal child. -/
inductive ParentDropCurrentDebtOutcome
    (target parentTime activeParent : Nat) : Prop
  | target_occurs (witness : Nat) (value_eq : a witness = target) :
      ParentDropCurrentDebtOutcome target parentTime activeParent
  | current_child (value firstTime : Nat)
      (certificate : ParentDropCurrentChildCertificate target parentTime
        activeParent value firstTime) :
      ParentDropCurrentDebtOutcome target parentTime activeParent
  | debt_child (value firstTime : Nat)
      (certificate : ParentDropDebtChildCertificate target parentTime
        activeParent value firstTime) :
      ParentDropCurrentDebtOutcome target parentTime activeParent

theorem normalParentDrop_currentOrDebt
    {target parentTime activeParent rawHorizon value firstTime : Nat}
    (htarget : 0 < target)
    (htimeReady : target ≤ parentTime + 1)
    (hevidence : NormalParentDropEvidence target rawHorizon value firstTime
      ⟨parentTime, activeParent, .normal, a parentTime⟩
      ⟨rawHorizon, value, .normal, a rawHorizon⟩) :
    ParentDropCurrentDebtOutcome target parentTime activeParent := by
  by_cases htargetEq : value = target
  · exact .target_occurs firstTime (by
      rw [hevidence.anchor_first.1, htargetEq])
  have htargetLt : target < value :=
    Nat.lt_of_le_of_ne hevidence.target_le_anchor (Ne.symm htargetEq)
  by_cases hfuture : parentTime ≤ firstTime
  · have hfirstPositive : 0 < firstTime :=
      historicalBridge_firstTime_pos htarget hevidence.target_le_anchor
        hevidence.anchor_first
    rcases exists_coordinatesAt hfirstPositive with
      ⟨q, r, hcoordinates⟩
    have hvalueAtFirst : a firstTime = value := hevidence.anchor_first.1
    have hready : OrbitReadyNormalInvariant target
        (targetStartNode firstTime) := by
      exact ⟨firstTime, q, r, {
        target_positive := htarget
        node_eq := rfl
        time_ready := by omega
        target_le_value := by simpa [hvalueAtFirst] using
          hevidence.target_le_anchor
        coordinates := hcoordinates
      }⟩
    have hanchor : a firstTime < activeParent := by
      simpa [hvalueAtFirst] using hevidence.anchor_drop
    have hprogress : PhaseSearchProgress target
        (targetStartNode firstTime)
        ⟨parentTime, activeParent, .normal, a parentTime⟩ :=
      phaseSearchProgress_of_horizonAndAnchor hfuture hanchor
    exact .current_child value firstTime {
      target_lt_value := htargetLt
      first := hevidence.anchor_first
      parent_time_le := hfuture
      anchor_drop := hevidence.anchor_drop
      invariant := hready
      progress := hprogress
    }
  · have hearlier : firstTime < parentTime := Nat.lt_of_not_ge hfuture
    let child : PhaseSearchNode :=
      ⟨parentTime, activeParent, .debt, firstTime⟩
    have hdebt : DebtInvariant target child value firstTime := {
      phase_eq := rfl
      local_eq := rfl
      target_le := hevidence.target_le_anchor
      first := hevidence.anchor_first
      firstTime_lt_horizon := hearlier
      value_lt_anchor := hevidence.anchor_drop
    }
    exact .debt_child value firstTime {
      target_lt_value := htargetLt
      first := hevidence.anchor_first
      first_time_lt_parent := hearlier
      anchor_drop := hevidence.anchor_drop
      invariant := hdebt
      progress := phaseSearch_enterDebt
    }

/-- Direct adapter for the existing negative-current invariant. -/
theorem NormalPhaseInvariantAt.parentDrop_currentOrDebt
    {target parentTime activeParent q r rawHorizon value firstTime : Nat}
    (htarget : 0 < target)
    (hparent : NormalPhaseInvariantAt target
      ⟨parentTime, activeParent, .normal, a parentTime⟩ parentTime q r)
    (hevidence : NormalParentDropEvidence target rawHorizon value firstTime
      ⟨parentTime, activeParent, .normal, a parentTime⟩
      ⟨rawHorizon, value, .normal, a rawHorizon⟩) :
    ParentDropCurrentDebtOutcome target parentTime activeParent :=
  normalParentDrop_currentOrDebt htarget hparent.time_ready hevidence

theorem ParentDropCurrentDebtOutcome.toCurrentOrDebtStep
    {target parentTime activeParent : Nat}
    (h : ParentDropCurrentDebtOutcome target parentTime activeParent) :
    (∃ witness, a witness = target) ∨
      ∃ child, CurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child
          ⟨parentTime, activeParent, .normal, a parentTime⟩ := by
  cases h with
  | target_occurs witness hvalue => exact Or.inl ⟨witness, hvalue⟩
  | current_child value firstTime hcurrent =>
      exact Or.inr ⟨targetStartNode firstTime, Or.inl hcurrent.invariant,
        hcurrent.progress⟩
  | debt_child value firstTime hdebt =>
      exact Or.inr
        ⟨⟨parentTime, activeParent, .debt, firstTime⟩,
          Or.inr ⟨value, firstTime, hdebt.invariant⟩, hdebt.progress⟩

/-! ## Crossing-frontier bridge -/

structure CrossingFrontierCurrentChildCertificate
    (target historyHorizon debtAnchor debtTime value firstTime : Nat) : Prop where
  target_lt_value : target < value
  first : FirstAt a value firstTime
  anchor_drop : value < debtAnchor
  invariant : OrbitReadyNormalInvariant target (targetStartNode firstTime)
  progress : PhaseSearchProgress target (targetStartNode firstTime)
    ⟨historyHorizon, debtAnchor, .debt, debtTime⟩

structure CrossingFrontierDebtChildCertificate
    (target historyHorizon debtAnchor debtTime value firstTime : Nat) : Prop where
  target_lt_value : target < value
  first : FirstAt a value firstTime
  first_time_lt_debt : firstTime < debtTime
  anchor_drop : value < debtAnchor
  invariant : DebtInvariant target
    ⟨historyHorizon, debtAnchor, .debt, firstTime⟩ value firstTime
  progress : PhaseSearchProgress target
    ⟨historyHorizon, debtAnchor, .debt, firstTime⟩
    ⟨historyHorizon, debtAnchor, .debt, debtTime⟩

/-- Exact interval left because a debt node has two independent clocks.

The first occurrence is not early enough to lower the debt-time coordinate
and is earlier than the history horizon.  It can be a current rank child only
when its own clock is target-ready and no below-target history was consumed
between it and the parent horizon. -/
structure CrossingFrontierMiddleResidual
    (target historyHorizon debtAnchor debtTime value firstTime : Nat) : Prop where
  target_lt_value : target < value
  first : FirstAt a value firstTime
  anchor_drop : value < debtAnchor
  debt_time_le_first : debtTime ≤ firstTime
  first_time_lt_horizon : firstTime < historyHorizon
  current_failure : firstTime + 1 < target ∨
    missingBelowCount target historyHorizon <
      missingBelowCount target firstTime

inductive CrossingFrontierCurrentDebtOutcome
    (target historyHorizon debtAnchor debtTime : Nat) : Prop
  | target_occurs (witness : Nat) (value_eq : a witness = target) :
      CrossingFrontierCurrentDebtOutcome target historyHorizon debtAnchor
        debtTime
  | current_child (value firstTime : Nat)
      (certificate : CrossingFrontierCurrentChildCertificate target
        historyHorizon debtAnchor debtTime value firstTime) :
      CrossingFrontierCurrentDebtOutcome target historyHorizon debtAnchor
        debtTime
  | debt_child (value firstTime : Nat)
      (certificate : CrossingFrontierDebtChildCertificate target
        historyHorizon debtAnchor debtTime value firstTime) :
      CrossingFrontierCurrentDebtOutcome target historyHorizon debtAnchor
        debtTime
  | middle_residual (value firstTime : Nat)
      (residual : CrossingFrontierMiddleResidual target historyHorizon
        debtAnchor debtTime value firstTime) :
      CrossingFrontierCurrentDebtOutcome target historyHorizon debtAnchor
        debtTime

/-- Refine a successful crossing-frontier first occurrence without creating
the enlarged historical normal node.  Future anchors and rank-compatible
middle anchors become current; debt-time-earlier anchors remain strong debt.
Only the precise two-clock interval failure remains. -/
theorem crossingFrontierFirstAt_currentOrDebt_or_middle
    {target historyHorizon debtAnchor debtValue debtTime value firstTime : Nat}
    (htarget : 0 < target)
    (hhorizonReady : target ≤ historyHorizon + 1)
    (hsource : DebtInvariant target
      ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ debtValue debtTime)
    (htargetValue : target ≤ value)
    (hfirst : FirstAt a value firstTime)
    (hanchor : value < debtAnchor) :
    CrossingFrontierCurrentDebtOutcome target historyHorizon debtAnchor
      debtTime := by
  by_cases htargetEq : value = target
  · exact .target_occurs firstTime (by rw [hfirst.1, htargetEq])
  have htargetLt : target < value :=
    Nat.lt_of_le_of_ne htargetValue (Ne.symm htargetEq)
  by_cases hdebtEarlier : firstTime < debtTime
  · have hfirstHorizon : firstTime < historyHorizon :=
      Nat.lt_trans hdebtEarlier hsource.firstTime_lt_horizon
    let child : PhaseSearchNode :=
      ⟨historyHorizon, debtAnchor, .debt, firstTime⟩
    have hdebt : DebtInvariant target child value firstTime := {
      phase_eq := rfl
      local_eq := rfl
      target_le := htargetValue
      first := hfirst
      firstTime_lt_horizon := hfirstHorizon
      value_lt_anchor := hanchor
    }
    exact .debt_child value firstTime {
      target_lt_value := htargetLt
      first := hfirst
      first_time_lt_debt := hdebtEarlier
      anchor_drop := hanchor
      invariant := hdebt
      progress := phaseSearch_debtTimeDrop hdebtEarlier
    }
  · have hdebtLe : debtTime ≤ firstTime := Nat.le_of_not_gt hdebtEarlier
    by_cases hfuture : historyHorizon ≤ firstTime
    · have hfirstPositive : 0 < firstTime :=
        historicalBridge_firstTime_pos htarget htargetValue hfirst
      rcases exists_coordinatesAt hfirstPositive with
        ⟨q, r, hcoordinates⟩
      have hvalueAtFirst : a firstTime = value := hfirst.1
      have hready : OrbitReadyNormalInvariant target
          (targetStartNode firstTime) := by
        exact ⟨firstTime, q, r, {
          target_positive := htarget
          node_eq := rfl
          time_ready := by omega
          target_le_value := by simpa [hvalueAtFirst] using htargetValue
          coordinates := hcoordinates
        }⟩
      have hprogress : PhaseSearchProgress target
          (targetStartNode firstTime)
          ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ := by
        have hanchor' : a firstTime < debtAnchor := by
          simpa [hvalueAtFirst] using hanchor
        exact phaseSearch_exitDebt_of_extendedHorizonAndAnchor hfuture hanchor'
      exact .current_child value firstTime {
        target_lt_value := htargetLt
        first := hfirst
        anchor_drop := hanchor
        invariant := hready
        progress := hprogress
      }
    · have hfirstHorizon : firstTime < historyHorizon :=
        Nat.lt_of_not_ge hfuture
      by_cases hready : target ≤ firstTime + 1
      · have hbudgetLe := missingBelowCount_antitone (m := target)
          (Nat.le_of_lt hfirstHorizon)
        by_cases hbudgetEq : missingBelowCount target historyHorizon =
            missingBelowCount target firstTime
        · have hfirstPositive : 0 < firstTime :=
            historicalBridge_firstTime_pos htarget htargetValue hfirst
          rcases exists_coordinatesAt hfirstPositive with
            ⟨q, r, hcoordinates⟩
          have hvalueAtFirst : a firstTime = value := hfirst.1
          have hinvariant : OrbitReadyNormalInvariant target
              (targetStartNode firstTime) := by
            exact ⟨firstTime, q, r, {
              target_positive := htarget
              node_eq := rfl
              time_ready := hready
              target_le_value := by simpa [hvalueAtFirst] using htargetValue
              coordinates := hcoordinates
            }⟩
          have hprogress : PhaseSearchProgress target
              (targetStartNode firstTime)
              ⟨historyHorizon, debtAnchor, .debt, debtTime⟩ := by
            change Prod.Lex Nat.lt
              (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
              (missingBelowCount target firstTime,
                (a firstTime,
                  (SearchPhase.normal.rank, a firstTime)))
              (missingBelowCount target historyHorizon,
                (debtAnchor, (SearchPhase.debt.rank, debtTime)))
            rw [← hbudgetEq]
            exact Prod.Lex.right _ (Prod.Lex.left _ _ (by
              simpa [hvalueAtFirst] using hanchor))
          exact .current_child value firstTime {
            target_lt_value := htargetLt
            first := hfirst
            anchor_drop := hanchor
            invariant := hinvariant
            progress := hprogress
          }
        · have hbudgetGap : missingBelowCount target historyHorizon <
              missingBelowCount target firstTime := by omega
          exact .middle_residual value firstTime {
            target_lt_value := htargetLt
            first := hfirst
            anchor_drop := hanchor
            debt_time_le_first := hdebtLe
            first_time_lt_horizon := hfirstHorizon
            current_failure := Or.inr hbudgetGap
          }
      · exact .middle_residual value firstTime {
          target_lt_value := htargetLt
          first := hfirst
          anchor_drop := hanchor
          debt_time_le_first := hdebtLe
          first_time_lt_horizon := hfirstHorizon
          current_failure := Or.inl (by omega)
        }

theorem CrossingFrontierCurrentDebtOutcome.toCurrentOrDebtStep_or_middle
    {target historyHorizon debtAnchor debtTime : Nat}
    (h : CrossingFrontierCurrentDebtOutcome target historyHorizon debtAnchor
      debtTime) :
    (∃ witness, a witness = target) ∨
      (∃ child, CurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child
          ⟨historyHorizon, debtAnchor, .debt, debtTime⟩) ∨
      ∃ value firstTime, CrossingFrontierMiddleResidual target historyHorizon
        debtAnchor debtTime value firstTime := by
  cases h with
  | target_occurs witness hvalue => exact Or.inl ⟨witness, hvalue⟩
  | current_child value firstTime hcurrent =>
      exact Or.inr (Or.inl ⟨targetStartNode firstTime,
        Or.inl hcurrent.invariant, hcurrent.progress⟩)
  | debt_child value firstTime hdebt =>
      exact Or.inr (Or.inl
        ⟨⟨historyHorizon, debtAnchor, .debt, firstTime⟩,
          Or.inr ⟨value, firstTime, hdebt.invariant⟩, hdebt.progress⟩)
  | middle_residual value firstTime hresidual =>
      exact Or.inr (Or.inr ⟨value, firstTime, hresidual⟩)

/-- The typed crossing-frontier package feeds the refined split once the
debt horizon is known target-ready. -/
theorem CrossingFrontierNormalProvenance.currentOrDebt_or_middle
    {target : Nat} {parent child : PhaseSearchNode}
    (h : CrossingFrontierNormalProvenance target parent child)
    (hhorizonReady : target ≤ h.historyHorizon + 1) :
    CrossingFrontierCurrentDebtOutcome target h.historyHorizon h.debtAnchor
      h.debtTime := by
  rcases h with
    ⟨historyHorizon, debtAnchor, debtValue, debtTime, frontierValue,
      frontierFirstTime, htarget, hparent, hsource, htargetFrontier,
      hfirst, hanchor, hchild, hroot, hrank⟩
  simp only at hhorizonReady ⊢
  exact crossingFrontierFirstAt_currentOrDebt_or_middle htarget
    hhorizonReady hsource htargetFrontier hfirst hanchor

/-- The middle interval is realized by the first strict-crossing debt state:
`a 3 = 6` lies above target five and below anchor seven, but time three is
not target-ready while the debt horizon is four. -/
theorem crossingFrontierMiddleResidual_actual :
    CrossingFrontierMiddleResidual 5 4 7 3 6 3 := by
  exact {
    target_lt_value := by decide
    first := by
      constructor
      · decide
      · intro u hu
        have hcases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
        rcases hcases with h | h | h <;> subst u <;> decide
    anchor_drop := by decide
    debt_time_le_first := by decide
    first_time_lt_horizon := by decide
    current_failure := Or.inl (by decide)
  }

/-! ## Debt evolution without historical self-exit -/

/-- Debt evolution can retain every above-target predecessor in debt instead
of exiting to a historical normal node. -/
inductive DebtClosedOutcome
    (target horizon anchor value firstTime : Nat) : Prop
  | target_occurs (witness : Nat) (value_eq : a witness = target) :
      DebtClosedOutcome target horizon anchor value firstTime
  | continue_debt (childValue childTime : Nat)
      (invariant : DebtInvariant target
        ⟨horizon, anchor, .debt, childTime⟩ childValue childTime)
      (progress : PhaseSearchProgress target
        ⟨horizon, anchor, .debt, childTime⟩
        ⟨horizon, anchor, .debt, firstTime⟩) :
      DebtClosedOutcome target horizon anchor value firstTime
  | crossing (obstruction : DebtStepObstruction
      target horizon anchor value firstTime) :
      DebtClosedOutcome target horizon anchor value firstTime

/-- Strengthening of `debtStep_classify` with no `exit_normal` constructor.
The forced-addition predecessor which remains above target is earlier than
the old debt time and below the fixed anchor, hence is itself strong debt. -/
theorem debtStep_classify_without_normalExit
    {target horizon anchor value firstTime : Nat}
    (htarget : 0 < target)
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    DebtClosedOutcome target horizon anchor value firstTime := by
  by_cases htargetValue : target = value
  · exact .target_occurs firstTime (by rw [htargetValue]; exact hinv.first.1)
  have htargetLt : target < value :=
    Nat.lt_of_le_of_ne hinv.target_le htargetValue
  have htimePositive := debt_firstTime_pos htarget hinv
  cases firstTime with
  | zero => omega
  | succ n =>
      rcases firstAt_succ_transition hinv.first with
        ⟨hcan, hvalue⟩ | ⟨hforced, hvalue⟩
      · rcases debt_legalSubtraction_earlierPredecessor hinv hcan with
          ⟨predecessorTime, hfirstPredecessor, htime,
            hvalueLt, hprogress⟩
        by_cases hanchor : a n < anchor
        · have hpreserved := debt_legalSubtraction_preservesInvariant
              hinv hcan hfirstPredecessor htime hanchor
          exact .continue_debt (a n) predecessorTime
            hpreserved.1 hpreserved.2
        · exact .crossing (.legal_reaches_anchor n rfl hcan hvalue htargetLt
            (Nat.le_of_not_gt hanchor))
      · rcases debt_forcedAddition_predecessor hinv hforced with
          ⟨predecessorTime, hfirstPredecessor, htime,
            hanchor, hbelow | habove⟩
        · rcases firstAt_forcedAddition_dichotomy hinv.first hforced with
            hnonpositive | ⟨x, fx, hcandidate, hxPositive,
              hfirstX, hfx, hxValue⟩
          · exact .crossing (.addition_nonpositive n rfl hforced hvalue
              htargetLt hbelow (Nat.le_of_not_gt hnonpositive))
          · have hxTarget : x < target :=
              Nat.lt_trans (by rw [hcandidate]; omega) hbelow
            have hxHorizon : x ∈ valuesThrough horizon :=
              debt_earlier_firstAt_mem_horizon hfirstX hfx
                hinv.firstTime_lt_horizon
            exact .crossing (.addition_seen_below_target n x fx rfl hforced
              hvalue htargetLt hbelow hcandidate hxPositive hfirstX hfx
              hxTarget hxHorizon)
        · have hchild : DebtInvariant target
              ⟨horizon, anchor, .debt, predecessorTime⟩
              (a n) predecessorTime := {
            phase_eq := rfl
            local_eq := rfl
            target_le := habove
            first := hfirstPredecessor
            firstTime_lt_horizon :=
              Nat.lt_trans htime hinv.firstTime_lt_horizon
            value_lt_anchor := hanchor
          }
          exact .continue_debt (a n) predecessorTime hchild
            (phaseSearch_debtTimeDrop htime)

theorem DebtClosedOutcome.toDebtStep_or_obstruction
    {target horizon anchor value firstTime : Nat}
    (h : DebtClosedOutcome target horizon anchor value firstTime) :
    (∃ witness, a witness = target) ∨
      (∃ childValue childTime,
        DebtInvariant target
          ⟨horizon, anchor, .debt, childTime⟩ childValue childTime ∧
        PhaseSearchProgress target
          ⟨horizon, anchor, .debt, childTime⟩
          ⟨horizon, anchor, .debt, firstTime⟩) ∨
      DebtStepObstruction target horizon anchor value firstTime := by
  cases h with
  | target_occurs witness hvalue => exact Or.inl ⟨witness, hvalue⟩
  | continue_debt childValue childTime hinvariant hprogress =>
      exact Or.inr (Or.inl
        ⟨childValue, childTime, hinvariant, hprogress⟩)
  | crossing hobstruction => exact Or.inr (Or.inr hobstruction)

/-- The historical self-exit lies exactly in the two-clock interval: its
first occurrence is before the horizon but equals the debt local time, so it
is neither a future current anchor nor an earlier debt-time child. -/
theorem debtSelfExit_is_middle_boundary
    {target horizon anchor value firstTime : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    firstTime < horizon ∧ ¬ horizon ≤ firstTime ∧ ¬ firstTime < firstTime := by
  have hlt := hinv.firstTime_lt_horizon
  change firstTime < horizon at hlt
  exact ⟨hlt, by omega, Nat.lt_irrefl _⟩

end Recaman
