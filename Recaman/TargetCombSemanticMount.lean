import Recaman.TargetCombTimeAncestry
import Recaman.PreTailBudgetSeparation
import Recaman.ExtendedHistoryDirectRefined

namespace Recaman

/-! # Semantic mounting of a terminal comb blocker

The normal node obtained by re-anchoring a completed comb at its historical
terminal blocker is not a current orbit node: its horizon is the comb entry
time `s`, whereas its stored value occurred strictly before `s`.  It is,
however, an exact extended-history normal node.  More directly, the blocker
first enters the ready strong-debt constructor at the unchanged current
horizon, so the refined recursion can accept it before the debt-to-normal
exit is taken.
-/

/-- Completed lower history makes every later horizon target-ready. -/
theorem MissingPermanentAboveTail.horizon_ready_of_start_le
    {target start horizon : Nat}
    (h : MissingPermanentAboveTail target start)
    (htime : start ≤ horizon) :
    target ≤ horizon + 1 := by
  have hcovered : coveredBelowCount target start = target :=
    coveredBelowCount_eq_of_covered target h.below_covered
  have hslots := coveredBelowCount_le_time target start
  omega

/-- The historical blocker normal node is never orbit-ready.  Its anchor is
strictly below the actual value at its stored horizon. -/
theorem HistoryTerminatedComb.blockerNormal_not_orbitReady
    {target s k blocker : Nat}
    (hcomb : HistoryTerminatedComb s k blocker) :
    ¬ OrbitReadyNormalInvariant target
      ⟨s, blocker, .normal, blocker⟩ := by
  have hexit := hcomb.episode.run.exit_value
  have hblockerEntry : blocker < a s := by
    rw [hcomb.blocker_eq] at hexit
    omega
  rintro ⟨time, quotient, remainder, hready⟩
  have htime : time = s := by
    simpa using
      (congrArg PhaseSearchNode.horizon hready.node_eq).symm
  subst time
  have hanchor : blocker = a s := by
    simpa using congrArg PhaseSearchNode.anchorParent hready.node_eq
  omega

/-- Consequently the re-anchored historical normal node does not belong to
the old current/debt domain.  Its correct refined constructor is
`ExtendedHistoryNormalInvariant`. -/
theorem HistoryTerminatedComb.blockerNormal_not_currentOrDebt
    {target s k blocker : Nat}
    (hcomb : HistoryTerminatedComb s k blocker) :
    ¬ CurrentOrDebtInvariant target
      ⟨s, blocker, .normal, blocker⟩ := by
  rintro (hcurrent | ⟨value, firstTime, hdebt⟩)
  · exact hcomb.blockerNormal_not_orbitReady hcurrent
  · have hphase := hdebt.phase_eq
    simp at hphase

/-- Strongest semantic wrapper for one terminal gate.

The blocker first gives a ready debt child of the actual entry node.  Its
self-exit is the historical normal node, which is certified in the complete
extended-history refined domain.  Both individual rank edges and their
composition are retained. -/
theorem HistoryTerminatedComb.tail_blocker_semanticMount
    {target tailStart s k blocker : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart ≤ s)
    (hcomb : HistoryTerminatedComb s k blocker) :
    ∃ firstTime quotient remainder,
      let debtNode : PhaseSearchNode :=
        ⟨s, a s, .debt, firstTime⟩
      let normalNode : PhaseSearchNode :=
        ⟨s, blocker, .normal, blocker⟩
      ReadyDebtInvariant target debtNode blocker firstTime ∧
      ReadyCurrentOrDebtInvariant target debtNode ∧
      OrbitReadyRefinedInvariant target debtNode ∧
      ExtendedHistoryNormalCertificate target normalNode
        firstTime quotient remainder ∧
      ExtendedHistoryNormalInvariant target normalNode ∧
      OrbitReadyRefinedInvariant target normalNode ∧
      PhaseSemanticInvariant target normalNode ∧
      PhaseSearchProgress target debtNode (targetStartNode s) ∧
      PhaseSearchProgress target normalNode debtNode ∧
      PhaseSearchProgress target normalNode (targetStartNode s) := by
  rcases hcomb.tail_blocker_debtNormalProgress htail htime with
    ⟨firstTime, htargetBlocker, hfirst, hfirstTime,
      hblockerEntry, hdebt, _hdirect⟩
  have hhorizonReady : target ≤ s + 1 :=
    htail.horizon_ready_of_start_le htime
  have hfirstPositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · subst firstTime
      have hzeroValue := firstAt_time_zero_value hfirst
      have htargetPositive := htail.target_positive
      omega
    · omega
  rcases exists_coordinatesAt hfirstPositive with
    ⟨quotient, remainder, hcoordinates⟩
  let debtNode : PhaseSearchNode :=
    ⟨s, a s, .debt, firstTime⟩
  let normalNode : PhaseSearchNode :=
    ⟨s, blocker, .normal, blocker⟩
  have hreadyDebt : ReadyDebtInvariant target debtNode blocker firstTime := {
    debt := by simpa [debtNode] using hdebt
    horizon_ready := by simpa [debtNode] using hhorizonReady
  }
  have hreadyCurrentDebt : ReadyCurrentOrDebtInvariant target debtNode :=
    Or.inr ⟨blocker, firstTime, hreadyDebt⟩
  have hrefinedDebt : OrbitReadyRefinedInvariant target debtNode :=
    Or.inl hreadyCurrentDebt
  have hextended : ExtendedHistoryNormalCertificate target normalNode
      firstTime quotient remainder := {
    target_positive := htail.target_positive
    node_eq := by
      dsimp only [normalNode]
      rw [hfirst.1]
    representative_le_horizon := Nat.le_of_lt hfirstTime
    horizon_time_ready := by simpa [normalNode] using hhorizonReady
    target_le_value := by
      rw [hfirst.1]
      exact Nat.le_of_lt htargetBlocker
    coordinates := hcoordinates
  }
  have hextendedInvariant : ExtendedHistoryNormalInvariant target normalNode :=
    ⟨firstTime, quotient, remainder, hextended⟩
  have hrefinedNormal : OrbitReadyRefinedInvariant target normalNode :=
    Or.inr (Or.inl hextendedInvariant)
  have hsemanticNormal : PhaseSemanticInvariant target normalNode :=
    hextended.toPhaseSemanticInvariant
  have henter : PhaseSearchProgress target debtNode (targetStartNode s) := by
    simpa [debtNode, targetStartNode] using
      (phaseSearch_enterDebt
        (m := target) (horizon := s) (anchor := a s)
        (normalLocal := a s) (debtTime := firstTime))
  have hexit : PhaseSearchProgress target normalNode debtNode := by
    simpa [normalNode, debtNode] using
      (phaseSearch_exitDebt_of_anchorDrop
        (m := target) (horizon := s) (childAnchor := blocker)
        (parentAnchor := a s) (childLocal := blocker)
        (parentTime := firstTime) hblockerEntry)
  exact ⟨firstTime, quotient, remainder, hreadyDebt,
    hreadyCurrentDebt, hrefinedDebt, hextended, hextendedInvariant,
    hrefinedNormal, hsemanticNormal, henter, hexit, hexit.trans henter⟩

/-- For recursive use, it is strongest to stop at the ready debt child.  No
historical-normal adapter is needed on the parent-to-child edge. -/
theorem HistoryTerminatedComb.tail_blocker_refinedDebtStep
    {target tailStart s k blocker : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart ≤ s)
    (hcomb : HistoryTerminatedComb s k blocker) :
    ∃ child,
      ReadyCurrentOrDebtInvariant target child ∧
      OrbitReadyRefinedInvariant target child ∧
      PhaseSemanticInvariant target child ∧
      PhaseSearchProgress target child (targetStartNode s) := by
  rcases hcomb.tail_blocker_semanticMount htail htime with
    ⟨firstTime, quotient, remainder, hreadyDebt, hreadyCurrentDebt,
      hrefinedDebt, _hextended, _hextendedInvariant, _hrefinedNormal,
      _hsemanticNormal, henter, _hexit, _hcomposed⟩
  let child : PhaseSearchNode := ⟨s, a s, .debt, firstTime⟩
  have hsemantic : PhaseSemanticInvariant target child :=
    hreadyCurrentDebt.toPhaseSemanticInvariant
  exact ⟨child, hreadyCurrentDebt, hrefinedDebt, hsemantic, henter⟩

/-- Full existing-domain continuation from a terminal comb entry.  The
historical normal child is locally total in the refined domain, and its next
rank edge composes with the mounted debt-to-normal-to-entry edge. -/
theorem HistoryTerminatedComb.tail_blocker_refinedStepFromEntry
    {target tailStart s k blocker : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart ≤ s)
    (hcomb : HistoryTerminatedComb s k blocker) :
    (∃ witness, a witness = target) ∨
      ∃ child,
        OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode s) := by
  rcases hcomb.tail_blocker_semanticMount htail htime with
    ⟨_firstTime, _quotient, _remainder, _hreadyDebt,
      _hreadyCurrentDebt, _hrefinedDebt, _hextended,
      hextendedInvariant, _hrefinedNormal, _hsemanticNormal,
      _henter, _hexit, hnormalFromEntry⟩
  rcases hextendedInvariant.refinedStep with
    hoccurs | ⟨child, hrefined, hchild⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child, hrefined, hchild.trans hnormalFromEntry⟩

/-! ## Mounting between chronological terminal episodes -/

/-- The exhausted tail budget remains zero at every later history horizon. -/
theorem MissingPermanentAboveTail.budget_zero_of_start_le
    {target tailStart horizon : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart ≤ horizon) :
    missingBelowCount target horizon = 0 := by
  apply missingBelowCount_eq_zero_of_belowCovered
  intro value hvalue
  exact valuesThrough_mono htime (htail.below_covered value hvalue)

/-- At two zero-budget normal nodes, a strict anchor drop is enough for
progress even when the child uses a later history horizon. -/
theorem MissingPermanentAboveTail.laterNormal_progress_of_anchorDrop
    {target tailStart parentHorizon childHorizon parentAnchor childAnchor
      parentLocal childLocal : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hparentTime : tailStart ≤ parentHorizon)
    (hchildTime : tailStart ≤ childHorizon)
    (hanchor : childAnchor < parentAnchor) :
    PhaseSearchProgress target
      ⟨childHorizon, childAnchor, .normal, childLocal⟩
      ⟨parentHorizon, parentAnchor, .normal, parentLocal⟩ := by
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (missingBelowCount target childHorizon,
      (childAnchor, (SearchPhase.normal.rank, childLocal)))
    (missingBelowCount target parentHorizon,
      (parentAnchor, (SearchPhase.normal.rank, parentLocal)))
  rw [htail.budget_zero_of_start_le hchildTime,
    htail.budget_zero_of_start_le hparentTime]
  exact Prod.Lex.right _ (Prod.Lex.left _ _ hanchor)

/-- Equal zero budgets also permit entering debt at a later horizon.  The
numeric rank stores the missing-history count, not the raw horizon. -/
theorem MissingPermanentAboveTail.laterDebt_progress_from_normal
    {target tailStart parentHorizon childHorizon anchor parentLocal
      childTime : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hparentTime : tailStart ≤ parentHorizon)
    (hchildTime : tailStart ≤ childHorizon) :
    PhaseSearchProgress target
      ⟨childHorizon, anchor, .debt, childTime⟩
      ⟨parentHorizon, anchor, .normal, parentLocal⟩ := by
  change Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
    (missingBelowCount target childHorizon,
      (anchor, (SearchPhase.debt.rank, childTime)))
    (missingBelowCount target parentHorizon,
      (anchor, (SearchPhase.normal.rank, parentLocal)))
  rw [htail.budget_zero_of_start_le hchildTime,
    htail.budget_zero_of_start_le hparentTime]
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.left _ _ (by
      change 0 < 1
      omega)))

/-- A first occurrence above the missing target, lying before a tail
horizon, is an exact extended-history normal node at that horizon. -/
theorem FirstAt.extendedHistoryNormal_of_tail
    {target tailStart horizon value firstTime : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart ≤ horizon)
    (htarget : target < value)
    (hfirst : FirstAt a value firstTime)
    (hfirstTime : firstTime < horizon) :
    ExtendedHistoryNormalInvariant target
      ⟨horizon, value, .normal, value⟩ := by
  have hfirstPositive : 0 < firstTime := by
    by_cases hzero : firstTime = 0
    · subst firstTime
      have hzeroValue := firstAt_time_zero_value hfirst
      have htargetPositive := htail.target_positive
      omega
    · omega
  rcases exists_coordinatesAt hfirstPositive with
    ⟨quotient, remainder, hcoordinates⟩
  refine ⟨firstTime, quotient, remainder, ?_⟩
  exact {
    target_positive := htail.target_positive
    node_eq := by
      simp only
      rw [hfirst.1]
    representative_le_horizon := Nat.le_of_lt hfirstTime
    horizon_time_ready := htail.horizon_ready_of_start_le htime
    target_le_value := by
      rw [hfirst.1]
      exact Nat.le_of_lt htarget
    coordinates := hcoordinates
  }

/-- A completed comb's fresh integer interval cannot straddle any value
which already had a first occurrence before the entry.  This is the
historical-anchor form of `fresh_intervals_ordered`; the anchor need not
itself be a terminal blocker of an earlier comb. -/
theorem HistoryTerminatedComb.entry_below_or_anchor_le_blocker
    {s k blocker anchor firstTime : Nat}
    (hcomb : HistoryTerminatedComb s k blocker)
    (hfirst : FirstAt a anchor firstTime)
    (hfirstTime : firstTime < s) :
    a s < anchor ∨ anchor ≤ blocker := by
  by_cases hentryBelow : a s < anchor
  · exact Or.inl hentryBelow
  · apply Or.inr
    by_cases hanchorLe : anchor ≤ blocker
    · exact hanchorLe
    exfalso
    have hanchorLeEntry : anchor ≤ a s := Nat.le_of_not_gt hentryBelow
    have hblockerLtAnchor : blocker < anchor := Nat.lt_of_not_ge hanchorLe
    let i := a s - anchor
    have hexit := hcomb.episode.run.exit_value
    rw [hcomb.blocker_eq] at hexit
    have hi : i ≤ k := by
      simp only [i]
      omega
    have hrail := hcomb.episode.run.low_rail i hi
    have hlanding : a (s + 2 * i) = anchor := by
      simp only [i] at hrail ⊢
      omega
    have hfresh := hcomb.episode.low_rail_first hi
    exact hfresh.2 firstTime (by omega)
      (hfirst.1.trans hlanding.symm)

/-- Exact consecutive-episode dichotomy at the refined semantic level.

If the later entry lies to the left of the earlier terminal blocker, the
later blocker-normal node itself is a refined semantic child of the earlier
blocker-normal node.  Otherwise the sole residual is the strict upward
blocker reset supplied by interval ordering. -/
theorem HistoryTerminatedComb.next_blockerNormalProgress_or_upwardReset
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime₁ : tailStart ≤ s₁)
    (h₁ : HistoryTerminatedComb s₁ k₁ blocker₁)
    (h₂ : HistoryTerminatedComb s₂ k₂ blocker₂)
    (hbefore : s₁ + 2 * k₁ < s₂) :
    (ExtendedHistoryNormalInvariant target
        ⟨s₁, blocker₁, .normal, blocker₁⟩ ∧
      OrbitReadyRefinedInvariant target
        ⟨s₁, blocker₁, .normal, blocker₁⟩ ∧
      PhaseSemanticInvariant target
        ⟨s₁, blocker₁, .normal, blocker₁⟩ ∧
      ExtendedHistoryNormalInvariant target
        ⟨s₂, blocker₂, .normal, blocker₂⟩ ∧
      OrbitReadyRefinedInvariant target
        ⟨s₂, blocker₂, .normal, blocker₂⟩ ∧
      PhaseSemanticInvariant target
        ⟨s₂, blocker₂, .normal, blocker₂⟩ ∧
      PhaseSearchProgress target (targetStartNode s₂)
        ⟨s₁, blocker₁, .normal, blocker₁⟩ ∧
      PhaseSearchProgress target
        ⟨s₂, blocker₂, .normal, blocker₂⟩ (targetStartNode s₂) ∧
      PhaseSearchProgress target
        ⟨s₂, blocker₂, .normal, blocker₂⟩
        ⟨s₁, blocker₁, .normal, blocker₁⟩) ∨
      blocker₁ < blocker₂ := by
  have htime₂ : tailStart ≤ s₂ := by omega
  rcases h₁.next_entry_below_or_blocker_lt h₂ hbefore with
    hentryBelow | hreset
  · rcases h₁.tail_blocker_semanticMount htail htime₁ with
      ⟨_firstTime₁, _quotient₁, _remainder₁, _hreadyDebt₁,
        _hreadyCurrentDebt₁, _hrefinedDebt₁, _hextended₁,
        hextendedInvariant₁, hrefinedNormal₁, hsemanticNormal₁,
        _henter₁, _hexit₁, _hcomposed₁⟩
    rcases h₂.tail_blocker_semanticMount htail htime₂ with
      ⟨_firstTime₂, _quotient₂, _remainder₂, _hreadyDebt₂,
        _hreadyCurrentDebt₂, _hrefinedDebt₂, _hextended₂,
        hextendedInvariant₂, hrefinedNormal₂, hsemanticNormal₂,
        _henter₂, _hexit₂, hnormalFromEntry₂⟩
    have hentryProgress : PhaseSearchProgress target (targetStartNode s₂)
        ⟨s₁, blocker₁, .normal, blocker₁⟩ := by
      simpa [targetStartNode] using
        (htail.laterNormal_progress_of_anchorDrop htime₁ htime₂
          hentryBelow)
    exact Or.inl ⟨hextendedInvariant₁, hrefinedNormal₁, hsemanticNormal₁,
      hextendedInvariant₂, hrefinedNormal₂, hsemanticNormal₂, hentryProgress,
      hnormalFromEntry₂, hnormalFromEntry₂.trans hentryProgress⟩
  · exact Or.inr hreset

/-- Once the previous blocker is above the finite pre-tail ceiling, both
branches of the consecutive-episode dichotomy yield a refined extended-
history child of the previous blocker-normal node.  In the upward-reset
branch, the later blocker's time ancestry must cross below the old blocker;
entering that ancestry debt at the later horizon is rank-decreasing because
both tail budgets are zero. -/
theorem HistoryTerminatedComb.next_extendedProgress_of_ceiling
    {target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (htime₁ : tailStart ≤ s₁)
    (h₁ : HistoryTerminatedComb s₁ k₁ blocker₁)
    (h₂ : HistoryTerminatedComb s₂ k₂ blocker₂)
    (hbefore : s₁ + 2 * k₁ < s₂)
    (hceiling : upperTri tailStart < blocker₁) :
    ∃ child,
      ExtendedHistoryNormalInvariant target
        ⟨s₁, blocker₁, .normal, blocker₁⟩ ∧
      PhaseSemanticInvariant target
        ⟨s₁, blocker₁, .normal, blocker₁⟩ ∧
      ExtendedHistoryNormalInvariant target child ∧
      OrbitReadyRefinedInvariant target child ∧
      PhaseSemanticInvariant target child ∧
      PhaseSearchProgress target child
        ⟨s₁, blocker₁, .normal, blocker₁⟩ := by
  have htime₂ : tailStart ≤ s₂ := by omega
  rcases h₁.tail_blocker_semanticMount htail htime₁ with
    ⟨_firstTime₁, _quotient₁, _remainder₁, _hreadyDebt₁,
      _hreadyCurrentDebt₁, _hrefinedDebt₁, _hextended₁,
      hextendedInvariant₁, _hrefinedNormal₁, hsemanticNormal₁,
      _henter₁, _hexit₁, _hcomposed₁⟩
  rcases h₁.next_blockerNormalProgress_or_upwardReset
      htail htime₁ h₂ hbefore with hleft | hreset
  · rcases hleft with
      ⟨_hextendedNormal₁, _hrefinedNormal₁, _hsemanticNormal₁,
        hextendedNormal₂, hrefinedNormal₂, hsemanticNormal₂,
        _hentryProgress, _hnormalFromEntry₂,
        hnormalFromPrevious₂⟩
    exact ⟨⟨s₂, blocker₂, .normal, blocker₂⟩,
      hextendedInvariant₁, hsemanticNormal₁, hextendedNormal₂,
      hrefinedNormal₂, hsemanticNormal₂, hnormalFromPrevious₂⟩
  · rcases h₂.tail_blocker_debtNormalProgress htail htime₂ with
      ⟨firstTime, htargetBlocker₂, hfirstBlocker₂,
        hfirstTime₂, _hblockerEntry₂, _hdebt₂, _hdirect₂⟩
    have henter : PhaseSearchProgress target
        ⟨s₂, blocker₁, .debt, firstTime⟩
        ⟨s₁, blocker₁, .normal, blocker₁⟩ :=
      htail.laterDebt_progress_from_normal htime₁ htime₂
    rcases hfirstBlocker₂.normalProgress_of_preTailCeiling_lt_anchor
        htail hceiling htargetBlocker₂ (Nat.le_of_lt hreset)
        hfirstTime₂ with
      ⟨childValue, childFirstTime, htargetChild, _hchildAnchor,
        hfirstChild, hchildTime, _hchildDebt, hnormalProgress⟩
    let child : PhaseSearchNode :=
      ⟨s₂, childValue, .normal, childValue⟩
    have hextendedChild : ExtendedHistoryNormalInvariant target child := by
      simpa [child] using hfirstChild.extendedHistoryNormal_of_tail
        htail htime₂ htargetChild (Nat.lt_trans hchildTime hfirstTime₂)
    have hrefinedChild : OrbitReadyRefinedInvariant target child :=
      Or.inr (Or.inl hextendedChild)
    have hsemanticChild : PhaseSemanticInvariant target child :=
      hrefinedChild.toPhaseSemanticInvariant
    have hprogress : PhaseSearchProgress target child
        ⟨s₁, blocker₁, .normal, blocker₁⟩ := by
      simpa [child] using hnormalProgress.trans henter
    exact ⟨child, hextendedInvariant₁, hsemanticNormal₁,
      hextendedChild, hrefinedChild, hsemanticChild, hprogress⟩

/-! ## Exact finite-basin residual -/

/-- Conditional remounting from an arbitrary historical normal anchor.
When a future terminal-comb entry lies strictly below the anchor, the future
blocker-normal node itself is a refined semantic child. -/
theorem HistoryTerminatedComb.blockerNormalProgress_from_historicalAnchor
    {target tailStart parentHorizon anchor anchorFirstTime
      s k blocker : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hparentTime : tailStart ≤ parentHorizon)
    (hfutureTime : tailStart ≤ s)
    (htargetAnchor : target < anchor)
    (hanchorFirst : FirstAt a anchor anchorFirstTime)
    (hanchorBeforeParent : anchorFirstTime < parentHorizon)
    (hcomb : HistoryTerminatedComb s k blocker)
    (hentryBelow : a s < anchor) :
    ExtendedHistoryNormalInvariant target
        ⟨parentHorizon, anchor, .normal, anchor⟩ ∧
      ∃ child,
        ExtendedHistoryNormalInvariant target child ∧
        OrbitReadyRefinedInvariant target child ∧
        PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨parentHorizon, anchor, .normal, anchor⟩ := by
  have hparentExtended : ExtendedHistoryNormalInvariant target
      ⟨parentHorizon, anchor, .normal, anchor⟩ :=
    hanchorFirst.extendedHistoryNormal_of_tail htail hparentTime
      htargetAnchor hanchorBeforeParent
  rcases hcomb.tail_blocker_semanticMount htail hfutureTime with
    ⟨_firstTime, _quotient, _remainder, _hreadyDebt,
      _hreadyCurrentDebt, _hrefinedDebt, _hextended,
      hchildExtended, hchildRefined, hchildSemantic,
      _henter, _hexit, hchildFromEntry⟩
  have hentryProgress : PhaseSearchProgress target (targetStartNode s)
      ⟨parentHorizon, anchor, .normal, anchor⟩ := by
    simpa [targetStartNode] using
      (htail.laterNormal_progress_of_anchorDrop hparentTime
        hfutureTime hentryBelow)
  exact ⟨hparentExtended,
    ⟨⟨s, blocker, .normal, blocker⟩, hchildExtended,
      hchildRefined, hchildSemantic,
      hchildFromEntry.trans hentryProgress⟩⟩

/-- Exact future-terminal routing from a historical anchor.  The left branch
is the conditional semantic remount above.  The only alternative is that the
future terminal blocker stays at or above the active anchor. -/
theorem HistoryTerminatedComb.blockerNormalProgress_or_anchor_le_blocker
    {target tailStart parentHorizon anchor anchorFirstTime
      s k blocker : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (hparentTime : tailStart ≤ parentHorizon)
    (hfutureTime : tailStart ≤ s)
    (hchronology : parentHorizon ≤ s)
    (htargetAnchor : target < anchor)
    (hanchorFirst : FirstAt a anchor anchorFirstTime)
    (hanchorBeforeParent : anchorFirstTime < parentHorizon)
    (hcomb : HistoryTerminatedComb s k blocker) :
    (ExtendedHistoryNormalInvariant target
        ⟨parentHorizon, anchor, .normal, anchor⟩ ∧
      ∃ child,
        ExtendedHistoryNormalInvariant target child ∧
        OrbitReadyRefinedInvariant target child ∧
        PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child
          ⟨parentHorizon, anchor, .normal, anchor⟩) ∨
      anchor ≤ blocker := by
  have hanchorBeforeEntry : anchorFirstTime < s :=
    Nat.lt_of_lt_of_le hanchorBeforeParent hchronology
  rcases hcomb.entry_below_or_anchor_le_blocker
      hanchorFirst hanchorBeforeEntry with hentryBelow | hblocker
  · exact Or.inl (hcomb.blockerNormalProgress_from_historicalAnchor
      htail hparentTime hfutureTime htargetAnchor
      hanchorFirst hanchorBeforeParent hentryBelow)
  · exact Or.inr hblocker

/-- The interval-order, one-use, unboundedness, and historical-provenance
consequences currently available do not force a future entry below a fixed
finite anchor.  This explicit right-moving ladder has singleton fresh
intervals: each previous fresh entry becomes the next historical blocker. -/
theorem finiteBasin_rightLadder_countermodel (anchor : Nat) :
    ∃ entry blocker : Nat → Nat,
      (∀ j, entry j = blocker j + 1) ∧
      (∀ j, blocker (j + 1) = entry j) ∧
      Function.Injective blocker ∧
      (∀ i j, i < j → entry i ≤ blocker j) ∧
      (∀ i j, i < j → blocker i < blocker j) ∧
      (∀ bound, ∃ j, bound < blocker j) ∧
      (∀ j, anchor ≤ blocker j) ∧
      (∀ j, ¬ entry j < anchor) := by
  let blocker : Nat → Nat := fun j => anchor + j
  let entry : Nat → Nat := fun j => anchor + j + 1
  refine ⟨entry, blocker, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [entry, blocker]
  · intro j
    simp only [entry, blocker]
    omega
  · intro i j heq
    simp only [blocker] at heq
    omega
  · intro i j hij
    simp only [entry, blocker]
    omega
  · intro i j hij
    simp only [blocker]
    omega
  · intro bound
    exact ⟨bound + 1, by simp only [blocker]; omega⟩
  · intro j
    simp only [blocker]
    omega
  · intro j
    simp only [entry]
    omega

end Recaman
