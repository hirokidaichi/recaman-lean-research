import Recaman.PermanentAboveCycleRank

namespace Recaman

noncomputable section

/-! # Canonical discharge returns and a crossing cursor

The permanent-tail cycle reaches a historical downcross in a strictly
descending discharge phase.  This module keeps the complete provenance of
the canonical upcrossing which returns from that endpoint.  It then refines
the outer crossing key from just the predecessor value to the pair
`(predecessor value, crossing time)`.

Consequently, an equal-anchor return is progress whenever it reaches an
earlier crossing.  Under the natural condition that the old crossing is
eligible from the downcross endpoint, the only non-progress cases are now
strict anchor growth or the literal same anchor at the same time.
-/

/-- Complete proof data for returning canonically from the historical
downcross of a combined permanent-tail obstruction. -/
structure PermanentTailDischargeReturnCertificate
    (target start : Nat) (parent : PhaseSearchNode) where
  combinedMinimumTime : Nat
  combinedPredecessorFirstTime : Nat
  combined : PermanentTailCombinedCertificate target start parent
    combinedMinimumTime combinedPredecessorFirstTime
  tailStart : Nat
  historicalMinimumTime : Nat
  historicalFirstTime : Nat
  downTime : Nat
  returnTime : Nat
  oldCrossingTime : Nat
  tailStart_le_start : tailStart ≤ start
  historical_tail : MissingStrictAboveTail target tailStart
  historical_minimum : PermanentTailMinimumCertificate target tailStart
    historicalMinimumTime historicalFirstTime
  downcross : FutureDowncrossStep target historicalFirstTime downTime
  endpoint_first : FirstAt a (a (downTime + 1)) (downTime + 1)
  endpoint_before_tail : downTime + 1 < tailStart
  return_crossing : FirstWeakUpcrossingStep target (downTime + 1) returnTime
  return_before_tail : returnTime + 1 ≤ tailStart
  old_crossing : WeakUpcrossingStep target 0 oldCrossingTime
  parent_anchor_eq : parent.anchorParent = a oldCrossingTime

/-- The finite historical descent and least-upcrossing theorem assemble into
one typed discharge/return certificate. -/
theorem PermanentTailCombinedCertificate.exists_dischargeReturnCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    Nonempty (PermanentTailDischargeReturnCertificate target start parent) := by
  rcases h.tail.exists_historicalDowncrossCertificate with
    ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
      htailStart, hhistoricalTail, hhistoricalMinimum, hdown, hendpointFirst,
      hendpointBefore, hbudgetDrop⟩
  rcases exists_firstWeakUpcrossingStep_from_below h.tail.target_positive
      hdown.endpoint_below with ⟨returnTime, hreturn⟩
  have htailAbove := hhistoricalTail.strictly_above tailStart
    (Nat.le_refl _)
  rcases exists_weakUpcrossingStep_between
      (Nat.le_of_lt hendpointBefore) hdown.endpoint_below
      (Nat.le_of_lt htailAbove) with
    ⟨witnessTime, hwitness, hwitnessBefore⟩
  have hreturnBefore := hreturn.endpoint_le_of_witness hwitness hwitnessBefore
  rcases h.crossing.ready_crossing.crossing with
    ⟨oldAnchor, oldCrossingTime, quotient, remainder, hold⟩
  have holdCrossing : WeakUpcrossingStep target 0 oldCrossingTime := {
    start_le := Nat.zero_le _
    below := hold.recovery.crossing.1
    endpoint_ge := Nat.le_of_lt hold.recovery.crossing.2.1
    forced_addition := hold.recovery.forced_addition
  }
  have hparentAnchor : parent.anchorParent = a oldCrossingTime := by
    simpa using congrArg PhaseSearchNode.anchorParent hold.node_eq
  exact ⟨{
    combinedMinimumTime := minimumTime
    combinedPredecessorFirstTime := predecessorFirstTime
    combined := h
    tailStart := tailStart
    historicalMinimumTime := historicalMinimumTime
    historicalFirstTime := historicalFirstTime
    downTime := downTime
    returnTime := returnTime
    oldCrossingTime := oldCrossingTime
    tailStart_le_start := htailStart
    historical_tail := hhistoricalTail
    historical_minimum := hhistoricalMinimum
    downcross := hdown
    endpoint_first := hendpointFirst
    endpoint_before_tail := hendpointBefore
    return_crossing := hreturn
    return_before_tail := hreturnBefore
    old_crossing := holdCrossing
    parent_anchor_eq := hparentAnchor
  }⟩

/-- The canonical return finishes strictly before the parent's zero-budget
horizon, so it is genuine historical provenance rather than future data. -/
theorem PermanentTailDischargeReturnCertificate.return_before_parentHorizon
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    h.returnTime + 1 < parent.horizon := by
  exact Nat.lt_of_le_of_lt h.return_before_tail
    (Nat.lt_of_le_of_lt h.tailStart_le_start
      h.combined.crossing.tail_strictly_before_horizon)

/-- A crossing cursor remembers the predecessor anchor and the exact orbit
time which produced it. -/
structure TailCrossingCursor where
  anchor : Nat
  crossingTime : Nat
deriving Repr, DecidableEq

def tailCrossingCursorRank (cursor : TailCrossingCursor) : Nat × Nat :=
  (cursor.anchor, cursor.crossingTime)

def TailCrossingCursorProgress
    (child parent : TailCrossingCursor) : Prop :=
  Prod.Lex Nat.lt Nat.lt
    (tailCrossingCursorRank child) (tailCrossingCursorRank parent)

/-- The cursor refinement remains well founded. -/
theorem tailCrossingCursorProgress_wellFounded :
    WellFounded TailCrossingCursorProgress := by
  apply WellFounded.intro
  intro cursor
  generalize hrank : tailCrossingCursorRank cursor = rank
  have hacc := natPairLex_wellFounded.apply rank
  induction hacc generalizing cursor with
  | intro rank _ ih =>
      apply Acc.intro cursor
      intro child hchild
      have hrelation : Prod.Lex Nat.lt Nat.lt
          (tailCrossingCursorRank child) rank := by
        simpa [TailCrossingCursorProgress, hrank] using hchild
      exact ih (tailCrossingCursorRank child) hrelation child rfl

/-- Exact numeric meaning of cursor progress. -/
theorem tailCrossingCursorProgress_iff
    {childAnchor childTime parentAnchor parentTime : Nat} :
    TailCrossingCursorProgress
        ⟨childAnchor, childTime⟩ ⟨parentAnchor, parentTime⟩ ↔
      childAnchor < parentAnchor ∨
        (childAnchor = parentAnchor ∧ childTime < parentTime) := by
  constructor
  · intro hprogress
    unfold TailCrossingCursorProgress tailCrossingCursorRank at hprogress
    rcases Prod.lex_def.mp hprogress with hanchor | ⟨hanchor, htime⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by simpa using hanchor, by omega⟩
  · intro hprogress
    rcases hprogress with hanchor | ⟨hanchor, htime⟩
    · exact Prod.Lex.left _ _ hanchor
    · rw [hanchor]
      exact Prod.Lex.right _ htime

/-- The residual after adding the time cursor: either the anchor genuinely
grows, or it is equal and the canonical return is not earlier. -/
inductive CanonicalDischargeReturnResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (certificate : PermanentTailDischargeReturnCertificate target start
      parent) : Prop
  | anchor_growth
      (growth : parent.anchorParent < a certificate.returnTime) :
      CanonicalDischargeReturnResidual certificate
  | same_anchor_not_earlier
      (same_anchor : a certificate.returnTime = parent.anchorParent)
      (not_earlier : certificate.oldCrossingTime ≤ certificate.returnTime) :
      CanonicalDischargeReturnResidual certificate

/-- Every canonical discharge return either lowers the well-founded cursor
or belongs to the strictly narrower residual above. -/
theorem PermanentTailDischargeReturnCertificate.cursorProgress_or_residual
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    TailCrossingCursorProgress
        ⟨a h.returnTime, h.returnTime⟩
        ⟨parent.anchorParent, h.oldCrossingTime⟩ ∨
      CanonicalDischargeReturnResidual h := by
  by_cases hanchorDrop : a h.returnTime < parent.anchorParent
  · left
    rw [tailCrossingCursorProgress_iff]
    exact Or.inl hanchorDrop
  by_cases hanchorSame : a h.returnTime = parent.anchorParent
  · by_cases htimeDrop : h.returnTime < h.oldCrossingTime
    · left
      rw [tailCrossingCursorProgress_iff]
      exact Or.inr ⟨hanchorSame, htimeDrop⟩
    · right
      exact .same_anchor_not_earlier hanchorSame
        (Nat.le_of_not_gt htimeDrop)
  · right
    exact .anchor_growth (by omega)

/-- If the old crossing lies after the historical endpoint, it is one of the
eligible upcrossings considered by the canonical return.  Therefore the
return time cannot be later than the old crossing time. -/
theorem PermanentTailDischargeReturnCertificate.returnTime_le_oldCrossingTime
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent)
    (holdEligible : h.downTime + 1 ≤ h.oldCrossingTime) :
    h.returnTime ≤ h.oldCrossingTime := by
  apply h.return_crossing.time_le
  exact {
    start_le := holdEligible
    below := h.old_crossing.below
    endpoint_ge := h.old_crossing.endpoint_ge
    forced_addition := h.old_crossing.forced_addition
  }

/-- With chronological eligibility, the residual is no longer a vague
nondecreasing case: it is strict anchor growth or the exact same anchor at
the exact same crossing time. -/
theorem PermanentTailDischargeReturnCertificate.cursorProgress_or_growth_or_stationary
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent)
    (holdEligible : h.downTime + 1 ≤ h.oldCrossingTime) :
    TailCrossingCursorProgress
        ⟨a h.returnTime, h.returnTime⟩
        ⟨parent.anchorParent, h.oldCrossingTime⟩ ∨
      parent.anchorParent < a h.returnTime ∨
      (a h.returnTime = parent.anchorParent ∧
        h.returnTime = h.oldCrossingTime) := by
  rcases h.cursorProgress_or_residual with hprogress | hresidual
  · exact Or.inl hprogress
  · right
    cases hresidual with
    | anchor_growth hgrowth => exact Or.inl hgrowth
    | same_anchor_not_earlier hsame hnotEarlier =>
        right
        have hle := h.returnTime_le_oldCrossingTime holdEligible
        exact ⟨hsame, by omega⟩

/-- Canonicalizing an old crossing which is already canonical returns the
identical time.  Thus a time cursor removes noncanonical equal-anchor loops,
but cannot by itself remove the literal stationary crossing. -/
theorem PermanentTailDischargeReturnCertificate.stationary_of_oldCanonical
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent)
    (holdCanonical : FirstWeakUpcrossingStep target (h.downTime + 1)
      h.oldCrossingTime) :
    h.returnTime = h.oldCrossingTime :=
  h.return_crossing.unique holdCanonical

/-- Five-coordinate rank used after adding the crossing-time cursor. -/
theorem natQuintLex_wellFounded :
    WellFounded
      (Prod.Lex Nat.lt
        (Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)))) := by
  apply WellFounded.intro
  intro tuple
  exact Prod.lexAccessible
    (Nat.lt_wfRel.wf.apply tuple.1)
    (fun quadruple => natQuadLex_wellFounded.apply quadruple)
    tuple.2

/-- Full permanent-tail cycle node with the exact crossing time retained
beneath its anchor. -/
structure TailCursorCycleSearchNode where
  anchor : Nat
  crossingTime : Nat
  phase : TailCyclePhase
  historyTime : Nat
  minimumValue : Nat
deriving Repr, DecidableEq

def tailCursorCycleRank (target : Nat) (node : TailCursorCycleSearchNode) :
    Nat × (Nat × (Nat × (Nat × Nat))) :=
  (node.anchor,
    (node.crossingTime,
      (node.phase.rank,
        (seenBelowCount target node.historyTime, node.minimumValue))))

def TailCursorCycleProgress (target : Nat)
    (child parent : TailCursorCycleSearchNode) : Prop :=
  Prod.Lex Nat.lt
      (Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)))
    (tailCursorCycleRank target child) (tailCursorCycleRank target parent)

/-- The cursor-refined permanent-tail cycle is well founded. -/
theorem tailCursorCycleProgress_wellFounded (target : Nat) :
    WellFounded (TailCursorCycleProgress target) := by
  apply WellFounded.intro
  intro node
  generalize hrank : tailCursorCycleRank target node = rank
  have hacc := natQuintLex_wellFounded.apply rank
  induction hacc generalizing node with
  | intro rank _ ih =>
      apply Acc.intro node
      intro child hchild
      have hrelation :
          Prod.Lex Nat.lt
              (Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)))
            (tailCursorCycleRank target child) rank := by
        simpa [TailCursorCycleProgress, hrank] using hchild
      exact ih (tailCursorCycleRank target child) hrelation child rfl

/-- A cursor decrease hides the otherwise upward `discharge → crossing`
phase transition and therefore closes the full cycle edge. -/
theorem tailCursorCycle_exit_of_cursorProgress
    {target childAnchor childCrossingTime parentAnchor parentCrossingTime
      childHistoryTime parentHistoryTime childMinimum parentMinimum : Nat}
    (hcursor : TailCrossingCursorProgress
      ⟨childAnchor, childCrossingTime⟩
      ⟨parentAnchor, parentCrossingTime⟩) :
    TailCursorCycleProgress target
      ⟨childAnchor, childCrossingTime, .crossing,
        childHistoryTime, childMinimum⟩
      ⟨parentAnchor, parentCrossingTime, .discharge,
        parentHistoryTime, parentMinimum⟩ := by
  rw [tailCrossingCursorProgress_iff] at hcursor
  rcases hcursor with hanchor | ⟨hanchor, htime⟩
  · exact Prod.Lex.left _ _ hanchor
  · rw [hanchor]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ htime)

/-- Conversely, the full cycle can return upward from discharge only when
the `(anchor, crossing time)` cursor decreases. -/
theorem tailCursorCycle_exit_iff_cursorProgress
    {target childAnchor childCrossingTime parentAnchor parentCrossingTime
      childHistoryTime parentHistoryTime childMinimum parentMinimum : Nat} :
    TailCursorCycleProgress target
        ⟨childAnchor, childCrossingTime, .crossing,
          childHistoryTime, childMinimum⟩
        ⟨parentAnchor, parentCrossingTime, .discharge,
          parentHistoryTime, parentMinimum⟩ ↔
      TailCrossingCursorProgress
        ⟨childAnchor, childCrossingTime⟩
        ⟨parentAnchor, parentCrossingTime⟩ := by
  constructor
  · intro hprogress
    unfold TailCursorCycleProgress tailCursorCycleRank at hprogress
    rcases Prod.lex_def.mp hprogress with hanchor | ⟨hanchorEq, hrest⟩
    · rw [tailCrossingCursorProgress_iff]
      exact Or.inl hanchor
    · rcases Prod.lex_def.mp hrest with htime | ⟨htimeEq, hphaseRest⟩
      · rw [tailCrossingCursorProgress_iff]
        exact Or.inr ⟨by simpa using hanchorEq, htime⟩
      · rcases Prod.lex_def.mp hphaseRest with hphase | ⟨hphaseEq, _⟩
        · simp [TailCyclePhase.rank] at hphase
        · simp [TailCyclePhase.rank] at hphaseEq
  · exact tailCursorCycle_exit_of_cursorProgress

/-- The typed discharge certificate now yields either a genuine exit in the
full well-founded cycle or the narrowed canonical residual. -/
theorem PermanentTailDischargeReturnCertificate.cycleExit_or_residual
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    TailCursorCycleProgress target
        ⟨a h.returnTime, h.returnTime, .crossing,
          h.returnTime, h.historicalMinimumTime⟩
        ⟨parent.anchorParent, h.oldCrossingTime, .discharge,
          h.downTime + 1, h.historicalMinimumTime⟩ ∨
      CanonicalDischargeReturnResidual h := by
  rcases h.cursorProgress_or_residual with hprogress | hresidual
  · exact Or.inl (tailCursorCycle_exit_of_cursorProgress hprogress)
  · exact Or.inr hresidual

/-- Final kernel after also exposing chronological eligibility.  A failed
cursor exit is now one of three concrete phenomena, with no hidden generic
nondecreasing case. -/
inductive CanonicalDischargeKernelResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (certificate : PermanentTailDischargeReturnCertificate target start
      parent) : Prop
  | anchor_growth
      (growth : parent.anchorParent < a certificate.returnTime) :
      CanonicalDischargeKernelResidual certificate
  | old_crossing_before_endpoint
      (old_before : certificate.oldCrossingTime < certificate.downTime + 1) :
      CanonicalDischargeKernelResidual certificate
  | stationary
      (same_anchor : a certificate.returnTime = parent.anchorParent)
      (same_time : certificate.returnTime = certificate.oldCrossingTime) :
      CanonicalDischargeKernelResidual certificate

/-- The full cycle either exits or reaches exactly one of the three typed
kernel obstructions: value growth, wrong chronology, or literal stationarity. -/
theorem PermanentTailDischargeReturnCertificate.cycleExit_or_kernelResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent) :
    TailCursorCycleProgress target
        ⟨a h.returnTime, h.returnTime, .crossing,
          h.returnTime, h.historicalMinimumTime⟩
        ⟨parent.anchorParent, h.oldCrossingTime, .discharge,
          h.downTime + 1, h.historicalMinimumTime⟩ ∨
      CanonicalDischargeKernelResidual h := by
  rcases h.cycleExit_or_residual with hprogress | hresidual
  · exact Or.inl hprogress
  · right
    cases hresidual with
    | anchor_growth hgrowth => exact .anchor_growth hgrowth
    | same_anchor_not_earlier hsame hnotEarlier =>
        by_cases holdBefore : h.oldCrossingTime < h.downTime + 1
        · exact .old_crossing_before_endpoint holdBefore
        · have holdEligible : h.downTime + 1 ≤ h.oldCrossingTime :=
            Nat.le_of_not_gt holdBefore
          have hreturnLe := h.returnTime_le_oldCrossingTime holdEligible
          exact .stationary hsame (by omega)

/-- If the old crossing is already the canonical crossing from this exact
endpoint, the kernel really contains the stationary constructor. -/
theorem PermanentTailDischargeReturnCertificate.kernelStationary_of_oldCanonical
    {target start : Nat} {parent : PhaseSearchNode}
    (h : PermanentTailDischargeReturnCertificate target start parent)
    (holdCanonical : FirstWeakUpcrossingStep target (h.downTime + 1)
      h.oldCrossingTime) :
    CanonicalDischargeKernelResidual h := by
  have htime := h.stationary_of_oldCanonical holdCanonical
  refine CanonicalDischargeKernelResidual.stationary ?_ htime
  rw [htime]
  exact h.parent_anchor_eq.symm

/-- The literal same crossing is still forbidden as a full cycle exit. -/
theorem tailCursorCycle_no_stationary_exit
    {target anchor crossingTime childHistoryTime parentHistoryTime
      childMinimum parentMinimum : Nat} :
    ¬ TailCursorCycleProgress target
      ⟨anchor, crossingTime, .crossing, childHistoryTime, childMinimum⟩
      ⟨anchor, crossingTime, .discharge, parentHistoryTime, parentMinimum⟩ := by
  rw [tailCursorCycle_exit_iff_cursorProgress,
    tailCrossingCursorProgress_iff]
  omega

end

end Recaman
