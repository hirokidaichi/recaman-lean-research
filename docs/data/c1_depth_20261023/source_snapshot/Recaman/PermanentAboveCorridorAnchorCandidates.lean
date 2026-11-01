import Recaman.PermanentAboveCorridorRestartRank

namespace Recaman

noncomputable section

/-! # Finite anchor candidates of the remaining growth kernel

After the stationary restart is ranked, the only eligible blocker-predecessor
kernel is strict crossing-anchor growth.  Every crossing predecessor remains
strictly below the missing target.  Thus its possible anchors are the explicit
finite list `List.range target`, and growth strictly lowers the remaining
gap `target - anchor`.

The final selection lemma keeps the semantic boundary explicit: the numeric
rank is available once the new crossing anchor is installed as the next
cycle's parent anchor.
-/

/-- All possible predecessor anchors of a strict crossing of `target`. -/
def terminalCrossingAnchorCandidates (target : Nat) : List Nat :=
  List.range target

theorem mem_terminalCrossingAnchorCandidates_iff
    {target anchor : Nat} :
    anchor ∈ terminalCrossingAnchorCandidates target ↔ anchor < target := by
  simp [terminalCrossingAnchorCandidates]

theorem terminalCrossingAnchorCandidates_length (target : Nat) :
    (terminalCrossingAnchorCandidates target).length = target := by
  simp [terminalCrossingAnchorCandidates]

/-- Remaining finite envelope above a crossing predecessor anchor. -/
def terminalCrossingAnchorRank (target anchor : Nat) : Nat :=
  target - anchor

def TerminalCrossingAnchorProgress (target : Nat)
    (childAnchor parentAnchor : Nat) : Prop :=
  terminalCrossingAnchorRank target childAnchor <
    terminalCrossingAnchorRank target parentAnchor

/-- The remaining-anchor-gap relation is well founded. -/
theorem terminalCrossingAnchorProgress_wellFounded (target : Nat) :
    WellFounded (TerminalCrossingAnchorProgress target) := by
  apply WellFounded.intro
  intro anchor
  generalize hrank : terminalCrossingAnchorRank target anchor = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing anchor with
  | intro rank _ ih =>
      apply Acc.intro anchor
      intro childAnchor hchild
      have hrelation :
          terminalCrossingAnchorRank target childAnchor < rank := by
        simpa [TerminalCrossingAnchorProgress, hrank] using hchild
      exact ih (terminalCrossingAnchorRank target childAnchor) hrelation
        childAnchor rfl

/-- Typed finite-candidate data behind a strict anchor-growth outcome. -/
structure TerminalCrossingAnchorGrowthCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    (crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder) : Prop where
  old_anchor_below_target : parent.anchorParent < target
  new_anchor_below_target : a crossingTime < target
  strict_growth : parent.anchorParent < a crossingTime
  old_anchor_mem :
    parent.anchorParent ∈ terminalCrossingAnchorCandidates target
  new_anchor_mem :
    a crossingTime ∈ terminalCrossingAnchorCandidates target
  gap_progress : TerminalCrossingAnchorProgress target
    (a crossingTime) parent.anchorParent

/-- Strict growth of a selected predecessor crossing produces the complete
finite candidate and remaining-gap certificate. -/
theorem TerminalBelowPredecessorCrossingCertificate.anchorGrowthCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    (h : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder)
    (hgrowth : parent.anchorParent < a crossingTime) :
    TerminalCrossingAnchorGrowthCertificate h := by
  have holdBelow : parent.anchorParent < target := by
    rw [source.parent_anchor_eq]
    exact source.old_crossing.below
  have hnewBelow : a crossingTime < target :=
    h.first_crossing.crossing.below
  have hprogress : TerminalCrossingAnchorProgress target
      (a crossingTime) parent.anchorParent := by
    unfold TerminalCrossingAnchorProgress terminalCrossingAnchorRank
    omega
  exact {
    old_anchor_below_target := holdBelow
    new_anchor_below_target := hnewBelow
    strict_growth := hgrowth
    old_anchor_mem := mem_terminalCrossingAnchorCandidates_iff.mpr holdBelow
    new_anchor_mem := mem_terminalCrossingAnchorCandidates_iff.mpr hnewBelow
    gap_progress := hprogress
  }

/-- Explicit provenance boundary for iterating the finite anchor rank. -/
theorem TerminalCrossingAnchorGrowthCertificate.progress_of_selected
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime
      crossingTime quotient remainder nextParentAnchor : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    {below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical}
    {crossing : TerminalBelowPredecessorCrossingCertificate below crossingTime
      quotient remainder}
    (h : TerminalCrossingAnchorGrowthCertificate crossing)
    (hselected : nextParentAnchor = a crossingTime) :
    TerminalCrossingAnchorProgress target nextParentAnchor
      parent.anchorParent := by
  subst nextParentAnchor
  exact h.gap_progress

/-- Total eligible outcome with the last kernel converted to a finite anchor
candidate and a strict well-founded gap edge. -/
inductive TerminalBelowPredecessorFiniteRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (below : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical) : Prop
  | phase_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : PhaseSearchProgress target
        (terminalPredecessorCrossingNode parent crossingTime) parent) :
      TerminalBelowPredecessorFiniteRankOutcome below
  | restart_cycle_progress
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (progress : TailRestartCycleProgress target
        ⟨a crossingTime, crossingTime, firstTime - 1, .crossing,
          firstTime - 1, 0⟩
        ⟨parent.anchorParent, source.oldCrossingTime, firstTime, .discharge,
          firstTime, 0⟩) :
      TerminalBelowPredecessorFiniteRankOutcome below
  | finite_anchor_growth
      (crossingTime quotient remainder : Nat)
      (certificate : TerminalBelowPredecessorCrossingCertificate below
        crossingTime quotient remainder)
      (growth : TerminalCrossingAnchorGrowthCertificate certificate) :
      TerminalBelowPredecessorFiniteRankOutcome below

theorem BelowTargetHistoricalPredecessorCertificate.finiteRankOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical)
    (holdEligible : source.downTime + 1 ≤ source.oldCrossingTime) :
    TerminalBelowPredecessorFiniteRankOutcome h := by
  cases h.restartRankOutcome holdEligible with
  | phase_progress crossingTime quotient remainder certificate progress =>
      exact .phase_progress crossingTime quotient remainder certificate
        progress
  | restart_cycle_progress crossingTime quotient remainder certificate
      progress =>
      exact .restart_cycle_progress crossingTime quotient remainder certificate
        progress
  | anchor_growth crossingTime quotient remainder certificate growth =>
      exact .finite_anchor_growth crossingTime quotient remainder certificate
        (certificate.anchorGrowthCertificate growth)

end

end Recaman
