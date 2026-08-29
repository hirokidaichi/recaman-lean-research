import Recaman.RefinedLandingMount
import Recaman.PermanentAboveCorridorMountedIteration

namespace Recaman

noncomputable section

/-! # Exhausting mounted landings with the pinned semantic branch

Re-entering the terminal analysis from a mounted landing crossing changes
only the crossing anchor at a fixed horizon, so the anchor gap is a plain
natural number and the iteration is consumed by strong induction.  A
strictly smaller anchor is an immediate global phase descent and is returned
as a semantic child; an equal anchor reproduces the parent node.

This stage repeats that exhaustion with the certificate-tied
`RefinedSemanticEdge` payload.  The descent branch is the one place in the
whole chain where a semantic child is *created* rather than forwarded, and
it is exactly the shape stored by `RefinedSemanticEdge.mounted_crossing`:
the combined certificate at the current parent, the mounted ready crossing,
and the anchor-drop progress edge into that same parent.
-/

/-- Refinement of `PermanentTailMountedIterationOutcome`. -/
inductive RefinedMountedIterationOutcome (target start : Nat) : Prop
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      RefinedMountedIterationOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      RefinedMountedIterationOutcome target start
  | landing_fixed_point
      (parent : PhaseSearchNode)
      (minimumTime predecessorFirstTime : Nat)
      (combined : PermanentTailCombinedCertificate target start parent
        minimumTime predecessorFirstTime)
      (childTime parentTime value landingTime crossingTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime)
      (value_below : value < target)
      (landing_first : FirstAt a value landingTime)
      (next_crossing : FirstWeakUpcrossingStep target landingTime
        crossingTime)
      (crossing_before_start : crossingTime + 1 ≤ start)
      (ready : ReadyCrossingSearchInvariant target
        (terminalPredecessorCrossingNode parent crossingTime))
      (anchor_eq : a crossingTime = parent.anchorParent)
      (node_eq : terminalPredecessorCrossingNode parent crossingTime =
        parent)
      (after_parent : parentTime < landingTime)
      (landing_cursor : TerminalHistoryCursor target landingTime) :
      RefinedMountedIterationOutcome target start

/-- Refined form of `mountedIterationOutcome`. -/
theorem PermanentTailCombinedCertificate.refinedMountedIterationOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    RefinedMountedIterationOutcome target start := by
  have main : ∀ gap : Nat,
      ∀ (parentNode : PhaseSearchNode) (mTime pTime : Nat)
        (hc : PermanentTailCombinedCertificate target start parentNode
          mTime pTime),
        terminalCrossingAnchorRank target parentNode.anchorParent = gap →
        RefinedMountedIterationOutcome target start := by
    intro gap
    induction Nat.lt_wfRel.wf.apply gap with
    | intro gap _ ih =>
        intro parentNode mTime pTime hc hgap
        cases hc.refinedTerminalMountedOutcome with
        | landing_crossing childTime parentTime progress value landingTime
            crossingTime hvalue hafter hfirst hnext hcrossStart
            hcrossHorizon ready hbeforeChild hcursor =>
            by_cases hdrop : a crossingTime < parentNode.anchorParent
            · rcases hc.crossing.ready_crossing.crossing with
                ⟨oldAnchor, oldTime, quotient, remainder, hold⟩
              have hparentAnchor : parentNode.anchorParent = a oldTime := by
                simpa using congrArg PhaseSearchNode.anchorParent
                  hold.node_eq
              have hdrop' : a crossingTime < a oldTime := by
                rw [← hparentAnchor]
                exact hdrop
              have hprogress : PhaseSearchProgress target
                  (terminalPredecessorCrossingNode parentNode crossingTime)
                  parentNode := by
                rw [hold.node_eq]
                exact phaseSearchProgress_of_horizonAndAnchor
                  (Nat.le_refl _) hdrop'
              exact .refined_semantic
                (.mounted_crossing parentNode mTime pTime crossingTime hc
                  ready hprogress)
            · by_cases hgrow : parentNode.anchorParent < a crossingTime
              · have hcombined' := hc.installReadyCrossing ready
                have hbelow := hnext.crossing.below
                have hrank : terminalCrossingAnchorRank target
                    (terminalPredecessorCrossingNode parentNode
                      crossingTime).anchorParent < gap := by
                  rw [← hgap]
                  show terminalCrossingAnchorRank target (a crossingTime) <
                    terminalCrossingAnchorRank target
                      parentNode.anchorParent
                  unfold terminalCrossingAnchorRank
                  exact Nat.sub_lt_sub_left
                    (Nat.lt_trans hgrow hbelow) hgrow
                exact ih _ hrank
                  (terminalPredecessorCrossingNode parentNode crossingTime)
                  mTime pTime hcombined' rfl
              · have hsame : a crossingTime = parentNode.anchorParent := by
                  omega
                have hnodeEq : terminalPredecessorCrossingNode parentNode
                    crossingTime = parentNode := by
                  rcases hc.crossing.ready_crossing.crossing with
                    ⟨oldAnchor, oldTime, quotient, remainder, hold⟩
                  have hanchor : parentNode.anchorParent = a oldTime := by
                    simpa using congrArg PhaseSearchNode.anchorParent
                      hold.node_eq
                  show (⟨parentNode.horizon, a crossingTime, .normal,
                    a crossingTime⟩ : PhaseSearchNode) = parentNode
                  rw [hsame, hanchor]
                  exact hold.node_eq.symm
                exact .landing_fixed_point parentNode mTime pTime hc
                  childTime parentTime value landingTime crossingTime
                  progress hvalue hfirst hnext hcrossStart ready hsame
                  hnodeEq hafter hcursor
        | refined_semantic edge =>
            exact .refined_semantic edge
        | exact_replay replayParent replaySource replay =>
            exact .exact_replay replayParent replaySource replay
  exact main (terminalCrossingAnchorRank target parent.anchorParent) parent
    minimumTime predecessorFirstTime h rfl

end

end Recaman
