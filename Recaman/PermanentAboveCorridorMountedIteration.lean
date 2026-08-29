import Recaman.PermanentAboveCorridorLandingInstall

namespace Recaman

noncomputable section

/-! # Well-founded closure of the mounted landing iteration

Re-entering the terminal analysis from a mounted landing crossing changes
only the crossing anchor at a fixed horizon.  A strictly smaller anchor is
an immediate global phase descent, so the mounted node can be returned as a
semantic child directly.  A strictly larger anchor lowers the remaining
anchor gap, which is a plain natural number, so that branch is consumed by
strong induction.  An equal anchor reproduces the parent node literally —
mounted nodes are determined by horizon and anchor — so the only
non-progressing landing is a node-level fixed point.

Together with the discharge-side closure, the entire permanent-tail
analysis now terminates in one of four shapes: a semantic phase child, an
exact discharge replay, a landing whose crossing reproduces the parent
node, or (inside those replays) the pinched finite corridor cycle.
-/

/-- Final outcome of iterating mounted landings to exhaustion. -/
inductive PermanentTailMountedIterationOutcome
    (target start : Nat) : Prop
  | semantic_progress
      (stepParent child : PhaseSearchNode)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child stepParent) :
      PermanentTailMountedIterationOutcome target start
  | exact_replay
      (replayParent : PhaseSearchNode)
      (replaySource : PermanentTailDischargeReturnCertificate target start
        replayParent)
      (replay : TerminalExactDischargeReplayCertificate replaySource) :
      PermanentTailMountedIterationOutcome target start
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
      PermanentTailMountedIterationOutcome target start

/-- Iterating mounted landings terminates: only a semantic child, an exact
discharge replay, or a node-level landing fixed point can remain. -/
theorem PermanentTailCombinedCertificate.mountedIterationOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    PermanentTailMountedIterationOutcome target start := by
  have main : ∀ gap : Nat,
      ∀ (parentNode : PhaseSearchNode) (mTime pTime : Nat)
        (hc : PermanentTailCombinedCertificate target start parentNode
          mTime pTime),
        terminalCrossingAnchorRank target parentNode.anchorParent = gap →
        PermanentTailMountedIterationOutcome target start := by
    intro gap
    induction Nat.lt_wfRel.wf.apply gap with
    | intro gap _ ih =>
        intro parentNode mTime pTime hc hgap
        cases hc.terminalMountedOutcome with
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
              exact .semantic_progress parentNode
                (terminalPredecessorCrossingNode parentNode crossingTime)
                (.crossing_recovery ready.crossing) hprogress
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
        | semantic_progress stepParent child semantic progress =>
            exact .semantic_progress stepParent child semantic progress
        | exact_replay replayParent replaySource replay =>
            exact .exact_replay replayParent replaySource replay
  exact main (terminalCrossingAnchorRank target parent.anchorParent) parent
    minimumTime predecessorFirstTime h rfl

end

end Recaman
