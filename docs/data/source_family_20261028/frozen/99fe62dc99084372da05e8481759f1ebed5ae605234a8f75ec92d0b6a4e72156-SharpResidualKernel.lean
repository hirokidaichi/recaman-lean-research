import Recaman.TargetStreamUpwardResets
import Recaman.TargetStreamBlockerUnbounded
import Recaman.EventualHighCorridorSupply

namespace Recaman

/-! # Sharp residual kernel of a missing permanent tail

The residual kernel splits every hypothetical missing permanent tail into
two branches: an eventual high-candidate corridor, or a fixed-root
unbounded right-terminal stream.  Both branches have since been sharpened
by several independent modules.  This module bundles those sharpenings at
one explicit cutoff, respectively one explicit root, so that downstream
work can consume a single handoff certificate per branch.

The corridor bundle records the candidate floor, the value law, the fresh
landing stream, the forced-addition recurrence, and the self-fueling
supplier window.  The reset-stream bundle records the separator root as a
certified pre-tail first occurrence, the blocker floor at that root, the
escape of blockers past every ceiling, and the upward blocker resets with
their entry interface.  The kernel theorem then cases on the original
disjunction and fills each bundle from the committed sharpenings.
-/

/-- Everything now known about the eventual high-candidate corridor,
bundled at one explicit cutoff.  Audit note: the `forced_additions` field
is unconditionally true (`exists_forcedAddition_of_ray`); it is kept for
interface completeness.  The corridor-bound content lives in
`candidate_high`, `value_law`, `fresh_landings`, and the value-law
conjunct of `self_fueled`. -/
structure SharpCorridor (target tailStart cutoff : Nat) : Prop where
  tail_le : tailStart ≤ cutoff
  candidate_high : ∀ n, cutoff ≤ n → target < nextSubtractionCandidate (n + 1)
  value_law : ∀ n, cutoff < n → target + (n + 1) < a n
  fresh_landings : ∀ M, ∃ n, M ≤ n ∧
    target + (n + 2) < a (n + 1) ∧ FirstAt a (a (n + 1)) (n + 1)
  forced_additions : ∀ M, ∃ n, M ≤ n ∧ ¬ CanSubtract (n + 1) (stateAt n)
  self_fueled : ∀ n, cutoff + 1 ≤ n →
    ¬ CanSubtract (n + 1) (stateAt n) →
    upperTri cutoff < nextSubtractionCandidate n →
    ∃ t, cutoff < t ∧ t ≤ n ∧
      a t = nextSubtractionCandidate n ∧
      t + 1 + target < nextSubtractionCandidate n ∧
      nextSubtractionCandidate n ≤ upperTri t

/-- Everything now known about the fixed-root right-terminal stream,
bundled at one explicit root. -/
structure SharpResetStream (target tailStart root rootFirstTime : Nat) : Prop where
  target_lt_root : target < root
  root_first : FirstAt a root rootFirstTime
  root_preTail : rootFirstTime ≤ tailStart
  stream : UnboundedRightTerminalStream target tailStart root
  blocker_floor : ∀ start length blocker,
    tailStart < start →
    HistoryTerminatedComb start length blocker →
    root ≤ blocker
  blockers_unbounded : ∀ B, ∃ start length blocker,
    tailStart < start ∧
    nextSubtractionCandidate start < target ∧
    HistoryTerminatedComb start length blocker ∧
    B < blocker
  upward_resets : ∀ cutoff,
    ∃ s₁ k₁ blocker₁ s₂ k₂ blocker₂,
      cutoff < s₁ ∧
      TargetMacroSuccessor target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ ∧
      blocker₁ < blocker₂ ∧
      a s₁ ≤ blocker₂

/-- **Sharp residual kernel.**  Every hypothetical missing permanent tail
falls into a sharp corridor or a sharp reset stream. -/
theorem MissingPermanentAboveTail.sharpResidualKernel
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart) :
    (∃ cutoff, SharpCorridor target tailStart cutoff) ∨
      ∃ root rootFirstTime, SharpResetStream target tailStart root rootFirstTime := by
  rcases htail.eventualHigh_or_unboundedRightTerminal with heventual | hright
  · have hcorridor := heventual
    rcases heventual with ⟨cutoff, htailLe, hhigh⟩
    exact Or.inl ⟨cutoff, {
      tail_le := htailLe
      candidate_high := hhigh
      value_law := fun n hn => corridor_value_law hhigh hn
      fresh_landings := hcorridor.infinitely_many_high_fresh_landings
      forced_additions := corridor_infinitely_many_forcedAdditions hhigh
      self_fueled := fun n hn hnot hbig =>
        corridor_forcedAddition_supplier hhigh hn hnot hbig
    }⟩
  · rcases hright with
      ⟨root, rootFirstTime, htargetRoot, hrootFirst, hrootPre, hstream⟩
    exact Or.inr ⟨root, rootFirstTime, {
      target_lt_root := htargetRoot
      root_first := hrootFirst
      root_preTail := hrootPre
      stream := hstream
      blocker_floor := fun start length blocker hstart hcomb =>
        hstream.blocker_floor hrootFirst hrootPre hstart hcomb
      blockers_unbounded := fun B => hstream.exists_blocker_gt B
      upward_resets := fun cutoff =>
        hstream.exists_upwardReset_entry_le_after htail cutoff
    }⟩

/-- In a sharp reset stream, target-low combs carry blockers simultaneously
at or above the separator root and strictly above any prescribed ceiling:
the blocker floor and the blocker escape compose at one comb. -/
theorem SharpResetStream.exists_blocker_in_band
    {target tailStart root rootFirstTime : Nat}
    (h : SharpResetStream target tailStart root rootFirstTime)
    (B : Nat) :
    ∃ start length blocker,
      tailStart < start ∧
      nextSubtractionCandidate start < target ∧
      HistoryTerminatedComb start length blocker ∧
      root ≤ blocker ∧
      B < blocker := by
  rcases h.blockers_unbounded B with
    ⟨start, length, blocker, hstart, hlow, hcomb, hceiling⟩
  exact ⟨start, length, blocker, hstart, hlow, hcomb,
    h.blocker_floor start length blocker hstart hcomb, hceiling⟩

end Recaman
