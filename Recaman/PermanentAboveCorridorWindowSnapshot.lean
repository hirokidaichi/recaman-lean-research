import Recaman.PermanentAboveCorridorWindowSelection

namespace Recaman

noncomputable section

/-! # Installed-cycle snapshots for exact terminal-window revisits

An exact `(returnTime, terminalEndpoint)` revisit still may arise from a
different installed parent.  This module records the three outer coordinates
which can decide such a change: the history-budget cursor, parent anchor, and
old crossing time.

Two snapshots admit a total comparison.  The current occurrence can be a
strict edge of the installed-cycle master rank, the stored occurrence can be
a strict edge in the reverse direction, or all three rank coordinates agree.
The reverse constructor is important: merely remembering a prior snapshot
does not orient the next semantic iteration.  A future selection invariant
must exclude rank regression or bound and consume it separately.
-/

/-- Numeric installed-cycle provenance attached to one terminal window. -/
structure TerminalInstalledWindowSnapshot : Type where
  budgetTime : Nat
  anchor : Nat
  oldCrossingTime : Nat
deriving Repr, DecidableEq

/-- The installed master node restricted to its first three coordinates.
Inner coordinates are fixed because comparison is decided before a new
historical blocker restart is chosen. -/
def TerminalInstalledWindowSnapshot.node
    (snapshot : TerminalInstalledWindowSnapshot) :
    TailInstalledCycleSearchNode :=
  ⟨snapshot.budgetTime, snapshot.anchor, snapshot.oldCrossingTime,
    0, .discharge, 0, 0⟩

/-- Snapshot carried by a discharge occurrence. -/
def PermanentTailDischargeReturnCertificate.windowSnapshot
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    TerminalInstalledWindowSnapshot :=
  ⟨parent.horizon, parent.anchorParent, source.oldCrossingTime⟩

theorem PermanentTailDischargeReturnCertificate.windowSnapshot_anchor_below
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    source.windowSnapshot.anchor < target := by
  change parent.anchorParent < target
  rw [source.parent_anchor_eq]
  exact source.old_crossing.below

theorem PermanentTailDischargeReturnCertificate.windowSnapshot_crossing_below_horizon
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    source.windowSnapshot.oldCrossingTime < parent.horizon := by
  change source.oldCrossingTime < parent.horizon
  exact Nat.lt_trans (Nat.lt_succ_self source.oldCrossingTime)
    source.old_crossing_before_horizon

/-- Equality of the three outer numeric coordinates seen by the master rank.
`budgetTime` itself need not agree when it carries the same missing count. -/
structure TerminalInstalledWindowRankPrefixEq
    (target : Nat)
    (left right : TerminalInstalledWindowSnapshot) : Prop where
  missing_budget_eq :
    missingBelowCount target left.budgetTime =
      missingBelowCount target right.budgetTime
  anchor_eq : left.anchor = right.anchor
  old_crossing_time_eq : left.oldCrossingTime = right.oldCrossingTime

/-- Total oriented comparison of two installed snapshots for the same finite
window key. -/
inductive TerminalInstalledWindowSnapshotComparison
    (target : Nat)
    (current stored : TerminalInstalledWindowSnapshot) : Prop
  | current_progress
      (progress : TailInstalledCycleProgress target current.node stored.node) :
      TerminalInstalledWindowSnapshotComparison target current stored
  | stored_progress
      (progress : TailInstalledCycleProgress target stored.node current.node) :
      TerminalInstalledWindowSnapshotComparison target current stored
  | rank_prefix_equal
      (equal : TerminalInstalledWindowRankPrefixEq target current stored) :
      TerminalInstalledWindowSnapshotComparison target current stored

private theorem terminalInstalledWindowSnapshotProgress_of_anchorGrowth
    {target : Nat} {current stored : TerminalInstalledWindowSnapshot}
    (hbudget : missingBelowCount target current.budgetTime =
      missingBelowCount target stored.budgetTime)
    (hcurrentBelow : current.anchor < target)
    (hgrowth : stored.anchor < current.anchor) :
    TailInstalledCycleProgress target current.node stored.node := by
  unfold TailInstalledCycleProgress tailInstalledCycleRank
    TerminalInstalledWindowSnapshot.node
  rw [hbudget]
  exact Prod.Lex.right _
    (Prod.Lex.left _ _
      (Nat.sub_lt_sub_left (Nat.lt_trans hgrowth hcurrentBelow) hgrowth))

private theorem terminalInstalledWindowSnapshotProgress_of_earlierCrossing
    {target : Nat} {current stored : TerminalInstalledWindowSnapshot}
    (hbudget : missingBelowCount target current.budgetTime =
      missingBelowCount target stored.budgetTime)
    (hanchor : current.anchor = stored.anchor)
    (hearlier : current.oldCrossingTime < stored.oldCrossingTime) :
    TailInstalledCycleProgress target current.node stored.node := by
  unfold TailInstalledCycleProgress tailInstalledCycleRank
    TerminalInstalledWindowSnapshot.node
  rw [hbudget, hanchor]
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.left _ _ hearlier))

/-- Lexicographic trichotomy of the master-rank prefix.  Notice that the
second strict branch is a genuine rank regression in iteration direction. -/
theorem terminalInstalledWindowSnapshotComparison_total
    {target : Nat} (current stored : TerminalInstalledWindowSnapshot)
    (hcurrentBelow : current.anchor < target)
    (hstoredBelow : stored.anchor < target) :
    TerminalInstalledWindowSnapshotComparison target current stored := by
  by_cases hhistory :
      missingBelowCount target current.budgetTime <
        missingBelowCount target stored.budgetTime
  · exact .current_progress
      (tailInstalledCycleProgress_of_historyDrop hhistory)
  · by_cases hhistoryReverse :
        missingBelowCount target stored.budgetTime <
          missingBelowCount target current.budgetTime
    · exact .stored_progress
        (tailInstalledCycleProgress_of_historyDrop hhistoryReverse)
    · have hbudget :
          missingBelowCount target current.budgetTime =
            missingBelowCount target stored.budgetTime := by omega
      by_cases hanchor : stored.anchor < current.anchor
      · exact .current_progress
          (terminalInstalledWindowSnapshotProgress_of_anchorGrowth hbudget
            hcurrentBelow hanchor)
      · by_cases hanchorReverse : current.anchor < stored.anchor
        · exact .stored_progress
            (terminalInstalledWindowSnapshotProgress_of_anchorGrowth
              hbudget.symm hstoredBelow hanchorReverse)
        · have hanchorEq : current.anchor = stored.anchor := by omega
          by_cases hcrossing :
              current.oldCrossingTime < stored.oldCrossingTime
          · exact .current_progress
              (terminalInstalledWindowSnapshotProgress_of_earlierCrossing
                hbudget hanchorEq hcrossing)
          · by_cases hcrossingReverse :
                stored.oldCrossingTime < current.oldCrossingTime
            · exact .stored_progress
                (terminalInstalledWindowSnapshotProgress_of_earlierCrossing
                  hbudget.symm hanchorEq.symm hcrossingReverse)
            · exact .rank_prefix_equal {
                missing_budget_eq := hbudget
                anchor_eq := hanchorEq
                old_crossing_time_eq := by omega
              }

/-- One proof-free state entry; validity is retained by the enclosing state. -/
structure TerminalReturnWindowSnapshotEntry : Type where
  key : TerminalReturnWindowKey
  snapshot : TerminalInstalledWindowSnapshot
deriving Repr, DecidableEq

/-- Prior finite-window occurrences together with their installed provenance. -/
structure TerminalReturnWindowSnapshotState (target : Nat) : Type where
  entries : List TerminalReturnWindowSnapshotEntry
  valid_entries : ∀ entry, entry ∈ entries →
    entry.key ∈ terminalReturnWindowKeys target ∧ entry.snapshot.anchor < target

def initialTerminalReturnWindowSnapshotState
    (target : Nat) : TerminalReturnWindowSnapshotState target := {
  entries := []
  valid_entries := by simp
}

def TerminalReturnWindowSnapshotState.record
    {target : Nat} (state : TerminalReturnWindowSnapshotState target)
    (entry : TerminalReturnWindowSnapshotEntry)
    (hkey : entry.key ∈ terminalReturnWindowKeys target)
    (hanchor : entry.snapshot.anchor < target) :
    TerminalReturnWindowSnapshotState target := {
  entries := entry :: state.entries
  valid_entries := by
    intro candidate hmem
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact ⟨hkey, hanchor⟩
    · exact state.valid_entries candidate htail
}

/-- Entry extracted without losing either exact-window or installed-parent
provenance. -/
def TerminalFiniteReturnWindowCertificate.snapshotEntry
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (_finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    TerminalReturnWindowSnapshotEntry :=
  ⟨⟨source.returnTime, terminalEndpoint⟩, source.windowSnapshot⟩

theorem TerminalFiniteReturnWindowCertificate.snapshotEntry_valid
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    finite.snapshotEntry.key ∈ terminalReturnWindowKeys target ∧
      finite.snapshotEntry.snapshot.anchor < target :=
  ⟨finite.key_mem, source.windowSnapshot_anchor_below⟩

/-- Provenance-state result for a finite occurrence.  A new key is recorded;
an old key exposes the stored occurrence and the fully oriented master-prefix
comparison. -/
inductive TerminalReturnWindowSnapshotSelectionOutcome
    (target : Nat) (current : TerminalReturnWindowSnapshotEntry)
    (state : TerminalReturnWindowSnapshotState target) : Type
  | fresh
      (no_prior : ¬ ∃ stored, stored ∈ state.entries ∧
        stored.key = current.key)
      (key_valid : current.key ∈ terminalReturnWindowKeys target)
      (anchor_below : current.snapshot.anchor < target)
      (next_state : TerminalReturnWindowSnapshotState target)
      (next_state_eq : next_state = state.record current
        key_valid anchor_below) :
      TerminalReturnWindowSnapshotSelectionOutcome target current state
  | revisited
      (stored : TerminalReturnWindowSnapshotEntry)
      (stored_mem : stored ∈ state.entries)
      (same_key : stored.key = current.key)
      (comparison : TerminalInstalledWindowSnapshotComparison target
        current.snapshot stored.snapshot) :
      TerminalReturnWindowSnapshotSelectionOutcome target current state

noncomputable def TerminalReturnWindowSnapshotState.select
    {target : Nat} (state : TerminalReturnWindowSnapshotState target)
    (current : TerminalReturnWindowSnapshotEntry)
    (hkey : current.key ∈ terminalReturnWindowKeys target)
    (hanchor : current.snapshot.anchor < target) :
    TerminalReturnWindowSnapshotSelectionOutcome target current state := by
  by_cases hprior : ∃ stored, stored ∈ state.entries ∧
      stored.key = current.key
  · let stored := hprior.choose
    have hstored : stored ∈ state.entries := hprior.choose_spec.1
    have hsame : stored.key = current.key := hprior.choose_spec.2
    have hstoredBelow := (state.valid_entries stored hstored).2
    exact .revisited stored hstored hsame
      (terminalInstalledWindowSnapshotComparison_total current.snapshot
        stored.snapshot hanchor hstoredBelow)
  · exact .fresh hprior hkey hanchor (state.record current hkey hanchor) rfl

/-- The full finite certificate invokes snapshot-aware selection directly. -/
noncomputable def TerminalFiniteReturnWindowCertificate.snapshotSelection
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (state : TerminalReturnWindowSnapshotState target) :
    TerminalReturnWindowSnapshotSelectionOutcome target finite.snapshotEntry
      state :=
  state.select finite.snapshotEntry finite.snapshotEntry_valid.1
    finite.snapshotEntry_valid.2

end

end Recaman
