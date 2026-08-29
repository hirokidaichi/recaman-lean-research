import Recaman.PermanentAboveCorridorWindowSnapshot

namespace Recaman

noncomputable section

/-! # Finite selection of installed terminal-window snapshots

The old crossing of every discharge is now known to lie before its parent
horizon.  At a fixed horizon, a terminal occurrence is therefore determined
up to a finite key:

* return time and terminal endpoint;
* parent anchor below the target;
* old crossing time below the horizon.

This key absorbs the reverse-oriented case of numeric snapshot comparison.
Regardless of whether the ordinary master prefix moves forward or backward,
a previously unseen full key is erased from a finite list.  The sole residual
is literal reuse of the same window, anchor, and crossing cursor at the same
horizon.
-/

/-- Exact finite numeric identity of an installed terminal occurrence. -/
structure TerminalReturnInstalledWindowKey : Type where
  window : TerminalReturnWindowKey
  anchor : Nat
  oldCrossingTime : Nat
deriving Repr, DecidableEq

/-- All installed-window identities available below a fixed target and
horizon. -/
def terminalReturnInstalledWindowKeys
    (target horizon : Nat) : List TerminalReturnInstalledWindowKey :=
  (terminalReturnWindowKeys target).flatMap fun window =>
    (List.range target).flatMap fun anchor =>
      (List.range horizon).map fun oldCrossingTime =>
        ⟨window, anchor, oldCrossingTime⟩

theorem mem_terminalReturnInstalledWindowKeys_iff
    {target horizon : Nat} {key : TerminalReturnInstalledWindowKey} :
    key ∈ terminalReturnInstalledWindowKeys target horizon ↔
      key.window ∈ terminalReturnWindowKeys target ∧
        key.anchor < target ∧ key.oldCrossingTime < horizon := by
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with
      ⟨window, hwindow, hrest⟩
    rcases List.mem_flatMap.mp hrest with
      ⟨anchor, hanchor, hcursor⟩
    rcases List.mem_map.mp hcursor with
      ⟨oldCrossingTime, holdCrossing, hkey⟩
    have hwindowEq : window = key.window :=
      congrArg TerminalReturnInstalledWindowKey.window hkey
    have hanchorEq : anchor = key.anchor :=
      congrArg TerminalReturnInstalledWindowKey.anchor hkey
    have hcursorEq : oldCrossingTime = key.oldCrossingTime :=
      congrArg TerminalReturnInstalledWindowKey.oldCrossingTime hkey
    subst window
    subst anchor
    subst oldCrossingTime
    exact ⟨hwindow, List.mem_range.mp hanchor,
      List.mem_range.mp holdCrossing⟩
  · rintro ⟨hwindow, hanchor, holdCrossing⟩
    apply List.mem_flatMap.mpr
    refine ⟨key.window, hwindow, ?_⟩
    apply List.mem_flatMap.mpr
    exact ⟨key.anchor, List.mem_range.mpr hanchor,
      List.mem_map.mpr
        ⟨key.oldCrossingTime, List.mem_range.mpr holdCrossing, rfl⟩⟩

/-- Full installed key extracted from one finite terminal certificate. -/
def TerminalFiniteReturnWindowCertificate.installedWindowKey
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (_finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    TerminalReturnInstalledWindowKey :=
  ⟨⟨source.returnTime, terminalEndpoint⟩, parent.anchorParent,
    source.oldCrossingTime⟩

theorem TerminalFiniteReturnWindowCertificate.installedWindowKey_mem
    {target horizon start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (horizon_eq : parent.horizon = horizon) :
    finite.installedWindowKey ∈
      terminalReturnInstalledWindowKeys target horizon := by
  apply mem_terminalReturnInstalledWindowKeys_iff.mpr
  have hcrossing := source.windowSnapshot_crossing_below_horizon
  rw [horizon_eq] at hcrossing
  exact ⟨finite.key_mem, source.windowSnapshot_anchor_below, hcrossing⟩

/-- Remaining full identities at one fixed installed horizon. -/
structure TerminalReturnInstalledWindowSelectionState
    (target horizon : Nat) : Type where
  remaining : List TerminalReturnInstalledWindowKey
  remaining_candidates : ∀ key, key ∈ remaining →
    key ∈ terminalReturnInstalledWindowKeys target horizon

def initialTerminalReturnInstalledWindowSelectionState
    (target horizon : Nat) :
    TerminalReturnInstalledWindowSelectionState target horizon := {
  remaining := terminalReturnInstalledWindowKeys target horizon
  remaining_candidates := fun _ h => h
}

def TerminalReturnInstalledWindowSelectionProgress {target horizon : Nat}
    (child parent :
      TerminalReturnInstalledWindowSelectionState target horizon) : Prop :=
  child.remaining.length < parent.remaining.length

theorem terminalReturnInstalledWindowSelectionProgress_wellFounded
    (target horizon : Nat) :
    WellFounded
      (@TerminalReturnInstalledWindowSelectionProgress target horizon) := by
  apply WellFounded.intro
  intro state
  generalize hrank : state.remaining.length = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing state with
  | intro rank _ ih =>
      apply Acc.intro state
      intro child hchild
      have hrelation : child.remaining.length < rank := by
        simpa [TerminalReturnInstalledWindowSelectionProgress, hrank] using
          hchild
      exact ih child.remaining.length hrelation child rfl

def TerminalReturnInstalledWindowSelectionState.erase
    {target horizon : Nat}
    (state : TerminalReturnInstalledWindowSelectionState target horizon)
    (key : TerminalReturnInstalledWindowKey) :
    TerminalReturnInstalledWindowSelectionState target horizon := {
  remaining := state.remaining.erase key
  remaining_candidates := by
    intro candidate hmem
    exact state.remaining_candidates candidate (List.mem_of_mem_erase hmem)
}

/-- A fresh full identity consumes one finite state entry. -/
structure TerminalReturnInstalledWindowFreshSelectionCertificate
    (target horizon : Nat) (key : TerminalReturnInstalledWindowKey)
    (state : TerminalReturnInstalledWindowSelectionState target horizon) :
    Type where
  candidate_membership :
    key ∈ terminalReturnInstalledWindowKeys target horizon
  remaining_membership : key ∈ state.remaining
  next_state : TerminalReturnInstalledWindowSelectionState target horizon
  next_state_eq : next_state = state.erase key
  progress : TerminalReturnInstalledWindowSelectionProgress next_state state

/-- Fresh full snapshot or exact reuse of all finite installed coordinates. -/
inductive TerminalReturnInstalledWindowSelectionOutcome
    (target horizon : Nat) (key : TerminalReturnInstalledWindowKey)
    (state : TerminalReturnInstalledWindowSelectionState target horizon) : Type
  | fresh
      (certificate : TerminalReturnInstalledWindowFreshSelectionCertificate
        target horizon key state) :
      TerminalReturnInstalledWindowSelectionOutcome target horizon key state
  | exact_revisit
      (candidate_membership :
        key ∈ terminalReturnInstalledWindowKeys target horizon)
      (not_remaining : key ∉ state.remaining) :
      TerminalReturnInstalledWindowSelectionOutcome target horizon key state

noncomputable def TerminalReturnInstalledWindowSelectionState.select
    {target horizon : Nat}
    (state : TerminalReturnInstalledWindowSelectionState target horizon)
    (key : TerminalReturnInstalledWindowKey)
    (hcandidate : key ∈ terminalReturnInstalledWindowKeys target horizon) :
    TerminalReturnInstalledWindowSelectionOutcome target horizon key state := by
  by_cases hremaining : key ∈ state.remaining
  · have hlength :
        (state.remaining.erase key).length < state.remaining.length := by
      rw [List.length_erase_of_mem hremaining]
      have hpositive := List.length_pos_of_mem hremaining
      omega
    exact .fresh {
      candidate_membership := hcandidate
      remaining_membership := hremaining
      next_state := state.erase key
      next_state_eq := rfl
      progress := hlength
    }
  · exact .exact_revisit hcandidate hremaining

/-- A finite occurrence at the state's fixed parent horizon invokes the full
installed-window selection directly. -/
noncomputable def TerminalFiniteReturnWindowCertificate.installedWindowSelection
    {target horizon start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (horizon_eq : parent.horizon = horizon)
    (state : TerminalReturnInstalledWindowSelectionState target horizon) :
    TerminalReturnInstalledWindowSelectionOutcome target horizon
      finite.installedWindowKey state :=
  state.select finite.installedWindowKey
    (finite.installedWindowKey_mem horizon_eq)

end

end Recaman
