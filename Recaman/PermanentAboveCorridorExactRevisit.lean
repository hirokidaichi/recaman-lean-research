import Recaman.PermanentAboveCorridorInstalledWindowSelection

namespace Recaman

noncomputable section

/-! # Historical provenance inside an exact installed-window revisit

The ready-crossing invariant fixes the numeric parent shape: phase is normal
and local measure equals the anchor.  Hence equal horizon and anchor already
mean equal `PhaseSearchNode`s.

The remaining choices made while constructing a discharge are the original
downcross and the historical minimum certificate.  All relevant numeric data
are nevertheless bounded by the fixed parent horizon.  This module first
classifies different downcross endpoints by strict history progress, then
extends the finite installed-window key with the endpoint, historical first
time, and minimum value.  A fresh extended key consumes a finite selection
entry; only exact equality of all these numeric provenance fields remains.
-/

/-- A certified permanent-tail crossing parent has no hidden phase/local
freedom. -/
theorem PermanentTailDischargeReturnCertificate.parent_node_shape
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    parent = ⟨parent.horizon, parent.anchorParent, .normal,
      parent.anchorParent⟩ := by
  rcases source.combined.crossing.ready_crossing.crossing with
    ⟨oldAnchor, crossingTime, quotient, remainder, certificate⟩
  have hanchor : parent.anchorParent = a crossingTime := by
    simpa using congrArg PhaseSearchNode.anchorParent certificate.node_eq
  simpa [hanchor] using certificate.node_eq

theorem PermanentTailDischargeReturnCertificate.parent_eq_of_horizon_anchor
    {target start₁ start₂ : Nat}
    {parent₁ parent₂ : PhaseSearchNode}
    (left : PermanentTailDischargeReturnCertificate target start₁ parent₁)
    (right : PermanentTailDischargeReturnCertificate target start₂ parent₂)
    (horizon_eq : parent₁.horizon = parent₂.horizon)
    (anchor_eq : parent₁.anchorParent = parent₂.anchorParent) :
    parent₁ = parent₂ := by
  rw [left.parent_node_shape, right.parent_node_shape, horizon_eq, anchor_eq]

theorem PermanentTailDischargeReturnCertificate.down_endpoint_before_horizon
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    source.downTime + 1 < parent.horizon :=
  Nat.lt_trans
    (Nat.lt_of_lt_of_le source.endpoint_before_tail source.tailStart_le_start)
    source.combined.crossing.tail_strictly_before_horizon

theorem PermanentTailDischargeReturnCertificate.historical_first_before_horizon
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    source.historicalFirstTime < parent.horizon :=
  Nat.lt_trans
    (Nat.lt_of_lt_of_le source.historical_minimum.firstTime_before_tail
      source.tailStart_le_start)
    source.combined.crossing.tail_strictly_before_horizon

theorem PermanentTailDischargeReturnCertificate.historical_minimum_value_le_upperTri_horizon
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    a source.historicalMinimumTime ≤ upperTri parent.horizon := by
  have hminimum := source.historical_minimum.minimum.minimal source.tailStart
    (Nat.le_refl _)
  have horbit := a_le_upperTri source.tailStart
  have hstartLe : source.tailStart ≤ parent.horizon :=
    Nat.le_trans source.tailStart_le_start
      (Nat.le_of_lt source.combined.crossing.tail_strictly_before_horizon)
  have htri := upperTri_mono hstartLe
  omega

/-- Original downcross endpoints either consume history in iteration
direction, consume it in reverse, or are the same absolute time. -/
inductive TerminalExactWindowDownEndpointComparison
    {target start₁ start₂ : Nat} {parent₁ parent₂ : PhaseSearchNode}
    (current : PermanentTailDischargeReturnCertificate target start₁ parent₁)
    (stored : PermanentTailDischargeReturnCertificate target start₂ parent₂) :
    Prop
  | current_progress
      (progress : TerminalChronologyHistoryProgress target
        (current.downTime + 1) (stored.downTime + 1)) :
      TerminalExactWindowDownEndpointComparison current stored
  | stored_progress
      (progress : TerminalChronologyHistoryProgress target
        (stored.downTime + 1) (current.downTime + 1)) :
      TerminalExactWindowDownEndpointComparison current stored
  | same_endpoint
      (time_eq : current.downTime + 1 = stored.downTime + 1) :
      TerminalExactWindowDownEndpointComparison current stored

theorem terminalExactWindowDownEndpointComparison_total
    {target start₁ start₂ : Nat} {parent₁ parent₂ : PhaseSearchNode}
    (current : PermanentTailDischargeReturnCertificate target start₁ parent₁)
    (stored : PermanentTailDischargeReturnCertificate target start₂ parent₂) :
    TerminalExactWindowDownEndpointComparison current stored := by
  by_cases hcurrent : stored.downTime + 1 < current.downTime + 1
  · exact .current_progress
      (missingBelowCount_strict_of_firstAt
        current.downcross.endpoint_below hcurrent current.endpoint_first)
  · by_cases hstored : current.downTime + 1 < stored.downTime + 1
    · exact .stored_progress
        (missingBelowCount_strict_of_firstAt
          stored.downcross.endpoint_below hstored stored.endpoint_first)
    · exact .same_endpoint (by omega)

/-- Finite numeric provenance after fixing the installed window. -/
structure TerminalExactInstalledHistoryKey : Type where
  installed : TerminalReturnInstalledWindowKey
  downEndpoint : Nat
  historicalFirstTime : Nat
  historicalMinimumValue : Nat
deriving Repr, DecidableEq

def terminalExactInstalledHistoryKeys
    (target horizon : Nat) : List TerminalExactInstalledHistoryKey :=
  (terminalReturnInstalledWindowKeys target horizon).flatMap fun installed =>
    (List.range horizon).flatMap fun downEndpoint =>
      (List.range horizon).flatMap fun historicalFirstTime =>
        (List.range (upperTri horizon + 1)).map fun historicalMinimumValue =>
          ⟨installed, downEndpoint, historicalFirstTime,
            historicalMinimumValue⟩

theorem mem_terminalExactInstalledHistoryKeys_iff
    {target horizon : Nat} {key : TerminalExactInstalledHistoryKey} :
    key ∈ terminalExactInstalledHistoryKeys target horizon ↔
      key.installed ∈ terminalReturnInstalledWindowKeys target horizon ∧
        key.downEndpoint < horizon ∧
        key.historicalFirstTime < horizon ∧
        key.historicalMinimumValue ≤ upperTri horizon := by
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with
      ⟨installed, hinstalled, hdownRest⟩
    rcases List.mem_flatMap.mp hdownRest with
      ⟨downEndpoint, hdown, hfirstRest⟩
    rcases List.mem_flatMap.mp hfirstRest with
      ⟨historicalFirstTime, hfirst, hminimumRest⟩
    rcases List.mem_map.mp hminimumRest with
      ⟨historicalMinimumValue, hminimum, hkey⟩
    have hinstalledEq : installed = key.installed :=
      congrArg TerminalExactInstalledHistoryKey.installed hkey
    have hdownEq : downEndpoint = key.downEndpoint :=
      congrArg TerminalExactInstalledHistoryKey.downEndpoint hkey
    have hfirstEq : historicalFirstTime = key.historicalFirstTime :=
      congrArg TerminalExactInstalledHistoryKey.historicalFirstTime hkey
    have hminimumEq : historicalMinimumValue =
        key.historicalMinimumValue :=
      congrArg TerminalExactInstalledHistoryKey.historicalMinimumValue hkey
    subst installed
    subst downEndpoint
    subst historicalFirstTime
    subst historicalMinimumValue
    exact ⟨hinstalled, List.mem_range.mp hdown,
      List.mem_range.mp hfirst, by
        have := List.mem_range.mp hminimum
        omega⟩
  · rintro ⟨hinstalled, hdown, hfirst, hminimum⟩
    apply List.mem_flatMap.mpr
    refine ⟨key.installed, hinstalled, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨key.downEndpoint, List.mem_range.mpr hdown, ?_⟩
    apply List.mem_flatMap.mpr
    exact ⟨key.historicalFirstTime, List.mem_range.mpr hfirst,
      List.mem_map.mpr
        ⟨key.historicalMinimumValue, List.mem_range.mpr (by omega), rfl⟩⟩

def TerminalFiniteReturnWindowCertificate.exactHistoryKey
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    TerminalExactInstalledHistoryKey :=
  ⟨finite.installedWindowKey, source.downTime + 1,
    source.historicalFirstTime, a source.historicalMinimumTime⟩

theorem TerminalFiniteReturnWindowCertificate.exactHistoryKey_mem
    {target horizon start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (horizon_eq : parent.horizon = horizon) :
    finite.exactHistoryKey ∈
      terminalExactInstalledHistoryKeys target horizon := by
  apply mem_terminalExactInstalledHistoryKeys_iff.mpr
  have hdown := source.down_endpoint_before_horizon
  have hfirst := source.historical_first_before_horizon
  have hminimum := source.historical_minimum_value_le_upperTri_horizon
  rw [horizon_eq] at hdown hfirst hminimum
  exact ⟨finite.installedWindowKey_mem horizon_eq, hdown, hfirst, hminimum⟩

/-- Remaining exact historical-provenance keys at a fixed horizon. -/
structure TerminalExactInstalledHistorySelectionState
    (target horizon : Nat) : Type where
  remaining : List TerminalExactInstalledHistoryKey
  remaining_candidates : ∀ key, key ∈ remaining →
    key ∈ terminalExactInstalledHistoryKeys target horizon

def initialTerminalExactInstalledHistorySelectionState
    (target horizon : Nat) :
    TerminalExactInstalledHistorySelectionState target horizon := {
  remaining := terminalExactInstalledHistoryKeys target horizon
  remaining_candidates := fun _ h => h
}

def TerminalExactInstalledHistorySelectionProgress {target horizon : Nat}
    (child parent :
      TerminalExactInstalledHistorySelectionState target horizon) : Prop :=
  child.remaining.length < parent.remaining.length

theorem terminalExactInstalledHistorySelectionProgress_wellFounded
    (target horizon : Nat) :
    WellFounded
      (@TerminalExactInstalledHistorySelectionProgress target horizon) := by
  apply WellFounded.intro
  intro state
  generalize hrank : state.remaining.length = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing state with
  | intro rank _ ih =>
      apply Acc.intro state
      intro child hchild
      have hrelation : child.remaining.length < rank := by
        simpa [TerminalExactInstalledHistorySelectionProgress, hrank] using
          hchild
      exact ih child.remaining.length hrelation child rfl

def TerminalExactInstalledHistorySelectionState.erase
    {target horizon : Nat}
    (state : TerminalExactInstalledHistorySelectionState target horizon)
    (key : TerminalExactInstalledHistoryKey) :
    TerminalExactInstalledHistorySelectionState target horizon := {
  remaining := state.remaining.erase key
  remaining_candidates := by
    intro candidate hmem
    exact state.remaining_candidates candidate (List.mem_of_mem_erase hmem)
}

structure TerminalExactInstalledHistoryFreshSelectionCertificate
    (target horizon : Nat) (key : TerminalExactInstalledHistoryKey)
    (state : TerminalExactInstalledHistorySelectionState target horizon) :
    Type where
  candidate_membership :
    key ∈ terminalExactInstalledHistoryKeys target horizon
  remaining_membership : key ∈ state.remaining
  next_state : TerminalExactInstalledHistorySelectionState target horizon
  next_state_eq : next_state = state.erase key
  progress : TerminalExactInstalledHistorySelectionProgress next_state state

inductive TerminalExactInstalledHistorySelectionOutcome
    (target horizon : Nat) (key : TerminalExactInstalledHistoryKey)
    (state : TerminalExactInstalledHistorySelectionState target horizon) : Type
  | fresh
      (certificate : TerminalExactInstalledHistoryFreshSelectionCertificate
        target horizon key state) :
      TerminalExactInstalledHistorySelectionOutcome target horizon key state
  | exact_revisit
      (candidate_membership :
        key ∈ terminalExactInstalledHistoryKeys target horizon)
      (not_remaining : key ∉ state.remaining) :
      TerminalExactInstalledHistorySelectionOutcome target horizon key state

noncomputable def TerminalExactInstalledHistorySelectionState.select
    {target horizon : Nat}
    (state : TerminalExactInstalledHistorySelectionState target horizon)
    (key : TerminalExactInstalledHistoryKey)
    (hcandidate : key ∈ terminalExactInstalledHistoryKeys target horizon) :
    TerminalExactInstalledHistorySelectionOutcome target horizon key state := by
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

noncomputable def TerminalFiniteReturnWindowCertificate.exactHistorySelection
    {target horizon start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (horizon_eq : parent.horizon = horizon)
    (state : TerminalExactInstalledHistorySelectionState target horizon) :
    TerminalExactInstalledHistorySelectionOutcome target horizon
      finite.exactHistoryKey state :=
  state.select finite.exactHistoryKey (finite.exactHistoryKey_mem horizon_eq)

end

end Recaman
