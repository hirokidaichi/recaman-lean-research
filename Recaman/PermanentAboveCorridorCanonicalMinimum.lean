import Recaman.PermanentAboveCorridorExactRevisit

namespace Recaman

noncomputable section

/-! # Canonical tail-minimum provenance for exact revisits

The witness time of a tail minimum is not bounded by the stored history
horizon.  It should not be enumerated.  Instead, for a fixed tail start and
minimum value, choose the first occurrence at or after that start.  This
relative first occurrence exists below every supplied witness and is unique.

The two start cursors themselves are historical: both lie strictly before
the fixed parent horizon.  Adding them to the finite exact-history key leaves
only the canonical minimum-time identity, which follows from uniqueness and
does not require another unbounded selection rank.
-/

/-- First occurrence of a value relative to a lower time bound. -/
structure FirstAtOrAfter
    (seq : Nat → Nat) (value start time : Nat) : Prop where
  start_le : start ≤ time
  value_eq : seq time = value
  earliest : ∀ candidate, start ≤ candidate → seq candidate = value →
    time ≤ candidate

/-- A relative first occurrence exists no later than any supplied witness. -/
theorem exists_firstAtOrAfter_bounded
    {seq : Nat → Nat} {value start witness : Nat}
    (hstart : start ≤ witness) (hvalue : seq witness = value) :
    ∃ time, FirstAtOrAfter seq value start time ∧ time ≤ witness := by
  have hwitnessEq : start + (witness - start) = witness := by omega
  have hshifted : ∃ offset, seq (start + offset) = value :=
    ⟨witness - start, by simpa [hwitnessEq] using hvalue⟩
  rcases exists_firstAt hshifted with ⟨offset, hfirst⟩
  let time := start + offset
  have htimeValue : seq time = value := by
    simpa [time] using hfirst.1
  have hearliest : ∀ candidate, start ≤ candidate →
      seq candidate = value → time ≤ candidate := by
    intro candidate hcandidate hcandidateValue
    apply Nat.le_of_not_gt
    intro hcandidateBefore
    have hoffsetBefore : candidate - start < offset := by
      dsimp [time] at hcandidateBefore
      omega
    have hcandidateEq : start + (candidate - start) = candidate := by omega
    have hshiftedCandidate :
        seq (start + (candidate - start)) = value := by
      simpa [hcandidateEq] using hcandidateValue
    exact hfirst.2 (candidate - start) hoffsetBefore hshiftedCandidate
  refine ⟨time, ⟨Nat.le_add_right start offset, htimeValue, hearliest⟩, ?_⟩
  exact hearliest witness hstart hvalue

theorem FirstAtOrAfter.unique
    {seq : Nat → Nat} {value start left right : Nat}
    (hleft : FirstAtOrAfter seq value start left)
    (hright : FirstAtOrAfter seq value start right) :
    left = right :=
  Nat.le_antisymm
    (hleft.earliest right hright.start_le hright.value_eq)
    (hright.earliest left hleft.start_le hleft.value_eq)

/-- Canonicalized occurrence of the historical tail minimum value. -/
structure CanonicalHistoricalMinimumOccurrence
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Type where
  time : Nat
  first_relative : FirstAtOrAfter a (a source.historicalMinimumTime)
    source.tailStart time
  no_later_than_source : time ≤ source.historicalMinimumTime

theorem PermanentTailDischargeReturnCertificate.exists_canonicalHistoricalMinimum
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Nonempty (CanonicalHistoricalMinimumOccurrence source) := by
  rcases exists_firstAtOrAfter_bounded
      source.historical_minimum.minimum.start_le_time rfl with
    ⟨time, hfirst, htime⟩
  exact ⟨⟨time, hfirst, htime⟩⟩

/-- Same relative tail start and minimum value force the same canonical
minimum occurrence, even when the original witness times differ. -/
theorem CanonicalHistoricalMinimumOccurrence.time_eq_of_same_tail_value
    {target start₁ start₂ : Nat} {parent₁ parent₂ : PhaseSearchNode}
    {left : PermanentTailDischargeReturnCertificate target start₁ parent₁}
    {right : PermanentTailDischargeReturnCertificate target start₂ parent₂}
    (leftCanonical : CanonicalHistoricalMinimumOccurrence left)
    (rightCanonical : CanonicalHistoricalMinimumOccurrence right)
    (tail_eq : left.tailStart = right.tailStart)
    (value_eq : a left.historicalMinimumTime =
      a right.historicalMinimumTime) :
    leftCanonical.time = rightCanonical.time := by
  have hleft : FirstAtOrAfter a (a right.historicalMinimumTime)
      right.tailStart leftCanonical.time := by
    simpa [tail_eq, value_eq] using leftCanonical.first_relative
  exact hleft.unique rightCanonical.first_relative

theorem PermanentTailDischargeReturnCertificate.start_before_parent_horizon
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    start < parent.horizon :=
  source.combined.crossing.tail_strictly_before_horizon

theorem PermanentTailDischargeReturnCertificate.tail_start_before_parent_horizon
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    source.tailStart < parent.horizon :=
  Nat.lt_of_le_of_lt source.tailStart_le_start
    source.start_before_parent_horizon

/-- Exact finite provenance including both permanent-tail start cursors. -/
structure TerminalCanonicalTailHistoryKey : Type where
  history : TerminalExactInstalledHistoryKey
  permanentStart : Nat
  historicalTailStart : Nat
deriving Repr, DecidableEq

def terminalCanonicalTailHistoryKeys
    (target horizon : Nat) : List TerminalCanonicalTailHistoryKey :=
  (terminalExactInstalledHistoryKeys target horizon).flatMap fun history =>
    (List.range horizon).flatMap fun permanentStart =>
      (List.range horizon).map fun historicalTailStart =>
        ⟨history, permanentStart, historicalTailStart⟩

theorem mem_terminalCanonicalTailHistoryKeys_iff
    {target horizon : Nat} {key : TerminalCanonicalTailHistoryKey} :
    key ∈ terminalCanonicalTailHistoryKeys target horizon ↔
      key.history ∈ terminalExactInstalledHistoryKeys target horizon ∧
        key.permanentStart < horizon ∧
        key.historicalTailStart < horizon := by
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with
      ⟨history, hhistory, hstartRest⟩
    rcases List.mem_flatMap.mp hstartRest with
      ⟨permanentStart, hstart, htailRest⟩
    rcases List.mem_map.mp htailRest with
      ⟨historicalTailStart, htail, hkey⟩
    have hhistoryEq : history = key.history :=
      congrArg TerminalCanonicalTailHistoryKey.history hkey
    have hstartEq : permanentStart = key.permanentStart :=
      congrArg TerminalCanonicalTailHistoryKey.permanentStart hkey
    have htailEq : historicalTailStart = key.historicalTailStart :=
      congrArg TerminalCanonicalTailHistoryKey.historicalTailStart hkey
    subst history
    subst permanentStart
    subst historicalTailStart
    exact ⟨hhistory, List.mem_range.mp hstart, List.mem_range.mp htail⟩
  · rintro ⟨hhistory, hstart, htail⟩
    apply List.mem_flatMap.mpr
    refine ⟨key.history, hhistory, ?_⟩
    apply List.mem_flatMap.mpr
    exact ⟨key.permanentStart, List.mem_range.mpr hstart,
      List.mem_map.mpr
        ⟨key.historicalTailStart, List.mem_range.mpr htail, rfl⟩⟩

def TerminalFiniteReturnWindowCertificate.canonicalTailHistoryKey
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    TerminalCanonicalTailHistoryKey :=
  ⟨finite.exactHistoryKey, start, source.tailStart⟩

theorem TerminalFiniteReturnWindowCertificate.canonicalTailHistoryKey_mem
    {target horizon start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (horizon_eq : parent.horizon = horizon) :
    finite.canonicalTailHistoryKey ∈
      terminalCanonicalTailHistoryKeys target horizon := by
  apply mem_terminalCanonicalTailHistoryKeys_iff.mpr
  have hstart := source.start_before_parent_horizon
  have htail := source.tail_start_before_parent_horizon
  rw [horizon_eq] at hstart htail
  exact ⟨finite.exactHistoryKey_mem horizon_eq, hstart, htail⟩

structure TerminalCanonicalTailHistorySelectionState
    (target horizon : Nat) : Type where
  remaining : List TerminalCanonicalTailHistoryKey
  remaining_candidates : ∀ key, key ∈ remaining →
    key ∈ terminalCanonicalTailHistoryKeys target horizon

def initialTerminalCanonicalTailHistorySelectionState
    (target horizon : Nat) :
    TerminalCanonicalTailHistorySelectionState target horizon := {
  remaining := terminalCanonicalTailHistoryKeys target horizon
  remaining_candidates := fun _ h => h
}

def TerminalCanonicalTailHistorySelectionProgress {target horizon : Nat}
    (child parent :
      TerminalCanonicalTailHistorySelectionState target horizon) : Prop :=
  child.remaining.length < parent.remaining.length

theorem terminalCanonicalTailHistorySelectionProgress_wellFounded
    (target horizon : Nat) :
    WellFounded
      (@TerminalCanonicalTailHistorySelectionProgress target horizon) := by
  apply WellFounded.intro
  intro state
  generalize hrank : state.remaining.length = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing state with
  | intro rank _ ih =>
      apply Acc.intro state
      intro child hchild
      have hrelation : child.remaining.length < rank := by
        simpa [TerminalCanonicalTailHistorySelectionProgress, hrank] using
          hchild
      exact ih child.remaining.length hrelation child rfl

def TerminalCanonicalTailHistorySelectionState.erase
    {target horizon : Nat}
    (state : TerminalCanonicalTailHistorySelectionState target horizon)
    (key : TerminalCanonicalTailHistoryKey) :
    TerminalCanonicalTailHistorySelectionState target horizon := {
  remaining := state.remaining.erase key
  remaining_candidates := by
    intro candidate hmem
    exact state.remaining_candidates candidate (List.mem_of_mem_erase hmem)
}

structure TerminalCanonicalTailHistoryFreshSelectionCertificate
    (target horizon : Nat) (key : TerminalCanonicalTailHistoryKey)
    (state : TerminalCanonicalTailHistorySelectionState target horizon) :
    Type where
  candidate_membership :
    key ∈ terminalCanonicalTailHistoryKeys target horizon
  remaining_membership : key ∈ state.remaining
  next_state : TerminalCanonicalTailHistorySelectionState target horizon
  next_state_eq : next_state = state.erase key
  progress : TerminalCanonicalTailHistorySelectionProgress next_state state

inductive TerminalCanonicalTailHistorySelectionOutcome
    (target horizon : Nat) (key : TerminalCanonicalTailHistoryKey)
    (state : TerminalCanonicalTailHistorySelectionState target horizon) : Type
  | fresh
      (certificate : TerminalCanonicalTailHistoryFreshSelectionCertificate
        target horizon key state) :
      TerminalCanonicalTailHistorySelectionOutcome target horizon key state
  | exact_revisit
      (candidate_membership :
        key ∈ terminalCanonicalTailHistoryKeys target horizon)
      (not_remaining : key ∉ state.remaining) :
      TerminalCanonicalTailHistorySelectionOutcome target horizon key state

noncomputable def TerminalCanonicalTailHistorySelectionState.select
    {target horizon : Nat}
    (state : TerminalCanonicalTailHistorySelectionState target horizon)
    (key : TerminalCanonicalTailHistoryKey)
    (hcandidate : key ∈ terminalCanonicalTailHistoryKeys target horizon) :
    TerminalCanonicalTailHistorySelectionOutcome target horizon key state := by
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

noncomputable def TerminalFiniteReturnWindowCertificate.canonicalTailHistorySelection
    {target horizon start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint)
    (horizon_eq : parent.horizon = horizon)
    (state : TerminalCanonicalTailHistorySelectionState target horizon) :
    TerminalCanonicalTailHistorySelectionOutcome target horizon
      finite.canonicalTailHistoryKey state :=
  state.select finite.canonicalTailHistoryKey
    (finite.canonicalTailHistoryKey_mem horizon_eq)

end

end Recaman
