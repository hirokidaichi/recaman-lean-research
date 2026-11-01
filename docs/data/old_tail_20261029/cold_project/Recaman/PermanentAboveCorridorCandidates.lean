import Recaman.PermanentAboveCorridorResidual

namespace Recaman

noncomputable section

/-! # Finite return candidates of the insufficient-value residual

The finite all-forced insufficient branch satisfies
`return < target < 2 * (return + 1)`.  Filtering `List.range target` by the
second inequality turns this abstract band into an explicit target-indexed
candidate list.  The enclosing `target - return` rank is well founded and
strictly decreases when a later candidate is selected.
-/

/-- Explicit return clocks compatible with the finite insufficient band. -/
def terminalReturnCandidates (target : Nat) : List Nat :=
  (List.range target).filter fun returnTime =>
    decide (target < 2 * (returnTime + 1))

/-- Membership is exactly the pair of clock-band inequalities. -/
theorem mem_terminalReturnCandidates_iff
    {target returnTime : Nat} :
    returnTime ∈ terminalReturnCandidates target ↔
      returnTime < target ∧ target < 2 * (returnTime + 1) := by
  simp [terminalReturnCandidates]

/-- Every finite clock-band certificate belongs to the explicit list. -/
theorem TerminalFiniteClockBandCertificate.mem_terminalReturnCandidates
    {target returnTime : Nat}
    (h : TerminalFiniteClockBandCertificate target returnTime) :
    returnTime ∈ terminalReturnCandidates target := by
  exact mem_terminalReturnCandidates_iff.mpr
    ⟨h.return_before_target, h.target_lt_twice_clock⟩

/-- The explicit candidate list has at most `target` elements. -/
theorem terminalReturnCandidates_length_le (target : Nat) :
    (terminalReturnCandidates target).length ≤ target := by
  have hlength := List.length_filter_le
    (fun returnTime : Nat => decide (target < 2 * (returnTime + 1)))
    (List.range target)
  simpa [terminalReturnCandidates] using hlength

/-- Remaining target-clock envelope after choosing a return candidate. -/
def terminalReturnCandidateRank (target returnTime : Nat) : Nat :=
  target - returnTime

def TerminalReturnCandidateProgress (target : Nat)
    (childReturn parentReturn : Nat) : Prop :=
  terminalReturnCandidateRank target childReturn <
    terminalReturnCandidateRank target parentReturn

/-- The candidate-envelope rank is well founded. -/
theorem terminalReturnCandidateProgress_wellFounded (target : Nat) :
    WellFounded (TerminalReturnCandidateProgress target) := by
  apply WellFounded.intro
  intro returnTime
  generalize hrank : terminalReturnCandidateRank target returnTime = rank
  have hacc := Nat.lt_wfRel.wf.apply rank
  induction hacc generalizing returnTime with
  | intro rank _ ih =>
      apply Acc.intro returnTime
      intro childReturn hchild
      have hrelation :
          terminalReturnCandidateRank target childReturn < rank := by
        simpa [TerminalReturnCandidateProgress, hrank] using hchild
      exact ih (terminalReturnCandidateRank target childReturn) hrelation
        childReturn rfl

/-- Moving to a later clock inside the candidate list strictly lowers the
remaining target-clock envelope. -/
theorem terminalReturnCandidateProgress_of_later
    {target parentReturn childReturn : Nat}
    (hparent : parentReturn ∈ terminalReturnCandidates target)
    (hchild : childReturn ∈ terminalReturnCandidates target)
    (hlater : parentReturn < childReturn) :
    TerminalReturnCandidateProgress target childReturn parentReturn := by
  have hparentBound := (mem_terminalReturnCandidates_iff.mp hparent).1
  have hchildBound := (mem_terminalReturnCandidates_iff.mp hchild).1
  unfold TerminalReturnCandidateProgress terminalReturnCandidateRank
  omega

/-- The three genuine outer residuals left after the finite-clock branch is
separated. -/
inductive PermanentTailTerminalNonClockResidual
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | immediate_insufficient
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime) :
      PermanentTailTerminalNonClockResidual source
  | immediate_historical
      (candidate firstTime : Nat)
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (firstTime_lt_endpoint : firstTime < source.downTime + 1) :
      PermanentTailTerminalNonClockResidual source
  | finite_outer_blocker
      (terminalEndpoint candidate firstTime : Nat)
      (origin_le : source.downTime + 1 ≤ terminalEndpoint)
      (window : TerminalAllForcedCrossingWindow target terminalEndpoint
        source.returnTime)
      (blocker : TerminalHistoricalBlockerCertificate target
        source.returnTime candidate firstTime)
      (firstTime_le_endpoint : firstTime ≤ terminalEndpoint) :
      PermanentTailTerminalNonClockResidual source

/-- A master outer residual is either located in the explicit finite return
list or belongs to one of the three non-clock residual constructors. -/
theorem PermanentTailTerminalOuterResidual.finiteCandidate_or_nonClockResidual
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    (h : PermanentTailTerminalOuterResidual source) :
    source.returnTime ∈ terminalReturnCandidates target ∨
      PermanentTailTerminalNonClockResidual source := by
  cases h with
  | immediate_insufficient valley insufficient =>
      exact Or.inr (.immediate_insufficient valley insufficient)
  | immediate_historical candidate firstTime valley blocker hfirst =>
      exact Or.inr (.immediate_historical candidate firstTime valley blocker
        hfirst)
  | finite_insufficient terminalEndpoint origin_le window insufficient band =>
      exact Or.inl band.mem_terminalReturnCandidates
  | finite_outer_blocker terminalEndpoint candidate firstTime origin_le
      window blocker hfirst =>
      exact Or.inr (.finite_outer_blocker terminalEndpoint candidate firstTime
        origin_le window blocker hfirst)

end

end Recaman
