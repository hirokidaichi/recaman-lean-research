import Recaman.PermanentAboveCorridorBlockerGeneration

namespace Recaman

noncomputable section

/-! # Semantic adapter for a terminal blocker's predecessor

The blocker landing is below the target, but its generating transition has a
strictly earlier predecessor.  This module packages that predecessor with its
first-occurrence provenance and classifies the exact semantic information
available there.

An at-or-above-target predecessor becomes a negative normal invariant exactly
when its clock is target-ready and its potential is negative.  The two failed
conditions are returned explicitly.  A below-target predecessor instead
retains a future weak crossing to the canonical discharge return.  Its orbit
coordinates are available at positive time; time zero is recorded as the
unique coordinate-free boundary.
-/

/-- Generation-independent provenance shared by the subtraction and addition
predecessors of a terminal historical blocker. -/
structure TerminalBlockerPredecessorCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime)
    (predecessor predecessorFirstTime : Nat) : Prop where
  predecessor_eq : a (firstTime - 1) = predecessor
  predecessor_first : FirstAt a predecessor predecessorFirstTime
  predecessorFirstTime_lt : predecessorFirstTime < firstTime
  target_position : predecessor < target ∨ target ≤ predecessor
  generation : TerminalHistoricalBlockerGeneration historical.blocker

/-- Both generation modes expose the same earlier predecessor interface. -/
theorem TerminalOuterHistoricalBlockerCertificate.exists_predecessorCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (h : TerminalOuterHistoricalBlockerCertificate source freshEndpoint
      candidate firstTime) :
    ∃ predecessor predecessorFirstTime,
      TerminalBlockerPredecessorCertificate h predecessor
        predecessorFirstTime := by
  have hgeneration := h.blocker.generation
  cases hgeneration with
  | legal_subtraction predecessor predecessorFirstTime legal predecessor_eq
      predecessor_first predecessorFirstTime_lt candidate_add_clock_eq
      candidate_fresh_before candidate_lt_predecessor
      predecessor_target_position =>
      exact ⟨predecessor, predecessorFirstTime, {
        predecessor_eq := predecessor_eq
        predecessor_first := predecessor_first
        predecessorFirstTime_lt := predecessorFirstTime_lt
        target_position := predecessor_target_position
        generation := h.blocker.generation
      }⟩
  | forced_addition predecessorFirstTime forced candidate_eq_add
      predecessor_first predecessorFirstTime_lt predecessor_lt_candidate
      predecessor_below_target clock_below_target forced_reason =>
      exact ⟨a (firstTime - 1), predecessorFirstTime, {
        predecessor_eq := rfl
        predecessor_first := predecessor_first
        predecessorFirstTime_lt := predecessorFirstTime_lt
        target_position := Or.inl predecessor_below_target
        generation := h.blocker.generation
      }⟩

/-- Minimal semantic domain for a below-target historical predecessor.

The stored future crossing is deliberately weak: a predecessor may lie before
the original discharge endpoint, so the canonical return need not be the first
crossing from this earlier clock. -/
structure BelowTargetHistoricalPredecessorCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    (historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime) : Prop where
  provenance : TerminalBlockerPredecessorCertificate historical predecessor
    predecessorFirstTime
  predecessor_below_target : predecessor < target
  predecessor_time_before_return : firstTime - 1 < source.returnTime
  future_return : WeakUpcrossingStep target (firstTime - 1)
    source.returnTime
  coordinates_or_initial : firstTime - 1 = 0 ∨
    ∃ quotient remainder, CoordinatesAt (firstTime - 1) quotient remainder

/-- A below-target generation predecessor always has the minimal historical
certificate above, including a future canonical-return crossing. -/
theorem TerminalBlockerPredecessorCertificate.toBelowTargetHistorical
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    {historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime}
    (h : TerminalBlockerPredecessorCertificate historical predecessor
      predecessorFirstTime)
    (hbelow : predecessor < target) :
    BelowTargetHistoricalPredecessorCertificate
      (predecessor := predecessor)
      (predecessorFirstTime := predecessorFirstTime) historical := by
  have hbefore : firstTime - 1 < source.returnTime :=
    Nat.lt_of_le_of_lt (Nat.sub_le firstTime 1)
      historical.blocker.firstTime_lt_return
  have hfuture : WeakUpcrossingStep target (firstTime - 1)
      source.returnTime := {
    start_le := Nat.le_of_lt hbefore
    below := source.return_crossing.crossing.below
    endpoint_ge := source.return_crossing.crossing.endpoint_ge
    forced_addition := source.return_crossing.crossing.forced_addition
  }
  have hcoordinates : firstTime - 1 = 0 ∨
      ∃ quotient remainder,
        CoordinatesAt (firstTime - 1) quotient remainder := by
    by_cases hzero : firstTime - 1 = 0
    · exact Or.inl hzero
    · exact Or.inr (exists_coordinatesAt (Nat.zero_lt_of_ne_zero hzero))
  exact {
    provenance := h
    predecessor_below_target := hbelow
    predecessor_time_before_return := hbefore
    future_return := hfuture
    coordinates_or_initial := hcoordinates
  }

/-- Exact missing condition when an above-target predecessor cannot yet be
installed as a negative normal node. -/
structure AboveTargetPredecessorResidual
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime predecessor predecessorFirstTime : Nat}
    (historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime)
    (quotient remainder : Nat) : Prop where
  provenance : TerminalBlockerPredecessorCertificate historical predecessor
    predecessorFirstTime
  target_le_predecessor : target ≤ predecessor
  coordinates : CoordinatesAt (firstTime - 1) quotient remainder
  obstruction : firstTime < target ∨ 0 ≤ potential quotient remainder

/-- Total semantic classification of the generating predecessor. -/
inductive TerminalBlockerPredecessorSemanticOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (historical : TerminalOuterHistoricalBlockerCertificate source
      freshEndpoint candidate firstTime) : Prop
  | normal_ready
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (predecessor_certificate : TerminalBlockerPredecessorCertificate
        historical predecessor predecessorFirstTime)
      (invariant : NormalPhaseInvariantAt target
        ⟨firstTime - 1, predecessor, .normal, a (firstTime - 1)⟩
        (firstTime - 1) quotient remainder) :
      TerminalBlockerPredecessorSemanticOutcome historical
  | above_residual
      (predecessor predecessorFirstTime quotient remainder : Nat)
      (residual : AboveTargetPredecessorResidual
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical quotient
        remainder) :
      TerminalBlockerPredecessorSemanticOutcome historical
  | below_historical
      (predecessor predecessorFirstTime : Nat)
      (certificate : BelowTargetHistoricalPredecessorCertificate
        (predecessor := predecessor)
        (predecessorFirstTime := predecessorFirstTime) historical) :
      TerminalBlockerPredecessorSemanticOutcome historical

/-- Every outer historical blocker is semantically usable in exactly one of
the existing negative-normal domain, an explicit above-target readiness/sign
residual, or the minimal below-target historical domain. -/
theorem TerminalOuterHistoricalBlockerCertificate.predecessorSemanticOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {freshEndpoint candidate firstTime : Nat}
    (h : TerminalOuterHistoricalBlockerCertificate source freshEndpoint
      candidate firstTime) :
    TerminalBlockerPredecessorSemanticOutcome h := by
  rcases h.exists_predecessorCertificate with
    ⟨predecessor, predecessorFirstTime, hpredecessor⟩
  rcases hpredecessor.target_position with hbelow | habove
  · exact .below_historical predecessor predecessorFirstTime
      (hpredecessor.toBelowTargetHistorical hbelow)
  · have htimePositive : 0 < firstTime - 1 := by
      by_cases htimeZero : firstTime - 1 = 0
      · have heq := hpredecessor.predecessor_eq
        have haZero : a 0 = 0 := rfl
        rw [htimeZero, haZero] at heq
        have htargetPositive := source.combined.tail.target_positive
        omega
      · exact Nat.zero_lt_of_ne_zero htimeZero
    rcases exists_coordinatesAt htimePositive with
      ⟨quotient, remainder, hcoordinates⟩
    by_cases hready : target ≤ firstTime
    · by_cases hnegative : potential quotient remainder < 0
      · have hinvariant : NormalPhaseInvariantAt target
            ⟨firstTime - 1, predecessor, .normal, a (firstTime - 1)⟩
            (firstTime - 1) quotient remainder := {
          node_eq := rfl
          time_ready := by
            have hfirstPositive := h.blocker.backtrackCertificate
              |>.firstTime_positive
            omega
          target_le_value := by
            rw [hpredecessor.predecessor_eq]
            exact habove
          value_le_anchor := by
            rw [hpredecessor.predecessor_eq]
            exact Nat.le_refl _
          coordinates := hcoordinates
          negative := hnegative
        }
        exact .normal_ready predecessor predecessorFirstTime quotient
          remainder hpredecessor hinvariant
      · exact .above_residual predecessor predecessorFirstTime quotient
          remainder {
            provenance := hpredecessor
            target_le_predecessor := habove
            coordinates := hcoordinates
            obstruction := Or.inr (by omega)
          }
    · exact .above_residual predecessor predecessorFirstTime quotient
        remainder {
          provenance := hpredecessor
          target_le_predecessor := habove
          coordinates := hcoordinates
          obstruction := Or.inl (Nat.lt_of_not_ge hready)
        }

end

end Recaman
