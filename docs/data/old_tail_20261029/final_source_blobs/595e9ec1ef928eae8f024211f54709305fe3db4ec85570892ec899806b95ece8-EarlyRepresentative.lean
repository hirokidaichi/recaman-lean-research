import Recaman.ExtendedHistoryNormal
import Recaman.CoverageDebtBridge

namespace Recaman

/-! # Historical representatives before target time-readiness

An extended-history normal node may represent an actual value above the
target at a time `representativeTime` for which
`representativeTime+1 < target`.  Such a node cannot be passed to the epoch
API as an orbit-ready node, even though its later history horizon is ready.

This module analyzes the very next actual transition.  A legal subtraction
which stays above the target gives a strictly smaller extended-history child
at the same history horizon.  A blocked subtraction whose positive candidate
is above the target enters strong debt at that horizon.  Equality is always
returned immediately.  The two genuinely unclosed cases are recorded
exactly: a legal subtraction crossing below the target after the historical
budget has already been consumed, and a forced addition blocked by an
already-seen below-target candidate.
-/

/-- An extended-history certificate whose representative time is strictly
too early for the target epoch API. -/
structure EarlyRepresentativeCertificate
    (target : Nat) (node : PhaseSearchNode)
    (representativeTime quotient remainder : Nat) : Prop where
  extended : ExtendedHistoryNormalCertificate target node
    representativeTime quotient remainder
  not_ready : representativeTime + 1 < target

/-- Elementary arithmetic forced by an early above-target representative.
The subtraction candidate is positive and the quotient cannot be zero.  In
the quotient-one chamber the remainder is at least two, so the potential is
positive; for larger quotients no uniform potential lower bound is claimed
(the target-five example has negative potential). -/
theorem EarlyRepresentativeCertificate.coordinate_constraints
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    0 < representativeTime ∧
      0 < quotient ∧
      representativeTime + 1 < a representativeTime ∧
      (quotient = 1 →
        2 ≤ remainder ∧
          (1 : Int) ≤ potential quotient remainder) := by
  have htarget := h.extended.target_le_value
  have htargetPositive := h.extended.target_positive
  have hcandidatePositive : representativeTime + 1 <
      a representativeTime := by
    have hnotReady := h.not_ready
    omega
  have htimePositive : 0 < representativeTime := by
    by_cases hzero : representativeTime = 0
    · subst representativeTime
      have htargetZero : target ≤ 0 := by
        simpa [a, stateAt, initial] using htarget
      omega
    · omega
  have hquotientPositive : 0 < quotient := by
    cases quotient with
    | zero =>
        have heq := h.extended.coordinates.eqn
        have hrlt := h.extended.coordinates.remainder_lt
        simp at heq
        omega
    | succ quotient => omega
  refine ⟨htimePositive, hquotientPositive, hcandidatePositive, ?_⟩
  intro hquotientOne
  subst quotient
  have heq := h.extended.coordinates.eqn
  have hremainder : 2 ≤ remainder := by omega
  constructor
  · exact hremainder
  · simp [potential, upperTri]
    omega

/-- An above-target legal-subtraction child at the same history horizon.
The readiness disjunction states whether advancing the representative by one
has reached the ordinary epoch boundary or remains in the early domain. -/
structure EarlyRepresentativeForwardChild
    (target : Nat) (parent child : PhaseSearchNode) : Type where
  representativeTime : Nat
  quotient : Nat
  remainder : Nat
  certificate : ExtendedHistoryNormalCertificate target child
    representativeTime quotient remainder
  target_strict : target < a representativeTime
  readiness : target ≤ representativeTime + 1 ∨
    representativeTime + 1 < target
  semantic : PhaseSemanticInvariant target child
  progress : PhaseSearchProgress target child parent

/-- Exact residuals after inspecting the next transition from an early
representative. -/
inductive EarlyRepresentativeResidual
    (target : Nat) (node : PhaseSearchNode) : Prop
  | legal_downcross
      (representativeTime quotient remainder : Nat)
      (certificate : EarlyRepresentativeCertificate target node
        representativeTime quotient remainder)
      (legal : CanSubtract (representativeTime + 1)
        (stateAt representativeTime))
      (next_below_target : a (representativeTime + 1) < target)
      (representative_to_next_budget_drop :
        missingBelowCount target (representativeTime + 1) <
          missingBelowCount target representativeTime)
      (history_budget_gap :
        missingBelowCount target node.horizon <
          missingBelowCount target representativeTime) :
      EarlyRepresentativeResidual target node
  | forced_below_candidate
      (representativeTime quotient remainder candidate : Nat)
      (certificate : EarlyRepresentativeCertificate target node
        representativeTime quotient remainder)
      (candidate_eq : candidate =
        a representativeTime - (representativeTime + 1))
      (candidate_positive : 0 < candidate)
      (candidate_below_target : candidate < target)
      (candidate_seen : candidate ∈ valuesThrough representativeTime)
      (forced : ¬ CanSubtract (representativeTime + 1)
        (stateAt representativeTime))
      (next_value : a (representativeTime + 1) =
        a representativeTime + (representativeTime + 1)) :
      EarlyRepresentativeResidual target node

/-- Strong proof-relevant classification.  Successful non-target outcomes
retain either an extended-history normal child or a strong debt child; no
bare historical `NormalSearchInvariant` is introduced. -/
inductive EarlyRepresentativeOutcome
    (target : Nat) (node : PhaseSearchNode) : Prop
  | target_occurs (witness : Nat) (value_eq : a witness = target) :
      EarlyRepresentativeOutcome target node
  | forward_child (child : PhaseSearchNode)
      (certificate : EarlyRepresentativeForwardChild target node child) :
      EarlyRepresentativeOutcome target node
  | debt_child (value firstTime : Nat) (child : PhaseSearchNode)
      (child_eq : child =
        ⟨node.horizon, node.anchorParent, .debt, firstTime⟩)
      (invariant : DebtInvariant target child value firstTime)
      (semantic : PhaseSemanticInvariant target child)
      (progress : PhaseSearchProgress target child node) :
      EarlyRepresentativeOutcome target node
  | residual (obstruction : EarlyRepresentativeResidual target node) :
      EarlyRepresentativeOutcome target node

/-- One-step analysis of an early representative.

Legal subtraction is fresh.  If it remains above the target, the represented
value and anchor decrease at fixed history horizon.  If it crosses below,
the standard downcrossing theorem either finds the target or exposes the
already-consumed history-budget gap.

When subtraction is blocked, positivity says the candidate was seen.  An
above-target candidate enters debt at fixed horizon and anchor; target
equality is a witness, while a below-target candidate is the precise forced
residual. -/
theorem EarlyRepresentativeCertificate.classify
    {target : Nat} {node : PhaseSearchNode}
    {representativeTime quotient remainder : Nat}
    (h : EarlyRepresentativeCertificate target node representativeTime
      quotient remainder) :
    EarlyRepresentativeOutcome target node := by
  by_cases hcurrent : a representativeTime = target
  · exact .target_occurs representativeTime hcurrent
  have habove : target < a representativeTime :=
    Nat.lt_of_le_of_ne h.extended.target_le_value (Ne.symm hcurrent)
  have hconstraints := h.coordinate_constraints
  have hcandidatePositive : representativeTime + 1 <
      a representativeTime := hconstraints.2.2.1
  have hrepresentativeBeforeHorizon : representativeTime < node.horizon := by
    have hnotReady := h.not_ready
    have hhorizonReady := h.extended.horizon_time_ready
    omega
  have hnextInHorizon : representativeTime + 1 ≤ node.horizon := by omega
  by_cases hcan : CanSubtract (representativeTime + 1)
      (stateAt representativeTime)
  · have hnext := a_succ_of_canSubtract hcan
    have hnextDrop : a (representativeTime + 1) <
        a representativeTime := by omega
    by_cases hnextEq : a (representativeTime + 1) = target
    · exact .target_occurs (representativeTime + 1) hnextEq
    by_cases hnextAbove : target ≤ a (representativeTime + 1)
    · have hnextStrict : target < a (representativeTime + 1) :=
        Nat.lt_of_le_of_ne hnextAbove (Ne.symm hnextEq)
      have hnextPositive : 0 < representativeTime + 1 := by omega
      rcases exists_coordinatesAt hnextPositive with
        ⟨nextQ, nextR, hnextCoordinates⟩
      let child : PhaseSearchNode :=
        ⟨node.horizon, a (representativeTime + 1), .normal,
          a (representativeTime + 1)⟩
      have hchildCertificate : ExtendedHistoryNormalCertificate target child
          (representativeTime + 1) nextQ nextR := {
        target_positive := h.extended.target_positive
        node_eq := rfl
        representative_le_horizon := hnextInHorizon
        horizon_time_ready := by
          simpa only [child] using h.extended.horizon_time_ready
        target_le_value := hnextAbove
        coordinates := hnextCoordinates
      }
      have hprogress : PhaseSearchProgress target child node := by
        rw [h.extended.node_eq]
        exact phaseSearchProgress_of_horizonAndAnchor
          (Nat.le_refl _) hnextDrop
      exact .forward_child child {
        representativeTime := representativeTime + 1
        quotient := nextQ
        remainder := nextR
        certificate := hchildCertificate
        target_strict := hnextStrict
        readiness := by
          by_cases hready : target ≤ representativeTime + 1 + 1
          · exact Or.inl hready
          · exact Or.inr (Nat.lt_of_not_ge hready)
        semantic := hchildCertificate.toPhaseSemanticInvariant
        progress := hprogress
      }
    · have hnextBelow : a (representativeTime + 1) < target :=
        Nat.lt_of_not_ge hnextAbove
      rcases orbit_downcrossing_occurs_or_budgetDrop
          (show representativeTime ≤ representativeTime + 1 by omega)
          h.extended.target_le_value hnextBelow with
        hoccurs | hbudgetDrop
      · rcases hoccurs with ⟨witness, _, _, hvalue⟩
        exact .target_occurs witness hvalue
      · have hhistoryMono : missingBelowCount target node.horizon ≤
            missingBelowCount target (representativeTime + 1) :=
          missingBelowCount_antitone hnextInHorizon
        have hhistoryGap : missingBelowCount target node.horizon <
            missingBelowCount target representativeTime := by omega
        exact .residual (.legal_downcross representativeTime quotient
          remainder h hcan hnextBelow hbudgetDrop hhistoryGap)
  · let candidate := a representativeTime - (representativeTime + 1)
    have hcandidatePositive' : 0 < candidate := by
      simp only [candidate]
      omega
    have hcandidateSeen : candidate ∈ valuesThrough representativeTime := by
      rcases not_canSubtract_cases hcan with hnonpositive | hseen
      · exact False.elim (by omega)
      · simpa only [candidate] using hseen
    by_cases hcandidateEq : candidate = target
    · rcases mem_valuesThrough_iff.mp hcandidateSeen with
        ⟨witness, _, hvalue⟩
      exact .target_occurs witness (by simpa [hcandidateEq] using hvalue)
    by_cases hcandidateAbove : target ≤ candidate
    · rcases history_member_has_firstAt hcandidateSeen with
        ⟨firstTime, hfirstTime, hfirst⟩
      have hfirstStrict : firstTime < representativeTime := by
        rcases Nat.eq_or_lt_of_le hfirstTime with heq | hlt
        · subst firstTime
          have hfirstValue := hfirst.1
          simp only [candidate] at hfirstValue
          omega
        · exact hlt
      let child : PhaseSearchNode :=
        ⟨node.horizon, node.anchorParent, .debt, firstTime⟩
      have hcandidateDrop : candidate < node.anchorParent := by
        have hanchor : node.anchorParent = a representativeTime := by
          simpa using congrArg PhaseSearchNode.anchorParent h.extended.node_eq
        rw [hanchor]
        simp only [candidate]
        omega
      have hdebt : DebtInvariant target child candidate firstTime := {
        phase_eq := rfl
        local_eq := rfl
        target_le := hcandidateAbove
        first := hfirst
        firstTime_lt_horizon :=
          Nat.lt_trans hfirstStrict hrepresentativeBeforeHorizon
        value_lt_anchor := hcandidateDrop
      }
      have hsemantic : PhaseSemanticInvariant target child :=
        .debt candidate firstTime hdebt
      have hprogress : PhaseSearchProgress target child node := by
        dsimp only [child]
        rw [h.extended.node_eq]
        exact phaseSearch_enterDebt
      exact .debt_child candidate firstTime child rfl hdebt hsemantic
        hprogress
    · have hcandidateBelow : candidate < target :=
        Nat.lt_of_not_ge hcandidateAbove
      have hnext := a_succ_of_not_canSubtract hcan
      exact .residual (.forced_below_candidate representativeTime quotient
        remainder candidate h rfl hcandidatePositive' hcandidateBelow
        hcandidateSeen hcan hnext)

/-- Refined domain preserved by successful early-representative outcomes.
It contains proof-carrying extended-history nodes and the current/debt domain
from `CoverageDebtBridge`, but no bare historical normal certificate. -/
def EarlyRefinedInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  ExtendedHistoryNormalInvariant target node ∨
    CurrentOrDebtInvariant target node

/-- Forget the strongest classification to a restricted-step shape, retaining
the two honest residuals. -/
theorem EarlyRepresentativeOutcome.toRefinedStep_or_residual
    {target : Nat} {node : PhaseSearchNode}
    (h : EarlyRepresentativeOutcome target node) :
    (∃ witness, a witness = target) ∨
      (∃ child, EarlyRefinedInvariant target child ∧
        PhaseSearchProgress target child node) ∨
      EarlyRepresentativeResidual target node := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | forward_child child hforward =>
      exact Or.inr (Or.inl ⟨child,
        Or.inl ⟨hforward.representativeTime, hforward.quotient,
          hforward.remainder, hforward.certificate⟩,
        hforward.progress⟩)
  | debt_child value firstTime child hchild hdebt hsemantic hprogress =>
      exact Or.inr (Or.inl ⟨child,
        Or.inr (Or.inr ⟨value, firstTime, hdebt⟩), hprogress⟩)
  | residual hresidual => exact Or.inr (Or.inr hresidual)

/-- The real early representative for target five takes the legal-downcross
residual: `a 3=6`, legal subtraction lands at `a 4=2`, and the target-five
missing-history budget has already fallen at the historical horizon four. -/
theorem earlyRepresentative_five_three_legalDowncross :
    EarlyRepresentativeResidual 5
      ⟨4, a 3, .normal, a 3⟩ := by
  have hextended : ExtendedHistoryNormalCertificate 5
      ⟨4, a 3, .normal, a 3⟩ 3 2 0 :=
    extendedHistory_horizonReady_not_representativeReady.1
  have hearly : EarlyRepresentativeCertificate 5
      ⟨4, a 3, .normal, a 3⟩ 3 2 0 := {
    extended := hextended
    not_ready := by decide
  }
  exact .legal_downcross 3 2 0 hearly (by decide) (by decide)
    (by decide) (by decide)

end Recaman
