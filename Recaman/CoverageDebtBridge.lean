import Recaman.NormalProvenance

namespace Recaman

/-! # Coverage blockers as current normal or debt children

The generic semantic interpretation of `CoverageStep` enlarges the history
horizon and admits its smaller first-occurring value as a historical normal
node.  For a current parent there is a sharper split.

If the blocker's first occurrence is at or after the parent time, it is an
actual future orbit state and therefore gives an orbit-ready current normal
child.  If its first occurrence is earlier, keeping the parent horizon and
anchor while entering the debt phase gives a strong `DebtInvariant`.  Thus a
coverage blocker never needs to enter the generic historical-normal domain.
-/

/-- Minimal current-parent assumptions needed by the coverage/debt split.
The value bound is retained because it is part of both canonical and
orbit-ready parent APIs, although the blocker branch itself implies it again.
-/
structure CurrentCoverageParentCertificate
    (target n : Nat) : Prop where
  target_positive : 0 < target
  time_ready : target ≤ n + 1
  target_le_value : target ≤ a n

/-- Exact data for the future blocker branch.  Since the blocker is a first
occurrence no earlier than the parent, strict value decrease rules out equal
times; its own first time is therefore a genuine future current horizon. -/
structure CoverageCurrentChildCertificate
    (target n value firstTime : Nat) : Prop where
  target_lt_value : target < value
  first : FirstAt a value firstTime
  parent_time_lt : n < firstTime
  value_lt_parent : value < a n
  invariant : OrbitReadyNormalInvariant target
    (targetStartNode firstTime)
  progress : PhaseSearchProgress target
    (targetStartNode firstTime) (targetStartNode n)

/-- Exact data for an earlier coverage blocker.  The child keeps the current
history horizon and anchor, while its first-occurrence time becomes the debt
local measure. -/
structure CoverageDebtChildCertificate
    (target n value firstTime : Nat) : Prop where
  target_lt_value : target < value
  first : FirstAt a value firstTime
  first_time_lt_parent : firstTime < n
  value_lt_parent : value < a n
  invariant : DebtInvariant target
    ⟨n, a n, .debt, firstTime⟩ value firstTime
  semantic : PhaseSemanticInvariant target
    ⟨n, a n, .debt, firstTime⟩
  progress : PhaseSearchProgress target
    ⟨n, a n, .debt, firstTime⟩ (targetStartNode n)

/-- Proof-relevant strongest classification of a coverage step from a
current parent.  Equality with the target is discharged before choosing a
normal or debt child, so both child certificates retain strict target
inequality. -/
inductive CoverageCurrentDebtOutcome (target n : Nat) : Prop
  | target_occurs (witness : Nat) (value_eq : a witness = target) :
      CoverageCurrentDebtOutcome target n
  | current_child (value firstTime : Nat)
      (certificate : CoverageCurrentChildCertificate
        target n value firstTime) :
      CoverageCurrentDebtOutcome target n
  | debt_child (value firstTime : Nat)
      (certificate : CoverageDebtChildCertificate
        target n value firstTime) :
      CoverageCurrentDebtOutcome target n

/-- A target-start certificate supplies the minimal current-parent data. -/
theorem TargetStartCertificate.toCurrentCoverageParentCertificate
    {target n : Nat} (htarget : 0 < target)
    (h : TargetStartCertificate target n) :
    CurrentCoverageParentCertificate target n := {
  target_positive := htarget
  time_ready := h.time_ready
  target_le_value := h.value_ready
}

/-- Orbit readiness at the canonical current node supplies the same parent
data, independently of which current coordinates witness it. -/
theorem OrbitReadyNormalInvariant.toCurrentCoverageParentCertificate
    {target n : Nat}
    (h : OrbitReadyNormalInvariant target (targetStartNode n)) :
    CurrentCoverageParentCertificate target n := by
  rcases h with ⟨time, q, r, hready⟩
  have htime : time = n := by
    simpa [targetStartNode] using
      (congrArg PhaseSearchNode.horizon hready.node_eq).symm
  subst time
  exact {
    target_positive := hready.target_positive
    time_ready := hready.time_ready
    target_le_value := by
      simpa [targetStartNode] using hready.target_le_value
  }

/-- Main bridge.  A coverage target witness is returned immediately.  In the
blocker branch, target equality is also returned immediately; strict blockers
are then split by their first occurrence relative to the current parent.

The future branch constructs current coordinates at the first occurrence and
uses simultaneous horizon extension and anchor decrease for rank progress.
The earlier branch enters debt at fixed horizon and anchor, so phase decrease
alone supplies progress. -/
theorem coverageStep_currentOrDebt
    {target n : Nat}
    (hparent : CurrentCoverageParentCertificate target n)
    (hcoverage : CoverageStep target (a n) n) :
    CoverageCurrentDebtOutcome target n := by
  rcases hcoverage with hoccurs |
      ⟨value, firstTime, htargetValue, hfirst, hvalueDrop⟩
  · rcases hoccurs with ⟨witness, hvalue⟩
    exact .target_occurs witness hvalue
  · by_cases htargetEq : value = target
    · exact .target_occurs firstTime (by
        simpa [htargetEq] using hfirst.1)
    · have htargetLt : target < value := by omega
      by_cases hfuture : n ≤ firstTime
      · have hstrictFuture : n < firstTime := by
          rcases Nat.eq_or_lt_of_le hfuture with heq | hlt
          · subst firstTime
            have hfirstValue : a n = value := hfirst.1
            omega
          · exact hlt
        have hfirstPositive : 0 < firstTime := by omega
        rcases exists_coordinatesAt hfirstPositive with
          ⟨q, r, hcoordinates⟩
        have htargetAtFirst : target ≤ a firstTime := by
          rw [hfirst.1]
          exact htargetValue
        have hvalueDrop' : a firstTime < a n := by
          rw [hfirst.1]
          exact hvalueDrop
        have htimeReady : target ≤ firstTime + 1 := by
          have := hparent.time_ready
          omega
        have hready : OrbitReadyNormalInvariant target
            (targetStartNode firstTime) := by
          exact ⟨firstTime, q, r, {
            target_positive := hparent.target_positive
            node_eq := rfl
            time_ready := htimeReady
            target_le_value := htargetAtFirst
            coordinates := hcoordinates
          }⟩
        have hprogress : PhaseSearchProgress target
            (targetStartNode firstTime) (targetStartNode n) := by
          exact phaseSearchProgress_of_horizonAndAnchor
            (Nat.le_of_lt hstrictFuture) hvalueDrop'
        exact .current_child value firstTime {
          target_lt_value := htargetLt
          first := hfirst
          parent_time_lt := hstrictFuture
          value_lt_parent := hvalueDrop
          invariant := hready
          progress := hprogress
        }
      · have hearlier : firstTime < n := Nat.lt_of_not_ge hfuture
        let child : PhaseSearchNode :=
          ⟨n, a n, .debt, firstTime⟩
        have hdebt : DebtInvariant target child value firstTime := {
          phase_eq := rfl
          local_eq := rfl
          target_le := htargetValue
          first := hfirst
          firstTime_lt_horizon := hearlier
          value_lt_anchor := hvalueDrop
        }
        have hsemantic : PhaseSemanticInvariant target child :=
          .debt value firstTime hdebt
        have hprogress : PhaseSearchProgress target child
            (targetStartNode n) := by
          exact phaseSearch_enterDebt
        exact .debt_child value firstTime {
          target_lt_value := htargetLt
          first := hfirst
          first_time_lt_parent := hearlier
          value_lt_parent := hvalueDrop
          invariant := hdebt
          semantic := hsemantic
          progress := hprogress
        }

/-- Canonical-parent wrapper using only the standard target-start
certificate. -/
theorem coverageStep_targetStart_currentOrDebt
    {target n : Nat} (htarget : 0 < target)
    (hstart : TargetStartCertificate target n)
    (hcoverage : CoverageStep target (a n) n) :
    CoverageCurrentDebtOutcome target n :=
  coverageStep_currentOrDebt
    (hstart.toCurrentCoverageParentCertificate htarget) hcoverage

/-- Orbit-ready-parent wrapper. -/
theorem coverageStep_orbitReady_currentOrDebt
    {target n : Nat}
    (hparent : OrbitReadyNormalInvariant target (targetStartNode n))
    (hcoverage : CoverageStep target (a n) n) :
    CoverageCurrentDebtOutcome target n :=
  coverageStep_currentOrDebt
    hparent.toCurrentCoverageParentCertificate hcoverage

/-- Refined domain containing only actual current normal nodes and strong
debt nodes.  Historical normal nodes are deliberately absent. -/
def CurrentOrDebtInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  OrbitReadyNormalInvariant target node ∨
    ∃ value firstTime, DebtInvariant target node value firstTime

/-- Forget the proof-relevant classification to the refined current/debt
restricted-step interface. -/
theorem CoverageCurrentDebtOutcome.toCurrentOrDebtStep
    {target n : Nat}
    (h : CoverageCurrentDebtOutcome target n) :
    (∃ witness, a witness = target) ∨
      ∃ child, CurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | current_child value firstTime hcurrent =>
      exact Or.inr ⟨targetStartNode firstTime,
        Or.inl hcurrent.invariant, hcurrent.progress⟩
  | debt_child value firstTime hdebt =>
      exact Or.inr ⟨⟨n, a n, .debt, firstTime⟩,
        Or.inr ⟨value, firstTime, hdebt.invariant⟩,
        hdebt.progress⟩

/-- The same bridge also remains in the existing broad semantic domain,
while exposing that no historical-normal constructor was used. -/
theorem CoverageCurrentDebtOutcome.toPhaseSemanticStep
    {target n : Nat}
    (h : CoverageCurrentDebtOutcome target n) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | current_child value firstTime hcurrent =>
      exact Or.inr ⟨targetStartNode firstTime,
        hcurrent.invariant.toPhaseSemanticInvariant, hcurrent.progress⟩
  | debt_child value firstTime hdebt =>
      exact Or.inr ⟨⟨n, a n, .debt, firstTime⟩,
        hdebt.semantic, hdebt.progress⟩

end Recaman
