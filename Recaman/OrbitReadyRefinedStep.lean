import Recaman.OrbitReadyAdapters
import Recaman.ReadyCurrentDebt
import Recaman.HistoricalDebtBridge
import Recaman.ExtendedHistoryComplete

namespace Recaman

/-! # Refining orbit-ready semantic children

`OrbitReadyNormalInvariant.phaseSemanticStep` is locally total, but its child
is returned only through the broad `PhaseSemanticInvariant`.  Pattern matching
that proof recovers most mechanism-specific data:

* canonical children are orbit-ready;
* crossing-recovery children retain their crossing certificate;
* debt children become ready debt when their horizon is target-ready;
* ordinary normal children become extended-history nodes when their horizon
  is target-ready, using the stored first occurrence as representative.

The broad normal and debt constructors do not themselves retain the horizon
clock condition.  The exact residual below records only that missing field;
it does not claim an unproved refined successor.
-/

/-- Proof-carrying refined child domain reachable from the currently audited
normal/debt/history mechanisms. -/
def OrbitReadyRefinedInvariant
    (target : Nat) (node : PhaseSearchNode) : Prop :=
  ReadyCurrentOrDebtInvariant target node ∨
    ExtendedHistoryNormalInvariant target node ∨
      CrossingSearchInvariant target node

/-- Every refined child embeds in the existing semantic domain. -/
theorem OrbitReadyRefinedInvariant.toPhaseSemanticInvariant
    {target : Nat} {node : PhaseSearchNode}
    (h : OrbitReadyRefinedInvariant target node) :
    PhaseSemanticInvariant target node := by
  rcases h with hready | hextended | hcrossing
  · exact hready.toPhaseSemanticInvariant
  · rcases hextended with
      ⟨representativeTime, quotient, remainder, hcertificate⟩
    exact hcertificate.toPhaseSemanticInvariant
  · exact .crossing_recovery hcrossing

/-- Exact proof-data gap left after inspecting a broad semantic child.

For normal children all representative data already exists in
`NormalSearchCertificate`; only target readiness at the history horizon is
absent.  For debt children the strong invariant is already present and the
same clock field alone is absent. -/
inductive OrbitReadyRefinedChildResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | normal_horizon_not_ready
      (child : PhaseSearchNode)
      (certificate : NormalSearchInvariant target child)
      (progress : PhaseSearchProgress target child parent)
      (not_ready : child.horizon + 1 < target) :
      OrbitReadyRefinedChildResidual target parent
  | debt_horizon_not_ready
      (child : PhaseSearchNode) (value firstTime : Nat)
      (certificate : DebtInvariant target child value firstTime)
      (progress : PhaseSearchProgress target child parent)
      (not_ready : child.horizon + 1 < target) :
      OrbitReadyRefinedChildResidual target parent

/-- Refine one broad semantic child while retaining its strict rank edge.
This is constructor-complete for `PhaseSemanticInvariant`; the only failure
is the explicit missing horizon clock on ordinary normal or debt children. -/
theorem phaseSemanticChild_refine_or_horizonResidual
    {target : Nat} (htarget : 0 < target)
    {parent child : PhaseSearchNode}
    (hsemantic : PhaseSemanticInvariant target child)
    (hprogress : PhaseSearchProgress target child parent) :
    (OrbitReadyRefinedInvariant target child ∧
      PhaseSemanticInvariant target child ∧
      PhaseSearchProgress target child parent) ∨
      OrbitReadyRefinedChildResidual target parent := by
  cases hsemantic with
  | canonical_start hstart =>
      have hready := hstart.toOrbitReadyNormalInvariant htarget
      exact Or.inl ⟨Or.inl (Or.inl hready),
        .canonical_start hstart, hprogress⟩
  | normal hnormal =>
      by_cases hhorizonReady : target ≤ child.horizon + 1
      · rcases hnormal with ⟨value, firstTime, quotient, remainder, hcert⟩
        have hextended : ExtendedHistoryNormalCertificate target child
            firstTime quotient remainder := {
          target_positive := hcert.target_positive
          node_eq := by
            rw [hcert.first.1]
            exact hcert.node_eq
          representative_le_horizon := hcert.firstTime_le_horizon
          horizon_time_ready := hhorizonReady
          target_le_value := by
            rw [hcert.first.1]
            exact hcert.target_le
          coordinates := hcert.coordinates
        }
        have hnormal' : NormalSearchInvariant target child :=
          ⟨value, firstTime, quotient, remainder, hcert⟩
        exact Or.inl ⟨Or.inr (Or.inl
          ⟨firstTime, quotient, remainder, hextended⟩),
          .normal hnormal', hprogress⟩
      · exact Or.inr (.normal_horizon_not_ready child hnormal hprogress
          (by omega))
  | debt value firstTime hdebt =>
      by_cases hhorizonReady : target ≤ child.horizon + 1
      · have hready : ReadyDebtInvariant target child value firstTime := {
          debt := hdebt
          horizon_ready := hhorizonReady
        }
        exact Or.inl ⟨Or.inl (Or.inr ⟨value, firstTime, hready⟩),
          .debt value firstTime hdebt, hprogress⟩
      · exact Or.inr (.debt_horizon_not_ready child value firstTime hdebt
          hprogress (by omega))
  | crossing_recovery hcrossing =>
      exact Or.inl ⟨Or.inr (Or.inr hcrossing),
        .crossing_recovery hcrossing, hprogress⟩

/-- Maximum refinement obtainable from the current black-box orbit-ready
step.  Target occurrence is unchanged; every returned semantic child is
promoted to the proof-carrying refined domain unless its broad normal/debt
certificate omitted the child-horizon readiness condition. -/
theorem OrbitReadyNormalInvariant.refinedStep_or_horizonResidual
    {target : Nat} {parent : PhaseSearchNode}
    (h : OrbitReadyNormalInvariant target parent) :
    (∃ witness, a witness = target) ∨
      (∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      OrbitReadyRefinedChildResidual target parent := by
  rcases h.phaseSemanticStep with hoccurs |
      ⟨child, hsemantic, hprogress⟩
  · exact Or.inl hoccurs
  · have htarget : 0 < target := by
      rcases h with ⟨time, quotient, remainder, hcertificate⟩
      exact hcertificate.target_positive
    rcases phaseSemanticChild_refine_or_horizonResidual htarget hsemantic
        hprogress with hrefined | hresidual
    · exact Or.inr (Or.inl ⟨child, hrefined.1, hrefined.2.1,
        hrefined.2.2⟩)
    · exact Or.inr (Or.inr hresidual)

/-- The residual really reflects missing information in the broad normal
constructor: the standard time-three target-six normal certificate is not
horizon-ready.  This theorem is not a claim that the node is produced by the
orbit-ready step; it isolates why constructor inspection alone cannot promote
every broad normal child. -/
theorem broadNormalChild_can_lack_horizonReadiness :
    NormalSearchInvariant 6 ⟨3, a 3, .normal, a 3⟩ ∧
      ¬ (6 ≤ (⟨3, a 3, .normal, a 3⟩ : PhaseSearchNode).horizon + 1) := by
  simpa using normalSearchInvariant_does_not_imply_time_ready

end Recaman
