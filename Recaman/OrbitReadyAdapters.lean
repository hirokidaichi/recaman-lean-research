import Recaman.NormalProvenance
import Recaman.CanonicalForcedGrowth

namespace Recaman

/-! # Orbit-ready adapters for current normal children

Several existing semantic closure theorems construct a normal child at an
actual orbit time, but immediately forget that fact by returning only
`PhaseSemanticInvariant`.  This module records the common proof data and
provides conservative adapters to `OrbitReadyNormalInvariant`.

The only datum not uniformly retained by those branch APIs is the absolute
epoch precondition `target ≤ time+1`.  `CurrentNormalChildEvidence` therefore
keeps all other current-state and rank data, and its conversion theorem takes
that condition explicitly.  Branches whose source certificate already
implies it discharge the condition locally.
-/

/-- Evidence common to a current-state normal child before the absolute-time
precondition is supplied.  Unlike a broad `NormalSearchInvariant`, the node
is definitionally the actual state at `time`, and its coordinates are current.
-/
structure CurrentNormalChildEvidence
    (target : Nat) (parent : PhaseSearchNode) (time q r : Nat) : Prop where
  target_positive : 0 < target
  target_le_value : target ≤ a time
  coordinates : CoordinatesAt time q r
  progress : PhaseSearchProgress target
    ⟨time, a time, .normal, a time⟩ parent

/-- Once the absolute-time condition is available, the retained branch data
gives both orbit readiness and the original rank edge without rebuilding a
first-occurrence certificate. -/
theorem CurrentNormalChildEvidence.orbitReady_and_progress
    {target : Nat} {parent : PhaseSearchNode} {time q r : Nat}
    (h : CurrentNormalChildEvidence target parent time q r)
    (htime : target ≤ time + 1) :
    OrbitReadyNormalInvariant target
        ⟨time, a time, .normal, a time⟩ ∧
      PhaseSearchProgress target
        ⟨time, a time, .normal, a time⟩ parent := by
  refine ⟨⟨time, q, r, {
    target_positive := h.target_positive
    node_eq := rfl
    time_ready := htime
    target_le_value := h.target_le_value
    coordinates := h.coordinates
  }⟩, h.progress⟩

/-- The extra condition above is exact: orbit readiness of this actual-state
node necessarily recovers the same absolute-time bound. -/
theorem CurrentNormalChildEvidence.time_ready_of_orbitReady
    {target : Nat} {parent : PhaseSearchNode} {time q r : Nat}
    (_h : CurrentNormalChildEvidence target parent time q r)
    (hready : OrbitReadyNormalInvariant target
      ⟨time, a time, .normal, a time⟩) :
    target ≤ time + 1 := by
  rcases hready with ⟨actualTime, actualQ, actualR, hcert⟩
  have htimeEq : actualTime = time := by
    simpa using (congrArg PhaseSearchNode.horizon hcert.node_eq).symm
  simpa [htimeEq] using hcert.time_ready

/-- Canonical starts already retain every field of the strengthened current
normal certificate.  This is the adapter entry point used by callers which
should not need to know the representation of `TargetStartInvariant`. -/
theorem targetStartInvariant_orbitReadyAdapter
    {target : Nat} (htarget : 0 < target) {node : PhaseSearchNode}
    (h : TargetStartInvariant target node) :
    OrbitReadyNormalInvariant target node :=
  h.toOrbitReadyNormalInvariant htarget

/-- Re-anchor a strong current normal invariant at its actual value.  The
coordinate and time data are preserved; only the possibly larger search
anchor is forgotten. -/
theorem NormalPhaseInvariantAt.reanchorOrbitReady
    {target n activeParent q r : Nat}
    (htarget : 0 < target)
    (h : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r) :
    OrbitReadyNormalInvariant target
      ⟨n, a n, .normal, a n⟩ := by
  exact ⟨n, q, r, {
    target_positive := htarget
    node_eq := rfl
    time_ready := h.time_ready
    target_le_value := h.target_le_value
    coordinates := h.coordinates
  }⟩

/-- Orbit-ready strengthening of
`normalPhaseInvariant_phaseSemantic_progress`.  The existing proof's
re-anchored child is current, so the stronger certificate is retained across
the same composed rank edge. -/
theorem normalPhaseInvariant_currentProgress_orbitReady
    {target n activeParent q r : Nat}
    (htarget : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r)
    {parent : PhaseSearchNode}
    (hprogress : PhaseSearchProgress target
      ⟨n, activeParent, .normal, a n⟩ parent) :
    ∃ child, OrbitReadyNormalInvariant target child ∧
      PhaseSearchProgress target child parent := by
  let child : PhaseSearchNode := ⟨n, a n, .normal, a n⟩
  have hready : OrbitReadyNormalInvariant target child := by
    simpa [child] using hinv.reanchorOrbitReady htarget
  rcases Nat.eq_or_lt_of_le hinv.value_le_anchor with
    hanchorEq | hanchorDrop
  · change a n = activeParent at hanchorEq
    subst activeParent
    exact ⟨child, hready, by simpa [child] using hprogress⟩
  · have hstep : PhaseSearchProgress target child
        ⟨n, activeParent, .normal, a n⟩ := by
      simpa [child] using
        (phaseSearchProgress_of_horizonAndAnchor
          (target := target) (Nat.le_refl n) hanchorDrop)
    exact ⟨child, hready, hstep.trans hprogress⟩

/-- The above-target branch of a normal epoch exit is current-state data.
Re-anchoring its raw child at `a time` preserves progress and supplies the
stronger invariant directly. -/
theorem normalEpochExit_above_orbitReadyAdapter
    {target n activeParent q r time quotient remainder : Nat}
    (htarget : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r)
    (hevidence : NormalEpochExitEvidence target time quotient remainder
      ⟨n, activeParent, .normal, a n⟩
      ⟨time, activeParent, .normal, a time⟩)
    (habove : target ≤ a time) :
    OrbitReadyNormalInvariant target
        ⟨time, a time, .normal, a time⟩ ∧
      PhaseSearchProgress target
        ⟨time, a time, .normal, a time⟩
        ⟨n, activeParent, .normal, a n⟩ := by
  have hcurrentProgress : PhaseSearchProgress target
      ⟨time, a time, .normal, a time⟩
      ⟨n, activeParent, .normal, a n⟩ :=
    normalProgress_reanchorAtValue hinv.value_le_anchor hevidence.progress
  exact (CurrentNormalChildEvidence.mk htarget habove
    hevidence.coordinates hcurrentProgress).orbitReady_and_progress
      hevidence.time_ready

/-- Generic adapter for the forward-above branch of the nonnegative history
search.  It consumes the exact `HistorySearchProgress` already returned by
that branch and re-anchors its current child. -/
theorem nonnegativeForwardAbove_orbitReadyAdapter
    {target n activeParent t q r : Nat}
    (htarget : 0 < target)
    (htime : target ≤ t + 1)
    (hparentBound : a n ≤ activeParent)
    (habove : target ≤ a t)
    (hcoord : CoordinatesAt t q r)
    (hprogress : HistorySearchProgress target
      ⟨t, activeParent, a t⟩ ⟨n, activeParent, a n⟩) :
    OrbitReadyNormalInvariant target
        ⟨t, a t, .normal, a t⟩ ∧
      PhaseSearchProgress target
        ⟨t, a t, .normal, a t⟩
        ⟨n, activeParent, .normal, a n⟩ := by
  have hphase : PhaseSearchProgress target
      ⟨t, activeParent, .normal, a t⟩
      ⟨n, activeParent, .normal, a n⟩ :=
    hprogress.toNormalPhaseSearchProgress
  have hcurrentProgress :=
    normalProgress_reanchorAtValue hparentBound hphase
  exact (CurrentNormalChildEvidence.mk htarget habove hcoord
    hcurrentProgress).orbitReady_and_progress htime

/-- Above-target forward children of the canonical history frontier are
orbit-ready.  The source's canonical time bound and strict time advance
derive the child time bound which the older frontier API did not return. -/
theorem canonicalHistoryFrontier_above_orbitReadyAdapter
    {target n t q r : Nat}
    (htarget : 0 < target)
    (htimeReady : target ≤ n + 1)
    (htime : n < t)
    (habove : target ≤ a t)
    (hcoord : CoordinatesAt t q r)
    (hprogress : HistoryBudgetProgress target
      ⟨a t, t⟩ ⟨a n, n⟩) :
    OrbitReadyNormalInvariant target
        ⟨t, a t, .normal, a t⟩ ∧
      PhaseSearchProgress target
        ⟨t, a t, .normal, a t⟩ (targetStartNode n) := by
  have hphase := historyBudgetProgress_to_phaseSemanticRank hprogress
  exact (CurrentNormalChildEvidence.mk htarget habove hcoord
    hphase).orbitReady_and_progress (by
      have := htimeReady
      omega)

/-- Adapter for the future-current branch exposed in canonical level zero.
All needed time information comes from the canonical certificate and the
strict future-time witness. -/
theorem canonicalLevelZero_future_orbitReadyAdapter
    {target n t q r : Nat}
    (htarget : 0 < target)
    (hcert : TargetStartCertificate target n)
    (htime : n < t)
    (habove : target ≤ a t)
    (hcoord : CoordinatesAt t q r)
    (hvalueDrop : a t < a n) :
    OrbitReadyNormalInvariant target
        ⟨t, a t, .normal, a t⟩ ∧
      PhaseSearchProgress target
        ⟨t, a t, .normal, a t⟩ (targetStartNode n) := by
  have hphase : PhaseSearchProgress target
      ⟨t, a t, .normal, a t⟩ (targetStartNode n) :=
    phaseSearchProgress_of_horizonAndAnchor (Nat.le_of_lt htime) hvalueDrop
  exact (CurrentNormalChildEvidence.mk htarget habove hcoord
    hphase).orbitReady_and_progress (by
      have := hcert.time_ready
      omega)

/-- Above-target legal subtraction produces an actual, fresh current child.
The added source-time hypothesis is precisely the time-readiness datum absent
from `canonical_legalSubtraction_phaseSemantic`'s public signature. -/
theorem canonicalLegalSubtraction_above_orbitReadyAdapter
    {target n : Nat}
    (htarget : 0 < target)
    (htimeReady : target ≤ n + 1)
    (habove : target ≤ a (n + 1))
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    OrbitReadyNormalInvariant target
        ⟨n + 1, a (n + 1), .normal, a (n + 1)⟩ ∧
      PhaseSearchProgress target
        ⟨n + 1, a (n + 1), .normal, a (n + 1)⟩
        (targetStartNode n) := by
  have hnextDrop : a (n + 1) < a n := by
    have hpositive : n + 1 < a n := by simpa [a] using hcan.1
    have hnext := a_succ_of_canSubtract hcan
    omega
  rcases exists_coordinatesAt (show 0 < n + 1 by omega) with
    ⟨q, r, hcoord⟩
  have hphase : PhaseSearchProgress target
      ⟨n + 1, a (n + 1), .normal, a (n + 1)⟩
      (targetStartNode n) :=
    phaseSearchProgress_of_horizonAndAnchor (by omega) hnextDrop
  exact (CurrentNormalChildEvidence.mk htarget habove hcoord
    hphase).orbitReady_and_progress (by omega)

/-- Adapter for the forward-above alternative of the quotient-at-least-two
forced-addition frontier.  Its raw two-step history edge already has the
right parent bound; current coordinates are reconstructed at the actual
future time. -/
theorem forcedAdditionForwardAbove_orbitReadyAdapter
    {target n : Nat}
    (htarget : 0 < target)
    (htimeReady : target ≤ n + 1)
    (habove : target ≤ a (n + 2))
    (hprogress : HistorySearchProgress target
      ⟨n + 2, a n, a (n + 2)⟩ ⟨n, a n, a n⟩) :
    OrbitReadyNormalInvariant target
        ⟨n + 2, a (n + 2), .normal, a (n + 2)⟩ ∧
      PhaseSearchProgress target
        ⟨n + 2, a (n + 2), .normal, a (n + 2)⟩
        (targetStartNode n) := by
  rcases exists_coordinatesAt (show 0 < n + 2 by omega) with
    ⟨q, r, hcoord⟩
  exact nonnegativeForwardAbove_orbitReadyAdapter htarget (by omega)
    (Nat.le_refl _) habove hcoord hprogress

/-- The immediate state of the canonical forced-growth chamber is also
orbit-ready, even though the existing theorem proves that it is not yet a
rank child of the canonical parent.  This separates semantic readiness from
the deliberate two-step rank lookahead. -/
theorem CanonicalForcedGrowthChamber.nextState_orbitReady
    {target level : Nat} {parent : PhaseSearchNode}
    (htarget : 0 < target)
    (h : CanonicalForcedGrowthChamber target parent level) :
    ∃ n child,
      child = ⟨n + 1, a (n + 1), .normal, a (n + 1)⟩ ∧
      OrbitReadyNormalInvariant target child ∧
      ¬ PhaseSearchProgress target child parent := by
  rcases h.nextState htarget with
    ⟨n, child, _, hchild, _, _, _, _, _, _, hstrong, hnoProgress⟩
  subst child
  exact ⟨n, _, rfl, hstrong.reanchorOrbitReady htarget, hnoProgress⟩

end Recaman
