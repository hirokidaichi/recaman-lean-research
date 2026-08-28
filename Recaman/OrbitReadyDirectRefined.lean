import Recaman.OrbitReadyRefinedStep

namespace Recaman

/-! # Direct refined steps from orbit-ready normal nodes

The broad semantic step erases the history-clock evidence of its normal and
debt children.  This module follows the generating branches before that
erasure.  Parent drops are split into future current or earlier ready debt;
actual above-target states remain orbit-ready; and downcross restarts retain
their old representative as an extended-history certificate.
-/

/-- Parent-drop classification with the source clock copied to an earlier
debt child before the source certificate is forgotten. -/
theorem ParentDropCurrentDebtOutcome.toReadyRefinedStep
    {target parentTime activeParent : Nat}
    (htimeReady : target ≤ parentTime + 1)
    (h : ParentDropCurrentDebtOutcome target parentTime activeParent) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨parentTime, activeParent, .normal, a parentTime⟩ := by
  cases h with
  | target_occurs witness hvalue =>
      exact Or.inl ⟨witness, hvalue⟩
  | current_child value firstTime hcurrent =>
      exact Or.inr ⟨targetStartNode firstTime,
        Or.inl (Or.inl hcurrent.invariant), hcurrent.progress⟩
  | debt_child value firstTime hdebt =>
      have hready : ReadyDebtInvariant target
          ⟨parentTime, activeParent, .debt, firstTime⟩ value firstTime := {
        debt := hdebt.invariant
        horizon_ready := htimeReady
      }
      exact Or.inr
        ⟨⟨parentTime, activeParent, .debt, firstTime⟩,
          Or.inl (Or.inr ⟨value, firstTime, hready⟩), hdebt.progress⟩

/-- Lift a ready current/debt coverage result into the larger refined normal
domain. -/
private theorem coverageReady_to_refined
    {target n : Nat}
    (h : (∃ witness, a witness = target) ∨
      ∃ child, ReadyCurrentOrDebtInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n)) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  rcases h with hoccurs | ⟨child, hchild, hprogress⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨child, Or.inl hchild, hprogress⟩

/-- Negative normal epochs refined at their actual generating branches.
Every debt child keeps the source horizon, every future normal child is
current, and a below-target forward exit becomes extended-history normal. -/
theorem negativeNormal_refinedStep
    {target activeParent n q r : Nat}
    (htargetPositive : 0 < target)
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩ := by
  rcases negative_epoch_historySearchOutcome_or_qOneDebt
      htargetPositive hinv.time_ready hinv.value_le_anchor
      hinv.coordinates hinv.negative with
    hoccurs | hparent | horbit |
      ⟨t, remainder, landing, hnt, htvalue, htcoord, htborrow, _, _,
        hnonnegative, hbelow⟩
  · exact Or.inl hoccurs
  · rcases hparent with
      ⟨horizon, value, firstTime, htargetValue, hfirst,
        hanchorDrop, hprogress⟩
    have hevidence : NormalParentDropEvidence target horizon value firstTime
        ⟨n, activeParent, .normal, a n⟩
        ⟨horizon, value, .normal, a horizon⟩ := {
      child_eq := rfl
      target_le_anchor := htargetValue
      anchor_first := hfirst
      anchor_drop := hanchorDrop
      progress := hprogress.toNormalPhaseSearchProgress
    }
    exact (normalParentDrop_currentOrDebt htargetPositive
      hinv.time_ready hevidence).toReadyRefinedStep hinv.time_ready
  · rcases horbit with
      ⟨time, quotient, remainder, htime, hcoordinates, hprogress⟩
    have hevidence : NormalEpochExitEvidence target time quotient remainder
        ⟨n, activeParent, .normal, a n⟩
        ⟨time, activeParent, .normal, a time⟩ := {
      child_eq := rfl
      time_advance := htime
      time_ready := Nat.le_trans hinv.time_ready (by omega)
      coordinates := hcoordinates
      progress := hprogress.toNormalPhaseSearchProgress
    }
    by_cases habove : target ≤ a time
    · rcases normalEpochExit_above_orbitReadyAdapter htargetPositive hinv
          hevidence habove with ⟨hready, hphase⟩
      exact Or.inr
        ⟨⟨time, a time, .normal, a time⟩,
          Or.inl (Or.inl hready), hphase⟩
    · have htimeLe : n ≤ time := Nat.le_of_lt htime
      have hnewBelow : a time < target := Nat.lt_of_not_ge habove
      rcases orbit_downcrossing_occurs_or_budgetDrop htimeLe
          hinv.target_le_value hnewBelow with htarget | hbudget
      · rcases htarget with ⟨witness, _, _, hvalue⟩
        exact Or.inl ⟨witness, hvalue⟩
      · let child : PhaseSearchNode :=
          ⟨time, a n, .normal, a n⟩
        have hextended : ExtendedHistoryNormalInvariant target child :=
          ⟨n, q, r, {
            target_positive := htargetPositive
            node_eq := rfl
            representative_le_horizon := htimeLe
            horizon_time_ready := by
              simpa [child] using hevidence.time_ready
            target_le_value := hinv.target_le_value
            coordinates := hinv.coordinates
          }⟩
        exact Or.inr ⟨child, Or.inr (Or.inl hextended),
          Prod.Lex.left _ _ hbudget⟩
  · exact Or.inl (normalPhase_qOneDebt_already_occurs hinv hnt htvalue
      htcoord htborrow hnonnegative hbelow)

/-- A regular nonnegative level refined before converting its result to the
broad semantic domain. -/
theorem nonnegative_epoch_refinedStep
    {target activeParent n q r g : Nat}
    (htargetPositive : 0 < target)
    (htimeReady : target ≤ n + 1)
    (htargetValue : target ≤ a n)
    (hvalueBound : a n ≤ activeParent)
    (hlevelLower : 3 ≤ g)
    (hlevelUpper : g < target)
    (hcoord : CoordinatesAt n q r)
    (hpotential : potential q r = Int.ofNat g) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child
          ⟨n, activeParent, .normal, a n⟩ := by
  rcases nonnegative_epoch_historySearchOutcome hvalueBound htimeReady
      hlevelLower hlevelUpper hcoord hpotential with
    hoccurs | hparent | hqzero | hforward
  · exact Or.inl hoccurs
  · rcases hparent with
      ⟨value, firstTime, htargetAnchor, hfirst, hanchorDrop, hprogress⟩
    have hevidence : NormalParentDropEvidence target n value firstTime
        ⟨n, activeParent, .normal, a n⟩
        ⟨n, value, .normal, a n⟩ := {
      child_eq := rfl
      target_le_anchor := htargetAnchor
      anchor_first := hfirst
      anchor_drop := hanchorDrop
      progress := hprogress.toNormalPhaseSearchProgress
    }
    exact (normalParentDrop_currentOrDebt htargetPositive htimeReady
      hevidence).toReadyRefinedStep htimeReady
  · subst q
    have hvalue : a n = r := by simpa using hcoord.eqn
    have hlevel : r = g := by
      apply Int.ofNat_inj.mp
      simpa [potential, upperTri] using hpotential
    omega
  · rcases hforward with
      ⟨time, childQ, childR, hnt, _, hchildCoord, _, hrawProgress⟩
    by_cases habove : target ≤ a time
    · rcases nonnegativeForwardAbove_orbitReadyAdapter htargetPositive
          (by omega) hvalueBound habove hchildCoord hrawProgress with
        ⟨hready, hprogress⟩
      exact Or.inr
        ⟨⟨time, a time, .normal, a time⟩,
          Or.inl (Or.inl hready), hprogress⟩
    · have htimeLe : n ≤ time := Nat.le_of_lt hnt
      have hbelow : a time < target := Nat.lt_of_not_ge habove
      rcases orbit_downcrossing_occurs_or_budgetDrop htimeLe
          htargetValue hbelow with htarget | hbudget
      · rcases htarget with ⟨witness, _, _, hvalue⟩
        exact Or.inl ⟨witness, hvalue⟩
      · let child : PhaseSearchNode :=
          ⟨time, a n, .normal, a n⟩
        have hchildReady : target ≤ time + 1 := by
          exact Nat.le_trans htimeReady (by omega)
        have hextended : ExtendedHistoryNormalInvariant target child :=
          ⟨n, q, r, {
            target_positive := htargetPositive
            node_eq := rfl
            representative_le_horizon := htimeLe
            horizon_time_ready := by
              simpa [child] using hchildReady
            target_le_value := htargetValue
            coordinates := hcoord
          }⟩
        exact Or.inr ⟨child, Or.inr (Or.inl hextended),
          Prod.Lex.left _ _ hbudget⟩

/-- Quotient-zero high potential produces coverage while the source clock is
still available, so an earlier blocker is ready debt rather than a broad
historical normal node. -/
theorem zeroQuotient_potential_aboveTarget_refinedStep
    {target n r : Nat}
    (htarget : 0 < target)
    (htimeReady : target ≤ n + 1)
    (hcoord : CoordinatesAt n 0 r)
    (habove : Int.ofNat target ≤ potential 0 r) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  have hvalue : a n = r := by
    simpa [potential, upperTri] using hcoord.eqn
  by_cases hcurrent : a n = target
  · exact Or.inl ⟨n, hcurrent⟩
  have htargetValue : target ≤ a n := by
    rw [hvalue]
    simpa [potential, upperTri] using habove
  have hstrict : target < r := by omega
  rcases coordinates_zeroQuotient_next hcoord with
    ⟨_, hnextCoord, _⟩
  let level := r - 1
  have hpotential : potential 1 r = Int.ofNat level := by
    apply (potential_eq_ofNat_iff 1 r level).mpr
    simp only [level, upperTri]
    omega
  have hseen : level ∈ valuesThrough (n + 2) := by
    simpa only [Nat.add_assoc] using
      (lowQuotient_level_seen_next hnextCoord (by omega) hpotential)
  rcases history_member_has_firstAt hseen with
    ⟨firstTime, _, hfirst⟩
  have hcoverage : CoverageStep target (a n) n :=
    Or.inr ⟨level, firstTime, (by simp only [level]; omega), hfirst,
      (by simp only [level]; omega)⟩
  have hparent : CurrentCoverageParentCertificate target n := {
    target_positive := htarget
    time_ready := htimeReady
    target_le_value := htargetValue
  }
  exact coverageReady_to_refined
    (coverageStep_readyCurrentOrDebt hparent hcoverage)

/-- Quotient-one forced growth also retains the ready current parent until
its two-step coverage candidate has been classified. -/
theorem quotientOne_forcedAddition_refinedStep
    {target n r level : Nat}
    (htarget : 0 < target)
    (htimeReady : target ≤ n + 1)
    (htargetValue : target < a n)
    (hcoord : CoordinatesAt n 1 r)
    (hpotential : potential 1 r = Int.ofNat level)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  have hr : r = 1 + level := by
    simpa [upperTri] using
      (potential_eq_ofNat_iff 1 r level).mp hpotential
  have hvalue : a n = n + 1 + level := by
    have heq := hcoord.eqn
    omega
  have hnext := a_succ_of_not_canSubtract hnot
  let candidate := n + level
  have hcandidate : a (n + 1) - (n + 2) = candidate := by
    simp only [candidate]
    omega
  have htargetCandidate : target ≤ candidate := by
    simp only [candidate]
    by_cases hlevelZero : level = 0
    · subst level
      omega
    · omega
  have hcandidateDrop : candidate < a n := by
    simp only [candidate]
    omega
  have hpositive : n + 2 < a (n + 1) := by
    have : 0 < candidate := Nat.lt_of_lt_of_le htarget htargetCandidate
    omega
  have hcoverage : CoverageStep target (a n) n := by
    by_cases hcanNext : CanSubtract (n + 2) (stateAt (n + 1))
    · have hnextNext := a_succ_of_canSubtract hcanNext
      have hvalueNext : a (n + 2) = candidate :=
        hnextNext.trans hcandidate
      have hfirstCandidate := firstAt_succ_of_canSubtract hcanNext
      exact Or.inr ⟨candidate, n + 2, htargetCandidate,
        by simpa [hvalueNext] using hfirstCandidate, hcandidateDrop⟩
    · rcases not_canSubtract_cases hcanNext with hnonpositive | hseen
      · exact False.elim (by omega)
      · have hcandidateSeen : candidate ∈ valuesThrough (n + 1) := by
          simpa only [hcandidate] using hseen
        rcases history_member_has_firstAt hcandidateSeen with
          ⟨firstTime, _, hfirst⟩
        exact Or.inr ⟨candidate, firstTime, htargetCandidate, hfirst,
          hcandidateDrop⟩
  have hparent : CurrentCoverageParentCertificate target n := {
    target_positive := htarget
    time_ready := htimeReady
    target_le_value := Nat.le_of_lt htargetValue
  }
  exact coverageReady_to_refined
    (coverageStep_readyCurrentOrDebt hparent hcoverage)

/-- The quotient-at-least-two forced-addition frontier, refined at its
coverage, current-forward, and downcross generating branches. -/
theorem forcedAddition_twoQuotient_refinedStep
    {target n q r : Nat}
    (htarget : 0 < target)
    (htimeReady : target ≤ n + 1)
    (htargetValue : target < a n)
    (hcoord : CoordinatesAt n q r)
    (hq : 2 ≤ q)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  rcases coordinates_forcedAddition_twoQuotient_historySearchProgress
      htarget htimeReady (Nat.le_refl _) hcoord hq hnot with
    ⟨value, firstTime, _, htargetAnchor, hfirst, hanchorDrop, _⟩ | hraw
  · have hcoverage : CoverageStep target (a n) n :=
      Or.inr ⟨value, firstTime, htargetAnchor, hfirst, hanchorDrop⟩
    have hparent : CurrentCoverageParentCertificate target n := {
      target_positive := htarget
      time_ready := htimeReady
      target_le_value := Nat.le_of_lt htargetValue
    }
    exact coverageReady_to_refined
      (coverageStep_readyCurrentOrDebt hparent hcoverage)
  · by_cases habove : target ≤ a (n + 2)
    · rcases forcedAdditionForwardAbove_orbitReadyAdapter htarget
          htimeReady habove hraw with ⟨hready, hprogress⟩
      exact Or.inr
        ⟨⟨n + 2, a (n + 2), .normal, a (n + 2)⟩,
          Or.inl (Or.inl hready), hprogress⟩
    · have hbelow : a (n + 2) < target := Nat.lt_of_not_ge habove
      rcases orbit_downcrossing_occurs_or_budgetDrop
          (show n ≤ n + 2 by omega) (Nat.le_of_lt htargetValue) hbelow with
        htargetOccurs | hbudget
      · rcases htargetOccurs with ⟨witness, _, _, hvalue⟩
        exact Or.inl ⟨witness, hvalue⟩
      · let child : PhaseSearchNode :=
          ⟨n + 2, a n, .normal, a n⟩
        have hextended : ExtendedHistoryNormalInvariant target child :=
          ⟨n, q, r, {
            target_positive := htarget
            node_eq := rfl
            representative_le_horizon := by
              simp [child]
            horizon_time_ready := by
              simpa [child] using
                (Nat.le_trans htimeReady (by omega : n + 1 ≤ n + 2 + 1))
            target_le_value := Nat.le_of_lt htargetValue
            coordinates := hcoord
          }⟩
        exact Or.inr ⟨child, Or.inr (Or.inl hextended),
          Prod.Lex.left _ _ hbudget⟩

/-- The exact low-level residual is total in the refined child domain. -/
theorem OrbitReadyLowLevelResidual.refinedStep
    {target : Nat} {parent : PhaseSearchNode}
    (h : OrbitReadyLowLevelResidual target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child parent := by
  cases h with
  | low n q r level hready hlow =>
      have hparentEq := hready.node_eq
      rw [hparentEq] at hready ⊢
      by_cases hcurrent : a n = target
      · exact Or.inl ⟨n, hcurrent⟩
      have habove : target < a n :=
        Nat.lt_of_le_of_ne hlow.target_le_value (Ne.symm hcurrent)
      by_cases hcan : CanSubtract (n + 1) (stateAt n)
      · by_cases hnextAbove : target ≤ a (n + 1)
        · rcases canonicalLegalSubtraction_above_orbitReadyAdapter
              hready.target_positive hlow.time_ready hnextAbove hcan with
            ⟨hchild, hprogress⟩
          exact Or.inr
            ⟨⟨n + 1, a (n + 1), .normal, a (n + 1)⟩,
              Or.inl (Or.inl hchild), hprogress⟩
        · have hbelow : a (n + 1) < target := Nat.lt_of_not_ge hnextAbove
          rcases orbit_downcrossing_occurs_or_budgetDrop
              (show n ≤ n + 1 by omega) hlow.target_le_value hbelow with
            htargetOccurs | hbudget
          · rcases htargetOccurs with ⟨witness, _, _, hvalue⟩
            exact Or.inl ⟨witness, hvalue⟩
          · let child : PhaseSearchNode :=
              ⟨n + 1, a n, .normal, a n⟩
            have hextended : ExtendedHistoryNormalInvariant target child :=
              ⟨n, q, r, {
                target_positive := hready.target_positive
                node_eq := rfl
                representative_le_horizon := by
                  simp [child]
                horizon_time_ready := by
                  simpa [child] using
                    (Nat.le_trans hlow.time_ready
                      (by omega : n + 1 ≤ n + 1 + 1))
                target_le_value := hlow.target_le_value
                coordinates := hlow.coordinates
              }⟩
            exact Or.inr ⟨child, Or.inr (Or.inl hextended),
              Prod.Lex.left _ _ hbudget⟩
      · by_cases hqOne : q = 1
        · subst q
          exact quotientOne_forcedAddition_refinedStep
            hready.target_positive hlow.time_ready habove hlow.coordinates
            hlow.potential_eq hcan
        · have hqPositive := hlow.quotient_positive
          have hqTwo : 2 ≤ q := by omega
          exact forcedAddition_twoQuotient_refinedStep
            hready.target_positive hlow.time_ready habove hlow.coordinates
            hqTwo hcan

/-- Complete sign classification, retaining refined children before the
legacy semantic interface can erase their clock data. -/
theorem OrbitReadyNormalCertificate.refinedStep_or_lowLevel
    {target : Nat} {parent : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target parent time q r) :
    (∃ witness, a witness = target) ∨
      (∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      OrbitReadyLowLevelResidual target parent := by
  have hparentEq := h.node_eq
  rw [hparentEq] at h ⊢
  by_cases hnegative : potential q r < 0
  · exact Or.imp_right Or.inl
      (negativeNormal_refinedStep h.target_positive
        (h.toNormalPhaseInvariantAt hnegative))
  have hnonnegative : 0 ≤ potential q r := by omega
  by_cases habove : Int.ofNat target ≤ potential q r
  · cases q with
    | zero =>
        rcases zeroQuotient_potential_aboveTarget_refinedStep
            h.target_positive h.time_ready h.coordinates habove with
          hoccurs | hchild
        · exact Or.inl hoccurs
        · exact Or.inr (Or.inl hchild)
    | succ q =>
        have htimePositive : 0 < time := by
          by_cases hzero : time = 0
          · subst time
            have htargetZero : target ≤ 0 := by
              simpa [a, stateAt, initial] using h.target_le_value
            exact False.elim
              ((Nat.not_lt_of_ge htargetZero) h.target_positive)
          · omega
        have hcoverage :=
          positiveQuotient_potential_aboveTarget_gives_coverageStep
            htimePositive (by omega) h.time_ready h.coordinates habove
        have hparent : CurrentCoverageParentCertificate target time := {
          target_positive := h.target_positive
          time_ready := h.time_ready
          target_le_value := h.target_le_value
        }
        rcases coverageReady_to_refined
            (coverageStep_readyCurrentOrDebt hparent hcoverage) with
          hoccurs | hchild
        · exact Or.inl hoccurs
        · exact Or.inr (Or.inl hchild)
  · have hbelow : potential q r < Int.ofNat target := by omega
    have hqPositive : 0 < q := by
      cases q with
      | zero =>
          have hvalue : a time = r := by simpa using h.coordinates.eqn
          have hcast : Int.ofNat target ≤ Int.ofNat r :=
            Int.ofNat_le.mpr (by simpa [hvalue] using h.target_le_value)
          have hrTarget : r < target := by
            simpa [potential, upperTri] using hbelow
          have htargetR : target ≤ r := Int.ofNat_le.mp hcast
          omega
      | succ q => omega
    let level := r - upperTri q
    have htri : upperTri q ≤ r :=
      (potential_nonnegative_iff q r).mp hnonnegative
    have hpotential : potential q r = Int.ofNat level := by
      apply (potential_eq_ofNat_iff q r level).mpr
      simp only [level]
      omega
    have hlevelTarget : level < target := by
      rw [hpotential] at hbelow
      exact Int.ofNat_lt.mp hbelow
    by_cases hregular : 3 ≤ level
    · rcases nonnegative_epoch_refinedStep h.target_positive h.time_ready
          h.target_le_value (Nat.le_refl _) hregular hlevelTarget
          h.coordinates hpotential with hoccurs | hchild
      · exact Or.inl hoccurs
      · exact Or.inr (Or.inl hchild)
    · exact Or.inr (Or.inr (.low time q r level h {
        time_ready := h.time_ready
        target_le_value := h.target_le_value
        value_le_anchor := Nat.le_refl _
        coordinates := h.coordinates
        quotient_positive := hqPositive
        potential_eq := hpotential
        level_le_two := by omega
        level_lt_target := hlevelTarget
      }))

/-- Certificate-level refined local totality. -/
theorem OrbitReadyNormalCertificate.refinedStep
    {target : Nat} {parent : PhaseSearchNode} {time q r : Nat}
    (h : OrbitReadyNormalCertificate target parent time q r) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child parent := by
  rcases h.refinedStep_or_lowLevel with hoccurs | hchild | hlow
  · exact Or.inl hoccurs
  · exact Or.inr hchild
  · exact hlow.refinedStep

/-- Orbit-ready current normal nodes have a residual-free refined step. -/
theorem OrbitReadyNormalInvariant.refinedStep
    {target : Nat} {parent : PhaseSearchNode}
    (h : OrbitReadyNormalInvariant target parent) :
    (∃ witness, a witness = target) ∨
      ∃ child, OrbitReadyRefinedInvariant target child ∧
        PhaseSearchProgress target child parent := by
  rcases h with ⟨time, q, r, hcertificate⟩
  exact hcertificate.refinedStep

end Recaman
