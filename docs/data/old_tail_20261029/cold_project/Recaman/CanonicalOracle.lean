import Recaman.NormalComplete
import Recaman.HistoryFrontier

namespace Recaman

/-! # Canonical-start oracle analysis

The current coordinates stored by `TargetStartCertificate` split a canonical
node into the negative, undershoot, and above-target regions.  The history
frontier closes every undershoot level at least three.  Only levels zero,
one, and two remain as an explicit boundary object.
-/

/-- A canonical target-ready state cannot have quotient zero.  Its time is at
most the target, while quotient-zero coordinates would put its value strictly
below that time. -/
theorem targetStartCertificate_quotient_pos
    {target n q r : Nat}
    (hcert : TargetStartCertificate target n)
    (hcoord : CoordinatesAt n q r) :
    0 < q := by
  cases q with
  | zero =>
      have heq := hcoord.eqn
      have hrlt := hcoord.remainder_lt
      simp at heq
      have hnle : n ≤ target := by
        rcases hcert.near_target with hnear | hnear <;> omega
      have hready := hcert.value_ready
      omega
  | succ q => omega

/-- A coverage certificate below the canonical value gives either the target
or a semantic normal child.  The enlarged horizon is intentional: the bare
`CoverageStep` interface does not state that the supplied first occurrence is
inside the old horizon. -/
theorem canonicalCoverage_phaseSemantic
    {target n : Nat}
    (htarget : 0 < target)
    (hcoverage : CoverageStep target (a n) n) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  rcases hcoverage with hoccurs | ⟨value, firstTime, htargetValue,
      hfirst, hvalueDrop⟩
  · exact Or.inl hoccurs
  · by_cases heq : value = target
    · exact Or.inl ⟨firstTime, by simpa [heq] using hfirst.1⟩
    · let child : PhaseSearchNode :=
        ⟨max n firstTime, value, .normal, value⟩
      have hsemantic : PhaseSemanticInvariant target child := .normal
        (firstAt_normalSearchInvariant htarget htargetValue hfirst
          (Nat.le_max_right _ _))
      have hprogress : PhaseSearchProgress target child
          (targetStartNode n) := by
        exact phaseSearchProgress_of_horizonAndAnchor
          (Nat.le_max_left _ _) hvalueDrop
      exact Or.inr ⟨child, hsemantic, hprogress⟩

/-- Embedding of a budget/value pair into the phase rank with its value used
as both anchor and local coordinate. -/
theorem natPairLex_embed_normalValue
    {x y : Nat × Nat}
    (hxy : Prod.Lex Nat.lt Nat.lt x y) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))
      (x.1, (x.2, (SearchPhase.normal.rank, x.2)))
      (y.1, (y.2, (SearchPhase.normal.rank, y.2))) := by
  rcases x with ⟨xbudget, xvalue⟩
  rcases y with ⟨ybudget, yvalue⟩
  cases hxy with
  | left _ _ hbudget => exact Prod.Lex.left _ _ hbudget
  | right _ hvalue =>
      exact Prod.Lex.right _ (Prod.Lex.left _ _ hvalue)

/-- A history-budget step between actual states embeds into phase search when
the child uses its own value as the new anchor. -/
theorem historyBudgetProgress_to_phaseSemanticRank
    {target n t : Nat}
    (hprogress : HistoryBudgetProgress target
      ⟨a t, t⟩ ⟨a n, n⟩) :
    PhaseSearchProgress target
      ⟨t, a t, .normal, a t⟩ (targetStartNode n) := by
  exact natPairLex_embed_normalValue hprogress

/-- A forward history frontier from a canonical node always has a semantic
interpretation.  If its value stays above the target, use that value.  If it
falls below, the actual orbit segment either hits the target or strictly
consumes history budget; in the latter case the certified old value is safely
reused at the new horizon. -/
theorem canonicalHistoryFrontier_phaseSemantic
    {target n t firstTime : Nat}
    (htarget : 0 < target)
    (htargetValue : target ≤ a n)
    (hfirst : FirstAt a (a n) firstTime)
    (hfirstTime : firstTime ≤ n)
    (htime : n < t)
    (hprogress : HistoryBudgetProgress target
      ⟨a t, t⟩ ⟨a n, n⟩) :
    (∃ witness, a witness = target) ∨
      ∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child (targetStartNode n) := by
  by_cases htargetChild : target ≤ a t
  · rcases history_member_has_firstAt (current_mem_valuesThrough t) with
      ⟨ft, hft, hfirstT⟩
    let child : PhaseSearchNode := ⟨t, a t, .normal, a t⟩
    have hsemantic : PhaseSemanticInvariant target child := .normal
      (firstAt_normalSearchInvariant htarget htargetChild hfirstT hft)
    exact Or.inr ⟨child, hsemantic,
      historyBudgetProgress_to_phaseSemanticRank hprogress⟩
  · have hbelow : a t < target := Nat.lt_of_not_ge htargetChild
    rcases orbit_downcrossing_occurs_or_budgetDrop (Nat.le_of_lt htime)
        htargetValue hbelow with hoccurs | hbudget
    · rcases hoccurs with ⟨witness, _, _, hvalue⟩
      exact Or.inl ⟨witness, hvalue⟩
    · let child : PhaseSearchNode := ⟨t, a n, .normal, a n⟩
      have hsemantic : PhaseSemanticInvariant target child := .normal
        (firstAt_normalSearchInvariant htarget htargetValue hfirst
          (Nat.le_trans hfirstTime (Nat.le_of_lt htime)))
      have hphase : PhaseSearchProgress target child
          (targetStartNode n) := Prod.Lex.left _ _ hbudget
      exact Or.inr ⟨child, hsemantic, hphase⟩

/-- Exact unresolved low-level band at a canonical start.  All defining data
is retained, including the canonical certificate and its actual current-time
coordinates. -/
inductive CanonicalLowLevelResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | low
      (orbitTime quotient remainder firstTime level : Nat)
      (parent_eq : parent = targetStartNode orbitTime)
      (certificate : TargetStartCertificate target orbitTime)
      (coordinates : CoordinatesAt orbitTime quotient remainder)
      (current_first : FirstAt a (a orbitTime) firstTime)
      (firstTime_le : firstTime ≤ orbitTime)
      (current_above_target : target < a orbitTime)
      (quotient_positive : 0 < quotient)
      (potential_eq : potential quotient remainder = Int.ofNat level)
      (level_le_two : level ≤ 2)
      (level_lt_target : level < target) :
      CanonicalLowLevelResidual target parent

/-- Complete canonical-node classification with the current APIs.

Negative potential enters the proven negative-normal oracle.  Potential at
or above the target gives immediate coverage.  An undershoot level `g≥3`
uses `nonnegative_epoch_historyFrontier`; its quotient-zero exception is
inconsistent with the canonical certificate, and every forward history step
has a semantic phase interpretation.  The only residual is `g≤2`. -/
theorem targetStartInvariant_phaseSemanticStep_or_lowLevel
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (hstart : TargetStartInvariant target parent) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      CanonicalLowLevelResidual target parent := by
  rcases hstart with ⟨n, rfl, hcert⟩
  rcases hcert.witnesses with ⟨q, r, firstTime, hcoord,
      hfirstTime, hfirst⟩
  have hqpos : 0 < q := targetStartCertificate_quotient_pos hcert hcoord
  by_cases hcurrent : a n = target
  · exact Or.inl ⟨n, hcurrent⟩
  by_cases hnegative : potential q r < 0
  · have hinv : NormalPhaseInvariantAt target (targetStartNode n) n q r := {
      node_eq := rfl
      time_ready := hcert.time_ready
      target_le_value := hcert.value_ready
      value_le_anchor := Nat.le_refl _
      coordinates := hcoord
      negative := hnegative
    }
    rcases negativeNormal_phaseSemanticStep htarget hinv with
      hoccurs | hchild
    · exact Or.inl hoccurs
    · exact Or.inr (Or.inl hchild)
  · have hnonnegative : 0 ≤ potential q r := by omega
    by_cases habove : Int.ofNat target ≤ potential q r
    · have hcoverage :=
        positiveQuotient_potential_aboveTarget_gives_coverageStep
          (show 0 < n by
            have hrlt := hcoord.remainder_lt
            omega)
          hqpos hcert.time_ready hcoord habove
      rcases canonicalCoverage_phaseSemantic htarget hcoverage with
        hoccurs | hchild
      · exact Or.inl hoccurs
      · exact Or.inr (Or.inl hchild)
    · have hbelow : potential q r < Int.ofNat target := by omega
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
      by_cases hlevel : 3 ≤ level
      · rcases nonnegative_epoch_historyFrontier hcert.time_ready hlevel
          hlevelTarget hcoord hpotential with
          hcoverage | hqzero | ⟨t, k, s, hnt, _, _, _, hprogress⟩
        · rcases canonicalCoverage_phaseSemantic htarget hcoverage with
            hoccurs | hchild
          · exact Or.inl hoccurs
          · exact Or.inr (Or.inl hchild)
        · exact False.elim (by omega)
        · rcases canonicalHistoryFrontier_phaseSemantic htarget
              hcert.value_ready hfirst hfirstTime hnt hprogress with
            hoccurs | hchild
          · exact Or.inl hoccurs
          · exact Or.inr (Or.inl hchild)
      · exact Or.inr (Or.inr (.low n q r firstTime level rfl hcert
          hcoord hfirst hfirstTime
          (Nat.lt_of_le_of_ne hcert.value_ready (Ne.symm hcurrent))
          hqpos hpotential (by omega)
          hlevelTarget))

/-- The residual is genuine: the canonical start for target two is time two,
where `a 2 = 3` has quotient one and potential level zero. -/
theorem canonicalLowLevelResidual_two :
    CanonicalLowLevelResidual 2 (targetStartNode 2) := by
  have hfirst : FirstAt a 3 2 := by
    constructor
    · decide
    · intro u hu
      have hcases : u = 0 ∨ u = 1 := by omega
      rcases hcases with h | h <;> subst u <;> decide
  have hcert : TargetStartCertificate 2 2 := {
    near_target := Or.inr rfl
    time_ready := by decide
    value_ready := by decide
    witnesses := ⟨1, 1, 2, ⟨by decide, by decide⟩, by decide, hfirst⟩
  }
  exact .low 2 1 1 2 0 rfl hcert ⟨by decide, by decide⟩ hfirst
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Recaman
