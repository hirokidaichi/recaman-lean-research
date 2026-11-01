import Recaman.CanonicalLevelZero
import Recaman.CanonicalLevelOne
import Recaman.CanonicalLevelTwo

namespace Recaman

/-! # Integrated canonical-start oracle

The hidden low level is split proof-relevantly into zero, one, and two.
Level zero is then eliminated by the successor theorem; only the two rigid
forced-addition chambers remain.
-/

/-- Proof-relevant refinement of a low-level residual to level one. -/
inductive CanonicalLowLevelResidual.IsOne
    {target : Nat} {parent : PhaseSearchNode}
    (h : CanonicalLowLevelResidual target parent) : Prop
  | intro
      (orbitTime quotient remainder firstTime : Nat)
      (parent_eq : parent = targetStartNode orbitTime)
      (certificate : TargetStartCertificate target orbitTime)
      (coordinates : CoordinatesAt orbitTime quotient remainder)
      (current_first : FirstAt a (a orbitTime) firstTime)
      (firstTime_le : firstTime ≤ orbitTime)
      (current_above_target : target < a orbitTime)
      (quotient_positive : 0 < quotient)
      (potential_one : potential quotient remainder = Int.ofNat 1)
      (one_lt_target : 1 < target)
      (source_eq : h = .low orbitTime quotient remainder firstTime 1
        parent_eq certificate coordinates current_first firstTime_le
        current_above_target quotient_positive potential_one (by omega)
        one_lt_target) :
      IsOne h

/-- Proof-relevant refinement of a low-level residual to level two. -/
inductive CanonicalLowLevelResidual.IsTwo
    {target : Nat} {parent : PhaseSearchNode}
    (h : CanonicalLowLevelResidual target parent) : Prop
  | intro
      (orbitTime quotient remainder firstTime : Nat)
      (parent_eq : parent = targetStartNode orbitTime)
      (certificate : TargetStartCertificate target orbitTime)
      (coordinates : CoordinatesAt orbitTime quotient remainder)
      (current_first : FirstAt a (a orbitTime) firstTime)
      (firstTime_le : firstTime ≤ orbitTime)
      (current_above_target : target < a orbitTime)
      (quotient_positive : 0 < quotient)
      (potential_two : potential quotient remainder = Int.ofNat 2)
      (two_lt_target : 2 < target)
      (source_eq : h = .low orbitTime quotient remainder firstTime 2
        parent_eq certificate coordinates current_first firstTime_le
        current_above_target quotient_positive potential_two (by omega)
        two_lt_target) :
      IsTwo h

/-- The numeric bound in `CanonicalLowLevelResidual` is exact: its hidden
level is zero, one, or two.  The three alternatives repeat all semantic
evidence needed by the corresponding boundary theorem. -/
theorem CanonicalLowLevelResidual.level_cases
    {target : Nat} {parent : PhaseSearchNode}
    (h : CanonicalLowLevelResidual target parent) :
    h.IsZero ∨ h.IsOne ∨ h.IsTwo := by
  cases h with
  | low n q r firstTime level hparent hcert hcoord hfirst hfirstTime
      habove hqpos hpotential hlevel hlevelTarget =>
      have hcases : level = 0 ∨ level = 1 ∨ level = 2 := by omega
      rcases hcases with hzero | hone | htwo
      · subst level
        exact Or.inl (.intro n q r firstTime hparent hcert hcoord hfirst
          hfirstTime habove hqpos (by simpa using hpotential) hlevelTarget
          (Subsingleton.elim _ _))
      · subst level
        exact Or.inr (Or.inl (.intro n q r firstTime hparent hcert hcoord
          hfirst hfirstTime habove hqpos hpotential hlevelTarget
          (Subsingleton.elim _ _)))
      · subst level
        exact Or.inr (Or.inr (.intro n q r firstTime hparent hcert hcoord
          hfirst hfirstTime habove hqpos hpotential hlevelTarget
          (Subsingleton.elim _ _)))

/-- The only unresolved canonical-start chambers after the complete sign and
low-level analysis. -/
inductive CanonicalForcedResidual
    (target : Nat) (parent : PhaseSearchNode) : Prop
  | level_one
      (residual : CanonicalLevelOneForcedQOneResidual target parent) :
      CanonicalForcedResidual target parent
  | level_two
      (residual : CanonicalLevelTwoForcedResidual target parent) :
      CanonicalForcedResidual target parent

/-- Strongest canonical-start theorem supplied by the current local APIs.

All negative, above-target, and level-at-least-three states close in
`CanonicalOracle`.  Level zero first reduces to the successor residual and
then reaches the target within two steps.  Levels one and two close except
for their exact forced quotient-one chambers. -/
theorem targetStartInvariant_phaseSemanticStep_or_forced
    {target : Nat} (htarget : 0 < target)
    {parent : PhaseSearchNode}
    (hstart : TargetStartInvariant target parent) :
    (∃ witness, a witness = target) ∨
      (∃ child, PhaseSemanticInvariant target child ∧
        PhaseSearchProgress target child parent) ∨
      CanonicalForcedResidual target parent := by
  rcases targetStartInvariant_phaseSemanticStep_or_lowLevel htarget hstart
      with hoccurs | hchild | hlow
  · exact Or.inl hoccurs
  · exact Or.inr (Or.inl hchild)
  · rcases hlow.level_cases with hzero | hone | htwo
    · rcases canonicalLowLevel_zero_phaseSemanticStep_or_successor
          htarget hlow hzero with hoccurs | hchild | hsuccessor
      · exact Or.inl hoccurs
      · exact Or.inr (Or.inl hchild)
      · exact Or.inl (hsuccessor.target_occurs htarget)
    · cases hone with
      | intro n q r firstTime hparent hcert hcoord hfirst hfirstTime
          habove hqpos hpotential _ _ =>
          rcases canonicalLowLevel_levelOne_phaseSemantic_or_forcedQOne
              htarget hparent hcert hcoord hfirst hfirstTime habove hqpos
              hpotential with hoccurs | hchild | hforced
          · exact Or.inl hoccurs
          · exact Or.inr (Or.inl hchild)
          · exact Or.inr (Or.inr (.level_one hforced))
    · cases htwo with
      | intro n q r firstTime hparent hcert hcoord hfirst hfirstTime
          habove hqpos hpotential hlevelTarget _ =>
          rcases canonicalLevelTwo_phaseSemanticStep_or_forcedQOne htarget
              hparent hcert hcoord hfirst hfirstTime habove hqpos hpotential
              hlevelTarget with hoccurs | hchild | hforced
          · exact Or.inl hoccurs
          · exact Or.inr (Or.inl hchild)
          · exact Or.inr (Or.inr (.level_two hforced))

end Recaman
