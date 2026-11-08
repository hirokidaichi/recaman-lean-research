import Recaman.UnitSecondSCounterCut

namespace Recaman.UnitSNextAFamily

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- A residual-one S target and its immediately following A-source
force the full A depth and R^2=2F+2; the actual counter band excludes it. -/
theorem next_A_source_excluded (x : List Bool) (L R i : Nat) (hR : 5≤R)
    (hF : cntF x≤13)
    (htarget : runKey (List.replicate 1 false++(List.replicate L true++x))= -2*(R : Int)^2) :
    ¬sourceAt true L x i := by
  rintro ⟨a,ha,haL,hm,hkey⟩
  have hFpos:=Recaman.MixedShortASources.A_depth_needs_subtractions x a ha hkey
  rw [runKey_prepend_A] at hkey
  rw [runKey_prepend_S,runKey_prepend_A] at htarget
  simp only [cntF_append,Recaman.UnitTargetSASProfile.cntF_A,Nat.zero_add] at htarget
  have haeq : a=L := by
    by_cases he : a=L
    · exact he
    · have hp:=Int.mul_nonneg (show 0≤(L : Int)-(a : Int)-1 by omega)
        (show 0≤(cntF x : Int) by omega)
      have hr:=square_lower (R : Int) 2 (by decide) (by omega)
      grind only
  rw [haeq] at hkey
  have hsq : (R : Int)^2=2*(cntF x : Int)+2 := by grind only
  by_cases hR5 : R=5
  · rw [hR5] at hsq
    omega
  · have hr:=square_lower (R : Int) 6 (by decide) (by omega)
    omega

/-- Both full source families disappear at once, leaving the unchanged
arbitrary future word rather than resetting a prefix. -/
theorem two_family_saving (x : List Bool) (m L R K : Nat) (hR : 5≤R)
    (hF : cntF x≤13)
    (htarget : runKey (List.replicate 1 false++(List.replicate L true++x))= -2*(R : Int)^2) :
    rayCount (List.replicate m false++(List.replicate L true++x)) K≤rayCount x K := by
  unfold rayCount
  apply cN_mono
  intro i hi hiK he
  rcases (local_const_split false m (List.replicate L true++x) i).mp he with hs|hx
  · exact False.elim (Recaman.UnitSSelectedSource.unit_S_target_excludes_source
      (List.replicate L true++x) m R i (by omega) htarget hs)
  · rcases (local_const_split true L x i).mp hx with ha|hx
    · exact False.elim (next_A_source_excluded x L R i hR hF htarget ha)
    · exact hx

/-- R=4 with seven future S signs is a real primitive-source boundary
for mixed futures; it is not an actual free-gap counterexample. -/
theorem R_four_boundary :
    let x:=List.replicate 3 false++List.replicate 4 true++List.replicate 3 false++
      List.replicate 1 true++List.replicate 1 false
    cntF x=7 ∧ runKey (List.replicate 1 false++(List.replicate 1 true++x))= -32 ∧
      sourceAt true 1 x 2 := by
  dsimp only
  refine ⟨by decide,by decide,1,by decide,by decide,by decide,by decide⟩

end Recaman.UnitSNextAFamily
