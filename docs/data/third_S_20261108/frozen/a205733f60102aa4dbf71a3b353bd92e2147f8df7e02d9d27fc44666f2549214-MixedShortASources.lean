import Recaman.MixedASQuarterBudget

namespace Recaman.MixedShortASources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- A positive A source depth needs strictly more than twice that depth
in later subtractions, for every mixed future word. -/
theorem A_depth_needs_subtractions (x : List Bool) (a : Nat) (ha : 1≤a)
    (hk : runKey (List.replicate a true++x)= -2) : 2*a+1≤cntF x := by
  rw [runKey_prepend_A] at hk
  have hl:=runKey_count_lower x
  by_cases h : 2*a+1≤cntF x
  · exact h
  · have hp:=Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(cntF x : Int) by omega)
      (show (cntF x : Int)-2*(a : Int)≤0 by omega)
    grind only

/-- No two adjacent S/A families coexist across an A interval of length
at most eight. The entire common mixed future is retained. -/
theorem short_A_S_A_collision (x : List Bool) (m L i j : Nat) (hL : L≤8)
    (hs : sourceAt false m (List.replicate L true++x) i)
    (ha : sourceAt true L x j) : False := by
  obtain ⟨b,hb,hbm,_,hkb⟩:=hs
  obtain ⟨a,ha1,haL,_,hka⟩:=ha
  have hFbound:=A_depth_needs_subtractions x a ha1 hka
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd _ hka
  simp only [cntF_append,Recaman.UnitTargetSASProfile.cntF_A,
    Int.natCast_add,Int.natCast_zero,Int.zero_add] at hodd
  rw [runKey_prepend_S,runKey_prepend_A] at hkb
  rw [runKey_prepend_A] at hka
  simp only [cntF_append,Recaman.UnitTargetSASProfile.cntF_A,
    Int.natCast_add,Int.natCast_zero,Int.zero_add] at hkb
  let d:=(L : Int)-(a : Int)-(b : Int)
  let F:=(cntF x : Int)
  have he : 2*d*F=(b : Int)^2 := by dsimp [d,F]; grind only
  have hF : 3≤F := by dsimp [F]; omega
  have hd : 1≤d := by
    by_cases h : 1≤d
    · exact h
    · have hp:=Int.mul_nonpos_of_nonpos_of_nonneg (show d≤0 by omega) (show 0≤F by omega)
      have hb2:=square_lower (b : Int) 1 (by decide) (by omega)
      grind only
  have hb6 : b≤6 := by dsimp [d] at hd; omega
  rcases (show b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 by omega)
    with hb1|hb2|hb3|hb4|hb5|hb6'
  · have hp : 2*(d*F)=1 := by rw [hb1] at he; grind only
    omega
  · rw [hb2] at he
    have hp:=Int.mul_nonneg (show 0≤d-1 by omega) (show 0≤F by omega)
    grind only
  · have hp : 2*(d*F)=9 := by rw [hb3] at he; grind only
    omega
  · have hd3 : d≤3 := by dsimp [d]; omega
    rw [hb4] at he
    change F%2=1 at hodd
    rcases (show d=1 ∨ d=2 ∨ d=3 by omega) with hd1|hd2|hd3'
    · rw [hd1] at he
      have hF8 : F=8 := by grind only
      omega
    · rw [hd2] at he
      have hF4 : F=4 := by grind only
      omega
    · rw [hd3'] at he
      have hp : 3*F=8 := by grind only
      omega
  · have hp : 2*(d*F)=25 := by rw [hb5] at he; grind only
    omega
  · have hd1 : d=1 := by dsimp [d]; omega
    rw [hb6',hd1] at he
    have hF18 : F=18 := by grind only
    change F%2=1 at hodd
    omega

/-- Length nine admits both families at different clocks. -/
theorem length_nine_joint_witness :
    let x:=List.replicate 3 true++List.replicate 8 false++
      List.replicate 4 true++List.replicate 1 false
    sourceAt false 6 (List.replicate 9 true++x) 0 ∧ sourceAt true 9 x 2 := by
  dsimp only
  exact ⟨⟨6,by decide,by decide,by decide,by decide⟩,
    ⟨1,by decide,by decide,by decide,by decide⟩⟩

end Recaman.MixedShortASources
