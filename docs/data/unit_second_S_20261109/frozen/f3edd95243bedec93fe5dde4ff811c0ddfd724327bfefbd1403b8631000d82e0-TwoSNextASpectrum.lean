import Recaman.TwoSecondSCounterCut

namespace Recaman.TwoSNextASpectrum

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- The source's own primitive key and the same residual-two target
leave only two concrete R/F bands, for arbitrary mixed future words. -/
theorem next_A_depth_spectrum (x : List Bool) (L R a : Nat) (ha : 1≤a) (haL : a≤L)
    (hR : 5≤R) (hF : cntF x≤11)
    (htarget : runKey (List.replicate 2 false++(List.replicate L true++x))= -2*(R : Int)^2)
    (hkey : runKey (List.replicate a true++x)= -2) :
    a=L ∧ ((R=5 ∧ cntF x=5 ∧ L≤2) ∨ (R=7 ∧ cntF x=11 ∧ L≤5)) := by
  have hfloor:=Recaman.MixedShortASources.A_depth_needs_subtractions x a ha hkey
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd _ hkey
  simp only [cntF_append,Recaman.UnitTargetSASProfile.cntF_A,Nat.zero_add] at hodd
  rw [runKey_prepend_A] at hkey
  rw [runKey_prepend_S,runKey_prepend_A] at htarget
  simp only [cntF_append,Recaman.UnitTargetSASProfile.cntF_A,Nat.zero_add] at htarget
  have hLa : L≤a+1 := by
    by_cases he : L≤a+1
    · exact he
    · have hp:=Int.mul_nonneg (show 0≤(L : Int)-(a : Int)-2 by omega) (show 0≤(cntF x : Int) by omega)
      have hr:=square_lower (R : Int) 5 (by decide) (by omega)
      grind only
  have hcases : L=a ∨ L=a+1 := by omega
  rcases hcases with he|he
  · have hsq : (R : Int)^2=5+4*(cntF x : Int) := by
      rw [he] at htarget
      grind only
    have hR7 : R≤7 := by
      by_cases he : R≤7
      · exact he
      · have hr:=square_lower (R : Int) 8 (by decide) (by omega)
        omega
    have hc : R=5 ∨ R=6 ∨ R=7 := by omega
    refine ⟨by omega,?_⟩
    rcases hc with hr|hr|hr
    · rw [hr] at hsq
      exact Or.inl ⟨hr,by omega,by omega⟩
    · rw [hr] at hsq
      omega
    · rw [hr] at hsq
      exact Or.inr ⟨hr,by omega,by omega⟩
  · have hsq : (R : Int)^2=5+2*(cntF x : Int) := by
      rw [he] at htarget
      simp only [Int.natCast_add,Int.natCast_one] at htarget
      grind only
    have hR5 : R=5 := by
      by_cases he : R=5
      · exact he
      · have hr:=square_lower (R : Int) 6 (by decide) (by omega)
        omega
    rw [hR5] at hsq
    omega

theorem R_five_A_boundary :
    let x:=List.replicate 4 false++List.replicate 2 true++List.replicate 1 false
    cntF x=5 ∧ runKey (List.replicate 2 false++(List.replicate 2 true++x))= -50 ∧
      sourceAt true 2 x 2 := by
  dsimp only
  refine ⟨by decide,by decide,2,by decide,by decide,by decide,by decide⟩

theorem R_seven_A_boundary :
    let x:=List.replicate 4 false++List.replicate 7 true++List.replicate 7 false
    cntF x=11 ∧ runKey (List.replicate 2 false++(List.replicate 1 true++x))= -98 ∧
      sourceAt true 1 x 4 := by
  dsimp only
  refine ⟨by decide,by decide,1,by decide,by decide,by decide,by decide⟩

end Recaman.TwoSNextASpectrum
