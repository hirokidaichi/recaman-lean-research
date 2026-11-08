import Recaman.TwoSNextASpectrum

namespace Recaman.ThreeSSelectedSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- The two possible same-S depths reduce to depth one and two R/F bands. -/
theorem same_S_depth_spectrum (x : List Bool) (R k : Nat) (hk : 1≤k) (hR : 5≤R)
    (hF : cntF x≤12)
    (htarget : runKey (List.replicate 3 false++x)= -2*(R : Int)^2)
    (hkey : runKey (List.replicate k false++x)= -2) :
    k=1 ∧ ((R=5 ∧ cntF x=4) ∨ (R=7 ∧ cntF x=10)) := by
  rw [runKey_prepend_S] at hkey htarget
  have hk2 : k≤2 := by
    by_cases he : k≤2
    · exact he
    · have hp:=Int.mul_nonneg (show 0≤(k : Int)-3 by omega)
        (show 0≤(k : Int)+3+2*(cntF x : Int) by omega)
      have hr:=square_lower (R : Int) 5 (by decide) (by omega)
      grind only
  have hkc : k=1 ∨ k=2 := by omega
  rcases hkc with he|he
  · rw [he] at hkey
    have hsq : (R : Int)^2=9+4*(cntF x : Int) := by grind only
    have hR7 : R≤7 := by
      by_cases hh : R≤7
      · exact hh
      · have hu:=square_lower (R : Int) 8 (by decide) (by omega)
        omega
    refine ⟨he,?_⟩
    have hc : R=5 ∨ R=6 ∨ R=7 := by omega
    rcases hc with hr|hr|hr
    · rw [hr] at hsq
      exact Or.inl ⟨hr,by omega⟩
    · rw [hr] at hsq
      omega
    · rw [hr] at hsq
      exact Or.inr ⟨hr,by omega⟩
  · rw [he] at hkey
    have hsq : (R : Int)^2=6+2*(cntF x : Int) := by grind only
    have hR5 : R=5 := by
      by_cases hh : R=5
      · exact hh
      · have hu:=square_lower (R : Int) 6 (by decide) (by omega)
        omega
    rw [hR5] at hsq
    omega

theorem R_five_S_boundary :
    let x:=List.replicate 2 true++List.replicate 3 false++List.replicate 4 true++List.replicate 1 false
    cntF x=4 ∧ runKey (List.replicate 3 false++x)= -50 ∧ sourceAt false 3 x 0 := by
  dsimp only
  refine ⟨by decide,by decide,1,by decide,by decide,by decide,by decide⟩

theorem R_seven_S_boundary :
    let x:=List.replicate 5 true++List.replicate 8 false++List.replicate 5 true++List.replicate 2 false
    cntF x=10 ∧ runKey (List.replicate 3 false++x)= -98 ∧ sourceAt false 3 x 2 := by
  dsimp only
  refine ⟨by decide,by decide,1,by decide,by decide,by decide,by decide⟩

end Recaman.ThreeSSelectedSource
