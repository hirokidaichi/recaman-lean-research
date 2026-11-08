import Recaman.UnitSNextAFamily

namespace Recaman.TwoSSelectedSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- A residual-two S target and a source from the same unchanged S
interval force the shorter depth one and this exact square. -/
theorem same_S_source_square (x : List Bool) (m R i : Nat) (hR : 2≤R)
    (htarget : runKey (List.replicate 2 false++x)= -2*(R : Int)^2)
    (hsource : sourceAt false m x i) : (R : Int)^2=2*(cntF x : Int)+4 := by
  obtain ⟨k,hk,hkm,hm,hkey⟩:=hsource
  rw [runKey_prepend_S] at hkey htarget
  have hk1 : k=1 := by
    by_cases he : k≤1
    · omega
    · have hp:=Int.mul_nonneg (show 0≤(k : Int)-2 by omega) (show 0≤(cntF x : Int) by omega)
      have hsq:=square_lower (k : Int) 2 (by decide) (by omega)
      have hr:=square_lower (R : Int) 2 (by decide) (by omega)
      grind only
  rw [hk1] at hkey
  grind only

/-- Any such primitive source needs at least sixteen later S signs
once the actual counter has supplied R>=5. -/
theorem same_S_source_floor (x : List Bool) (m R i : Nat) (hR : 5≤R)
    (htarget : runKey (List.replicate 2 false++x)= -2*(R : Int)^2)
    (hsource : sourceAt false m x i) : 16≤cntF x := by
  have hs:=same_S_source_square x m R i (by omega) htarget hsource
  by_cases he : R=5
  · rw [he] at hs
    omega
  · have hh:=square_lower (R : Int) 6 (by decide) (by omega)
    omega

theorem same_S_prefix_saving (x : List Bool) (m R K : Nat) (hR : 5≤R)
    (hF : cntF x≤13)
    (htarget : runKey (List.replicate 2 false++x)= -2*(R : Int)^2) :
    rayCount (List.replicate m false++x) K≤rayCount x K := by
  unfold rayCount
  apply cN_mono
  intro i hi hiK he
  rcases (local_const_split false m x i).mp he with hs|hx
  · have hf:=same_S_source_floor x m R i hR htarget hs
    omega
  · exact hx

theorem R_four_same_S_boundary :
    let x:=List.replicate 1 true++List.replicate 3 false++List.replicate 6 true++List.replicate 3 false
    cntF x=6 ∧ runKey (List.replicate 2 false++x)= -32 ∧ sourceAt false 2 x 1 := by
  dsimp only
  refine ⟨by decide,by decide,1,by decide,by decide,by decide,by decide⟩

theorem sixteen_S_boundary :
    let x:=List.replicate 1 true++List.replicate 8 false++List.replicate 16 true++List.replicate 8 false
    cntF x=16 ∧ runKey (List.replicate 2 false++x)= -72 ∧ sourceAt false 2 x 1 := by
  dsimp only
  refine ⟨by decide,by decide,1,by decide,by decide,by decide,by decide⟩

end Recaman.TwoSSelectedSource
