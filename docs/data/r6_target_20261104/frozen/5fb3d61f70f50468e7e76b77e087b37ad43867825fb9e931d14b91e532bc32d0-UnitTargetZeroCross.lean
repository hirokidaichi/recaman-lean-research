import Recaman.UnitTargetPrefixParity

namespace Recaman.UnitTargetZeroCross

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- A literal S-A prefix at the remaining mass-one equality boundary
forces the source to the exact head position and clock. -/
theorem source_zero_cross_boundary (x : List Bool) (h M i T j : Nat)
    (hS : 1≤cntF x) (hj : 2≤j) (hband : T≤i+j) (hM : M≤j+2)
    (hm1 : mass (x++List.replicate i true)=1)
    (ha1 : areaW (x++List.replicate i true)=0)
    (hm2 : mass ([true]++(List.replicate h false++List.replicate M true)++x++
      List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW ([true]++(List.replicate h false++List.replicate M true)++x++
      List.replicate T true++List.replicate j false)=0) :
    M=j+1 ∧ h=j+2 ∧ i+j=T := by
  let b:=List.replicate h false++List.replicate M true
  let d:=(i : Int)+(j : Int)-(T : Int)
  let R:=(j : Int)+1
  let X:=(M : Int)-d
  have hcA : cntF (List.replicate M true)=0 := by
    have hm:=mass_cntF (List.replicate M true)
    rw [mass_replicate_A,List.length_replicate] at hm
    omega
  have hcb : cntF b=h := by dsimp [b]; rw [cntF_append,cntF_replicate_S,hcA]; omega
  have hmb : mass b=(M : Int)-(h : Int) := by dsimp [b]; rw [mass_append,mass_rep_false,mass_replicate_A]; omega
  have hAb : ones b=(M : Int) := by simp only [b,ones_append,ones_replicate_A,ones_replicate_S]; omega
  have hkb : runKey b= -2*(h : Int)^2 := by
    dsimp [b]
    rw [runKey_prepend_S,hcA]
    have hk : runKey (List.replicate M true)=0 := by
      have h:=runKey_append_A ([] : List Bool) M
      simpa using h
    rw [hk]
    omega
  have hmu : mass [true]=1 := by decide
  have hku : runKey [true]=0 := by decide
  have he:=Recaman.SourceCrossSurplus.two_source_cross_identity [true] b x i T j hm1 ha1 hm2 ha2
  rw [hcb,hkb,hAb,hmu,hku] at he
  have hid : X^2=R^2+2*d*(cntF x : Int) := by dsimp [X,R,d]; grind only
  have hm : X=(h : Int)-1 := by
    simp only [mass_append,mass_replicate_A,mass_rep_false,hmu,hmb] at hm1 hm2
    dsimp [X,d]
    omega
  have hd : 0≤d := by dsimp [d]; omega
  have hR : 3≤R := by dsimp [R]; omega
  have hXlo : -1≤X := by omega
  have hMle : (M : Int)≤R+1 := by dsimp [R]; omega
  have hp:=Int.mul_nonneg hd (show 0≤(cntF x : Int) by omega)
  have hXR : R≤X := by
    by_cases hx : R≤X
    · exact hx
    · have hp2:=Int.mul_nonneg (show 0≤R-1-X by omega) (show 0≤R-1+X by omega)
      grind only
  have hd0 : d=0 := by
    by_cases hd0 : d=0
    · exact hd0
    · have hdp:=Int.mul_pos (show 0<d by omega) (show 0<(cntF x : Int) by omega)
      have hXle : X≤R := by dsimp [X]; omega
      have hprod:=Int.mul_nonneg (show 0≤R-X by omega) (show 0≤R+X by omega)
      grind only
  rw [hd0] at hid
  have hXe : X=R := by
    by_cases heq : X=R
    · exact heq
    · have hprod:=Int.mul_nonneg (show 0≤X-R-1 by omega) (show 0≤X+R by omega)
      grind only
  dsimp [X,R,d] at hm hd0 hXe
  omega

end Recaman.UnitTargetZeroCross
