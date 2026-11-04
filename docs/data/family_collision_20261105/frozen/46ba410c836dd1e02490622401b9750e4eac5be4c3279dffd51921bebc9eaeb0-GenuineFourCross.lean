import Recaman.PrimitiveOldTargetCut
import Recaman.SourceFamilyFreeCount
import Recaman.UnitTargetSASProfile
import Recaman.MomentTargetProfile

namespace Recaman.GenuineFourCross

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.UnitTargetSASProfile

/-- Six forced A-before-S pairs contribute24 to the full literal cross. -/
theorem four_cross_twenty_four (h M m L s U v T : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) :
    let z:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++List.replicate T true
    24≤runKey z+2*(cntF z : Int)^2 := by
  dsimp only
  rw [runKey_append_A,runKey_append_S,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
  simp only [cntF_append,cntF_replicate_S,cntF_A,mass_append,mass_rep_false,mass_replicate_A,Int.natCast_add]
  have hp:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int)+(v : Int) by omega)
  have hq:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int)+(v : Int) by omega)
  have hr:=Int.mul_nonneg (show 0≤(U : Int)-1 by omega) (show 0≤(v : Int) by omega)
  grind only

/-- An explicit cross lower bound is retained in the same-target square. -/
theorem primitive_cross_square (u z : List Bool) (hu : BlockWord u) (j : Nat)
    (hm : mass (u++z++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate j false)=0)
    (hcross : 24≤runKey z+2*(cntF z : Int)^2) :
    (mass u)^2+((j : Int)+1)^2+12≤(ones z-((j : Int)+1))^2+1 := by
  let R:=(j : Int)+1
  let C:=mass u
  let S:=(cntF z : Int)
  let X:=S-C
  have hk:=source_key_before_gap (u++z) 0 j (by simpa only [List.replicate_zero,List.append_nil] using hm)
    (by simpa only [List.replicate_zero,List.append_nil] using ha)
  rw [runKey_append] at hk
  have huKey : -2≤runKey u := by have hl:=block_area_quadratic_lower hu; unfold runKey; omega
  have hmass:=mass_eq z
  have hcnt:=cntF_int z
  simp only [mass_append,mass_rep_false] at hm
  have hA : ones z=X+R := by dsimp [X,S,C,R]; omega
  have hid : 2*X^2=2*R^2+runKey u+2*C^2+(runKey z+2*S^2) := by
    dsimp [R,C,S,X]
    grind only
  change 24≤runKey z+2*S^2 at hcross
  have hi : C^2+R^2+12≤X^2+1 := by omega
  have he : ones z-R=X := by omega
  change C^2+R^2+12≤(ones z-R)^2+1
  rw [he]
  exact hi

end Recaman.GenuineFourCross
