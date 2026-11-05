import Recaman.ThirdSTargetProfile
import Recaman.FourthSaturationSources

namespace Recaman.ThirdSTargetSaturation

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

/-- Seven counted clocks require a source in the third S separator. -/
theorem seven_needs_third_S (w : List Bool) (hw : BlockWord w) (h M m L s U v T : Nat)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) :
    let z:=List.replicate U true++List.replicate v false
    let y:=runWord [(false,h),(true,M),(false,m),(true,L)]++(List.replicate s false++z)
    7≤rayCount (w++y) T → ∃ i, i<T ∧ sourceAt false s z i := by
  dsimp only
  let z:=List.replicate U true++List.replicate v false
  let pre:=[(false,h),(true,M),(false,m),(true,L)]
  let y:=runWord pre++(List.replicate s false++z)
  change 7≤rayCount (w++y) T → _
  intro h7
  by_cases hex : ∃ i, i<T ∧ sourceAt false s z i
  · exact hex
  exfalso
  have hn : rayCount (List.replicate s false++z) T=rayCount z T := by
    apply cN_congr
    intro i _ hi
    change Recaman.ThreeNonsuppliedData.localSupply ((List.replicate s false++z)++List.replicate i true)=true ↔
      Recaman.ThreeNonsuppliedData.localSupply (z++List.replicate i true)=true
    rw [local_const_split,or_iff_right (fun hsource=>hex ⟨i,hi,hsource⟩)]
  have h1 : rayCount z T≤1 := rayCount_A_S_le_one U v T hv
  have h5:=run_prefix_ray_budget pre (List.replicate s false++z) T
  change rayCount y T≤4+rayCount (List.replicate s false++z) T at h5
  have hS : 3≤cntF y := by
    simp only [y,pre,z,runWord,List.append_nil,cntF_append,cntF_A,cntF_replicate_S]
    omega
  have h6:=block_rayCount_append hw y hS T
  omega

end Recaman.ThirdSTargetSaturation
