import Recaman.FifthTargetCounter

namespace Recaman.FifthHeadBound

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem target_head_ten_fifth (u z : List Bool) (hu : BlockWord u) (R : Nat) (hR : 5≤R)
    (hkey : runKey u= -runKey z-12*(cntF z : Int)-10-2*(R : Int)^2) :
    10≤cntF z := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hlowz:=runKey_count_lower z
  by_cases hh : 10≤cntF z
  · exact hh
  · have hp:=Int.mul_nonneg (show 0≤9-(cntF z : Int) by omega)
      (show 0≤(cntF z : Int)+3 by omega)
    have hRR:=Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
      (show 0≤(R : Int)+5 by omega)
    grind only


end Recaman.FifthHeadBound
