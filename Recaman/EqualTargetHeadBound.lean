import Recaman.OffsetHeadBound

namespace Recaman.EqualTargetHeadBound

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- An equal-separator target forces eight head S signs even before a
counter gap lower bound is known. -/
theorem equal_target_head_eight (u z : List Bool) (hu : BlockWord u) (R : Nat)
    (hk : runKey u≤ -runKey z-12*(cntF z : Int)-18-2*(R : Int)^2) :
    8≤cntF z := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hz:=runKey_count_lower z
  have hRR:=Int.sq_nonneg (R : Int)
  by_cases h : 8≤cntF z
  · exact h
  · have hp:=Int.mul_nonneg (show 0≤7-(cntF z : Int) by omega)
      (show 0≤(cntF z : Int)+1 by omega)
    grind only

end Recaman.EqualTargetHeadBound
