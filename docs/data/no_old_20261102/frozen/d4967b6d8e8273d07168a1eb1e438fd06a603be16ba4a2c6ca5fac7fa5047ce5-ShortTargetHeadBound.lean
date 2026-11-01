import Recaman.EqualTargetHeadBound

namespace Recaman.ShortTargetHeadBound

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem short_target_head_eight (u z : List Bool) (hu : BlockWord u) (C v R : Nat)
    (hC : 4≤C) (hv : 1≤v) (hvC : v≤C)
    (hk : runKey u= -runKey z-4*(C : Int)*((cntF z : Int)+(v : Int))+
      2*(v : Int)^2-2*(R : Int)^2) : 8≤cntF z := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hz:=runKey_count_lower z
  have hRR:=Int.sq_nonneg (R : Int)
  have hvp:=Int.mul_nonneg (show 0≤(v : Int)-1 by omega)
    (show 0≤2*(C : Int)-(v : Int)-1 by omega)
  have hcp:=Int.mul_nonneg (show 0≤(C : Int)-4 by omega)
    (show 0≤(cntF z : Int) by omega)
  by_cases h : 8≤cntF z
  · exact h
  · have hp:=Int.mul_nonneg (show 0≤(cntF z : Int) by omega)
      (show 0≤7-(cntF z : Int) by omega)
    grind only

end Recaman.ShortTargetHeadBound
