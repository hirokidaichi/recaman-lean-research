import Recaman.GenuineFourCross

namespace Recaman.FourCrossExact

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse Recaman.UnitTargetSASProfile

/-- Retain the actual four-run AS cross, including the first-run
cost that a uniform head-A lower bound loses. -/
theorem four_cross_exact (h M m L s U v T : Nat) :
    let z:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++List.replicate T true
    runKey z+2*(cntF z : Int)^2 =
      4*(((M : Int)+(L : Int)+(U : Int))*(v : Int)+(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) := by
  dsimp only
  rw [runKey_append_A,runKey_append_S,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
  simp only [cntF_append,cntF_replicate_S,cntF_A,mass_append,mass_rep_false,mass_replicate_A,Int.natCast_add]
  grind only

theorem four_cross_head_first_lower (h M m L s U v T : Nat) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) :
    let z:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++List.replicate T true
    4*((M : Int)+(L : Int)+(U : Int)+2*(M : Int)+(L : Int))≤runKey z+2*(cntF z : Int)^2 := by
  dsimp only
  rw [four_cross_exact]
  have h1:=Int.mul_nonneg (show 0≤(M : Int)+(L : Int)+(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have h2:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
  have h3:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
  grind only

end Recaman.FourCrossExact
