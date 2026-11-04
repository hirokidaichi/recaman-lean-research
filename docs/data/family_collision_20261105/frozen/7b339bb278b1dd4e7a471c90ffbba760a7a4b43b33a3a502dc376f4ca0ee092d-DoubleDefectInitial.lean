import Recaman.UnitTargetTwoS
import Recaman.FourthSourceFamilies

namespace Recaman.DoubleDefectInitial

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- Keep an initial-S source at clock zero instead of assuming it absent.
Only the shared target excludes the d<=2 branches. -/
theorem initial_two_clock_zero (x : List Bool) (h i T j v : Nat) (hj : 2≤j)
    (hmz : mass (List.replicate h false++x)+2=(v : Int))
    (hmt : mass ([true]++(List.replicate h false++x)++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (hat : areaW ([true]++(List.replicate h false++x)++List.replicate v false++
      List.replicate T true++List.replicate j false)=0)
    (he : sourceAt false h (x++List.replicate v false) i) : i=0 := by
  obtain ⟨q,hq,hqh,hbal,hkey⟩:=he
  let d:=h-q
  let r:=List.replicate q false++x
  have hrep : List.replicate h false=List.replicate d false++List.replicate q false := by
    rw [List.replicate_append_replicate,show d+q=h by dsimp [d]; omega]
  have hsplit : List.replicate h false++x=List.replicate d false++r := by
    rw [hrep]; simp only [r,List.append_assoc]
  have hmr : mass r=(d : Int)+(v : Int)-2 := by rw [hsplit,mass_append,mass_rep_false] at hmz; omega
  have hlm : mass ((r++List.replicate v false)++List.replicate i true)=1 := by
    simpa only [r,List.append_assoc,mass_append,mass_replicate_A,Int.add_assoc] using hbal
  have hla : areaW ((r++List.replicate v false)++List.replicate i true)=0 := by
    have hk : runKey ((r++List.replicate v false)++List.replicate i true)= -2 := by
      rw [runKey_append_A]
      simpa only [r,List.append_assoc] using hkey
    unfold runKey at hk
    rw [hlm] at hk
    omega
  have hdi : d+i=3 := by simp only [mass_append,hmr,mass_rep_false,mass_replicate_A] at hlm; omega
  by_cases hd : d≤2
  · rw [hsplit] at hmt hat
    exact False.elim (Recaman.UnitTargetTwoS.two_S_source_excluded (r++List.replicate v false) d i T j
      hd hj hlm hla (by simpa only [List.append_assoc] using hmt)
      (by simpa only [List.append_assoc] using hat))
  · omega

end Recaman.DoubleDefectInitial
