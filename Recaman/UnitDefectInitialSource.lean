import Recaman.UnitTargetTwoS
import Recaman.FourthSourceFamilies

namespace Recaman.UnitDefectInitialSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem unit_defect_initial_excluded (x : List Bool) (h i T j v : Nat) (hj : 2≤j)
    (hmz : mass (List.replicate h false++x)+1=(v : Int))
    (hmt : mass ([true]++(List.replicate h false++x)++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (hat : areaW ([true]++(List.replicate h false++x)++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    ¬sourceAt false h (x++List.replicate v false) i := by
  rintro ⟨q,hq,hqh,hbal,hkey⟩
  let d:=h-q
  let r:=List.replicate q false++x
  have hsplit : List.replicate h false++x=List.replicate d false++r := by
    dsimp [r]
    have hd : d≤h := by dsimp [d]; omega
    have ht : (List.replicate h false).take d=List.replicate d false := by
      rw [List.take_replicate,Nat.min_eq_left hd]
    have hh : (List.replicate h false).drop d=List.replicate q false := by
      rw [List.drop_replicate,show h-d=q by dsimp [d]; omega]
    rw [←ht,←hh,←List.append_assoc,List.take_append_drop]
  have hmr : mass r=(d : Int)+(v : Int)-1 := by
    rw [hsplit,mass_append,mass_rep_false] at hmz
    omega
  have hlm : mass ((r++List.replicate v false)++List.replicate i true)=1 := by
    simp only [mass_append,hmr,mass_rep_false,mass_replicate_A]
    have hh : mass (r++List.replicate v false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hh
    omega
  have hd2 : d≤2 := by
    rw [mass_append,mass_append,hmr,mass_rep_false,mass_replicate_A] at hlm
    omega
  have hlk : runKey ((r++List.replicate v false)++List.replicate i true)= -2 := by
    rw [runKey_append_A]
    simpa only [r,List.append_assoc] using hkey
  have hla : areaW ((r++List.replicate v false)++List.replicate i true)=0 := by
    unfold runKey at hlk
    rw [hlm] at hlk
    omega
  rw [hsplit] at hmt hat
  exact Recaman.UnitTargetTwoS.two_S_source_excluded (r++List.replicate v false) d i T j hd2 hj hlm hla
    (by simpa only [List.append_assoc] using hmt)
    (by simpa only [List.append_assoc] using hat)

end Recaman.UnitDefectInitialSource
