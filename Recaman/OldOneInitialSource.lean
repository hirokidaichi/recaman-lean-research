import Recaman.OldFourThirteenKey
import Recaman.FourthSourceFamilies

namespace Recaman.OldOneInitialSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem old_one_initial_source_exclusion (u x : List Bool) (hu : BlockWord u)
    (h i : Nat)
    (hmz : mass (List.replicate h false++x)=0)
    (hS : 11≤cntF (List.replicate h false++x))
    (hmold : mass u=4)
    (hkold : runKey (u++(List.replicate h false++x)++List.replicate 4 false)= -2) :
    ¬sourceAt false h (x++List.replicate 4 false) i := by
  rintro ⟨q,hq,hqh,hbal,hkey⟩
  let d:=h-q
  let r:=List.replicate q false++x
  let S:=(cntF (List.replicate h false++x) : Int)
  have hsplit : List.replicate h false++x=List.replicate d false++r := by
    dsimp [r]
    have hd : d≤h := by dsimp [d]; omega
    have ht : (List.replicate h false).take d=List.replicate d false := by
      rw [List.take_replicate,Nat.min_eq_left hd]
    have hh : (List.replicate h false).drop d=List.replicate q false := by
      rw [List.drop_replicate,show h-d=q by dsimp [d]; omega]
    rw [←ht,←hh,←List.append_assoc,List.take_append_drop]
  have hmr : mass r=(d : Int) := by
    rw [hsplit,mass_append,mass_rep_false] at hmz
    omega
  have hcr : (cntF r : Int)=S-(d : Int) := by
    have hc:=cntF_append (List.replicate d false) r
    rw [←hsplit,cntF_replicate_S] at hc
    dsimp [S]
    omega
  have hkeyr : runKey (r++List.replicate 4 false)= -2 := by
    simpa only [r,List.append_assoc] using hkey
  rw [runKey_append_S,hmr] at hkeyr
  have hdi : (d : Int)+(i : Int)=(4 : Int)+1 := by
    have hbalr : mass (r++List.replicate 4 false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hbalr
    omega
  have hkz : runKey (List.replicate h false++x)=runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  have hD : mass u=4 := hmold
  rw [runKey_append_S,runKey_append,mass_append,hmz,hkz,hD] at hkold
  have hku : runKey u=4*(1-(i : Int))*(S+4)-2*(d : Int)^2 := by grind only
  have hb:=Recaman.OldFourThirteenKey.block_four_key_bounds u hu hmold
  have hS11 : 11≤S := by dsimp [S]; omega
  by_cases hi0 : i=0
  · have hd : d=5 := by omega
    rw [hi0,hd] at hku
    omega
  by_cases hi1 : i=1
  · have hd : d=4 := by omega
    rw [hi1,hd] at hku
    omega
  have hp:=Int.mul_nonneg (show 0≤(i : Int)-2 by omega) (show 0≤S+4 by omega)
  have hq:=Int.sq_nonneg (d : Int)
  grind only

end Recaman.OldOneInitialSource
