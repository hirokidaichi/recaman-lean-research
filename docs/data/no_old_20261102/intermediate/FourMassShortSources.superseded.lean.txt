import Recaman.NoOldInitialSource

namespace Recaman.FourMassShortSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem four_mass_initial_S_zero (u x : List Bool) (hu : BlockWord u)
    (h R i : Nat) (hR : 5≤R)
    (hmz : mass (List.replicate h false++x)=0)
    (hS15 : cntF (List.replicate h false++x)≤15)
    (hkeyTarget : runKey u= -runKey (List.replicate h false++x)-
      16*(cntF (List.replicate h false++x) : Int)-30-2*(R : Int)^2) :
    sourceAt false h (x++List.replicate 5 false) i → i=0 := by
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
  have hkr : runKey (r++List.replicate 5 false)= -2 := by
    simpa only [r,List.append_assoc] using hkey
  rw [runKey_append_S,hmr] at hkr
  have hdi : (d : Int)+(i : Int)=6 := by
    have hb : mass (r++List.replicate 5 false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc,Int.natCast_zero] using hbal
    rw [mass_append,hmr,mass_rep_false] at hb
    omega
  have hkz : runKey (List.replicate h false++x)=
      runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  have hku : runKey u= -2*(R : Int)^2+2+
      4*(2-(i : Int))*(S+5)-2*(d : Int)^2 := by
    change runKey u= -runKey (List.replicate h false++x)-16*S-30-2*(R : Int)^2 at hkeyTarget
    rw [hkz] at hkeyTarget
    grind only
  have hlu : -2≤runKey u := by
    have hh:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hRR:=Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
    (show 0≤(R : Int)+5 by omega)
  have hS0 : 0≤S := by dsimp [S]; omega
  have hSmax : S≤15 := by dsimp [S]; omega
  by_cases hi : i=0
  · exact hi
  by_cases hi1 : i=1
  · have hd4 : (d : Int)=5 := by omega
    rw [hi1,hd4] at hku
    simp only [Int.natCast_one] at hku
    grind only
  · have hp:=Int.mul_nonneg (show 0≤(i : Int)-2 by omega)
      (show 0≤S+4 by omega)
    have hq:=Int.sq_nonneg (d : Int)
    grind only


end Recaman.FourMassShortSources
