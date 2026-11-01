import Recaman.NoOldInitialSource

namespace Recaman.EqualTargetInitialS

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

theorem equal_target_initial_excluded (u x : List Bool) (hu : BlockWord u)
    (h R i v : Nat) (hR : 5≤R) (hv : 4≤v)
    (hmz : mass (List.replicate h false++x)=0)
    (hS15 : cntF (List.replicate h false++x)≤15)
    (hkeyTarget : runKey u= -runKey (List.replicate h false++x)-
      4*(v : Int)*((cntF (List.replicate h false++x) : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) :
    sourceAt false h (x++List.replicate v false) i → False := by
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
  have hkr : runKey (r++List.replicate v false)= -2 := by
    simpa only [r,List.append_assoc] using hkey
  rw [runKey_append_S,hmr] at hkr
  have hdi : (d : Int)+(i : Int)=(v : Int)+1 := by
    have hb : mass (r++List.replicate v false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc,Int.natCast_zero] using hbal
    rw [mass_append,hmr,mass_rep_false] at hb
    omega
  have hkz : runKey (List.replicate h false++x)=
      runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  have hku : runKey u= -2*(R : Int)^2+2+
      4*(1-(i : Int))*(S+(v : Int))-2*(d : Int)^2 := by
    change runKey u= -runKey (List.replicate h false++x)-4*(v : Int)*(S+(v : Int))+2*(v : Int)^2-2*(R : Int)^2 at hkeyTarget
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
  · have hd0 : (d : Int)=(v : Int)+1 := by omega
    rw [hi,hd0] at hku
    have hvp:=Int.mul_nonneg (show 0≤(v : Int)-4 by omega) (show 0≤(v : Int)+4 by omega)
    grind only
  · have hp:=Int.mul_nonneg (show 0≤(i : Int)-1 by omega) (show 0≤S+(v : Int) by omega)
    have hq:=Int.sq_nonneg (d : Int)
    grind only

end Recaman.EqualTargetInitialS
