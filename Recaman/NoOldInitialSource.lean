import Recaman.FourthSourceFamilies
import Recaman.MomentTargetProfile

namespace Recaman.NoOldInitialSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- A mass-three target after S3 and a gap R-1 excludes initial-S local
sources when the same zero-mass head has at most fifteen S signs and R>=5.
These two bounds are explicit here; this raw lemma is not a full free-gap result. -/
theorem target_initial_S_excluded (u x : List Bool) (hu : BlockWord u)
    (h R i : Nat) (hR : 5≤R)
    (hmz : mass (List.replicate h false++x)=0)
    (hS15 : cntF (List.replicate h false++x)≤15)
    (hkeyTarget : runKey u= -runKey (List.replicate h false++x)-
      12*(cntF (List.replicate h false++x) : Int)-18-2*(R : Int)^2) :
    ¬sourceAt false h (x++List.replicate 3 false) i := by
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
  have hkr : runKey (r++List.replicate 3 false)= -2 := by
    simpa only [r,List.append_assoc] using hkey
  rw [runKey_append_S,hmr] at hkr
  have hdi : (d : Int)+(i : Int)=4 := by
    have hb : mass (r++List.replicate 3 false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hb
    omega
  have hkz : runKey (List.replicate h false++x)=
      runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  have hku : runKey u= -2*(R : Int)^2+2+
      4*(1-(i : Int))*(S+3)-2*(d : Int)^2 := by
    change runKey u= -runKey (List.replicate h false++x)-12*S-18-2*(R : Int)^2 at hkeyTarget
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
  · have hd4 : (d : Int)=4 := by omega
    rw [hi,hd4] at hku
    simp only [Int.natCast_zero] at hku
    grind only
  · have hp:=Int.mul_nonneg (show 0≤(i : Int)-1 by omega)
      (show 0≤S+3 by omega)
    have hq:=Int.sq_nonneg (d : Int)
    grind only

end Recaman.NoOldInitialSource
