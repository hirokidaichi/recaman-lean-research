import Recaman.FourthSourceFamilies

namespace Recaman.OldZeroInitialSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- In a zero-mass head, an old supplier at clock0 excludes every local
source in the initial S run, for every positive final separator length. -/
theorem old_zero_initial_source_exclusion (u x : List Bool) (hu : BlockWord u)
    (h v i : Nat) (hv : 1≤v)
    (hmz : mass (List.replicate h false++x)=0)
    (hS : 1≤cntF (List.replicate h false++x))
    (hmold : mass u-(v : Int)=1)
    (hkold : runKey (u++(List.replicate h false++x)++List.replicate v false)= -2) :
    ¬sourceAt false h (x++List.replicate v false) i := by
  rintro ⟨q,hq,hqh,hbal,hkey⟩
  let d:=h-q
  let r:=List.replicate q false++x
  let S:=(cntF (List.replicate h false++x) : Int)
  have hsplit : List.replicate h false++x=List.replicate d false++r := by
    dsimp [r]
    rw [←List.append_assoc,←List.replicate_add]
    congr 1
    dsimp [d]
    omega
  have hmr : mass r=(d : Int) := by
    rw [hsplit,mass_append,mass_rep_false] at hmz
    omega
  have hcr : (cntF r : Int)=S-(d : Int) := by
    have hc:=cntF_append (List.replicate d false) r
    rw [←hsplit,cntF_replicate_S] at hc
    dsimp [S]
    omega
  have hkeyr : runKey (r++List.replicate v false)= -2 := by
    simpa only [r,List.append_assoc] using hkey
  rw [runKey_append_S,hmr] at hkeyr
  have hdi : (d : Int)+(i : Int)=(v : Int)+1 := by
    have hbalr : mass (r++List.replicate v false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hbalr
    omega
  have hkz : runKey (List.replicate h false++x)=runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  have hD : mass u=(v : Int)+1 := by omega
  rw [runKey_append_S,runKey_append,mass_append,hmz,hkz,hD] at hkold
  have hku : runKey u= -4*(i : Int)*(S+(v : Int))-2*(d : Int)^2 := by
    grind only
  have hlu : -2≤runKey u := by
    have hh:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hS1 : 1≤S := by dsimp [S]; omega
  by_cases hi : i=0
  · have hd2 : 2≤d := by omega
    have hp:=Int.mul_nonneg (show 0≤(d : Int)-2 by omega) (show 0≤(d : Int)+2 by omega)
    rw [hi] at hku
    simp only [Int.natCast_zero,Int.mul_zero,Int.zero_mul,Int.zero_sub] at hku
    grind only
  · have hp:=Int.mul_nonneg (show 0≤(i : Int)-1 by omega) (show 0≤S+(v : Int) by omega)
    have hq:=Int.sq_nonneg (d : Int)
    grind only

end Recaman.OldZeroInitialSource
