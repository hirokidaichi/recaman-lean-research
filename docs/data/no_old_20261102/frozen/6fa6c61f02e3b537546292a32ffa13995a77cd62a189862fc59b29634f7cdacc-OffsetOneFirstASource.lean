import Recaman.FourthSourceFamilies
import Recaman.MomentTargetProfile

namespace Recaman.OffsetOneFirstASource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.SourceFamilyFreeCount

/-- The same target compares two squares directly, avoiding an enumeration
of head areas or lengths. The A budget is explicit in this raw lemma. -/
theorem offset_one_first_A_one (u : List Bool) (hu : BlockWord u)
    (h M m L s U R i v : Nat) (hv : 5≤v) (hzero : M+L+U=h+m+s) (hbudget : M≤R+1)
    (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-4*((v : Int)-1)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2)
    (he : sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i) : i≤1 := by
  obtain ⟨e,he,heM,hbal,hkey⟩:=he
  have hUval : (U : Int)=(h : Int)+(m : Int)+(s : Int)-(M : Int)-(L : Int) := by omega
  rw [runKey_append_A,runKey_five_runs] at hB
  have hkey0 : runKey ((List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true)++List.replicate v false)= -2 := by
    simpa only [List.append_assoc] using hkey
  rw [runKey_append_S,runKey_append_A] at hkey0
  have hke:=runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append] at hke
  rw [hke] at hkey0
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hkey0 hbal
  have hbal0 : (h : Int)=(M : Int)-(e : Int)+(v : Int)+1-(i : Int) := by omega
  have hid : ((M : Int)-(e : Int))^2=
      B-2*((v : Int)+1)*((h : Int)+(m : Int)+(s : Int))+2*(i : Int)*((h : Int)+(m : Int)+(s : Int))+
        (i : Int)^2-2*(i : Int) := by
    rw [hUval] at hkey0 hbal
    rw [hbal0] at hB hkey0 ⊢
    grind only
  have hlow : -2≤runKey u := by
    have hh:=block_area_quadratic_lower hu
    unfold runKey
    omega
  by_cases hi : i≤1
  · exact hi
  have hd0 : 0≤(M : Int)-(e : Int) := by omega
  have hdR : (M : Int)-(e : Int)≤(R : Int) := by omega
  have hp:=Int.mul_nonneg (show 0≤(R : Int)-((M : Int)-(e : Int)) by omega)
    (show 0≤(R : Int)+((M : Int)-(e : Int)) by omega)
  have hq:=Int.mul_nonneg (show 0≤(i : Int)-2 by omega)
    (show 0≤(h : Int)+(m : Int)+(s : Int) by omega)
  have hr:=Int.mul_nonneg (show 0≤(i : Int) by omega) (show 0≤(i : Int)-2 by omega)
  have hvp:=Int.mul_nonneg (show 0≤(v : Int)-5 by omega) (show 0≤(v : Int)+3 by omega)
  grind only

end Recaman.OffsetOneFirstASource
