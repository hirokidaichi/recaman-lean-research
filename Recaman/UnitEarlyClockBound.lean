import Recaman.UnitTargetSASProfile
import Recaman.FourthSourceFamilies

namespace Recaman.UnitEarlyClockBound


open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

private theorem split_rep (b : Bool) (N q : Nat) (hq : q≤N) :
    List.replicate N b=List.replicate (N-q) b++List.replicate q b := by
  rw [List.replicate_append_replicate,show N-q+q=N by omega]

private theorem local_profile (x : List Bool) (i : Nat)
    (hm : mass x+(i : Int)=1) (hk : runKey x= -2) :
    mass (x++List.replicate i true)=1 ∧ areaW (x++List.replicate i true)=0 := by
  have hmass : mass (x++List.replicate i true)=1 := by rw [mass_append,mass_replicate_A]; exact hm
  have hkey : runKey (x++List.replicate i true)= -2 := by rw [runKey_append_A]; exact hk
  unfold runKey at hkey
  rw [hmass] at hkey
  exact ⟨hmass,by omega⟩

/-- A positive first-A source clock is pinned by its own same-target
boundary. It is not the refuted target-independent first-ray bound. -/
theorem first_clock_above_separator (x : List Bool) (h M i j v : Nat)
    (hN : 1≤cntF x) (hj : 2≤j) (hM : M≤j+2) (hi : v≤i)
    (hmt : mass ([true]++List.replicate h false++List.replicate M true++x++
      List.replicate (j+v) true++List.replicate j false)=1)
    (hat : areaW ([true]++List.replicate h false++List.replicate M true++x++
      List.replicate (j+v) true++List.replicate j false)=0)
    (he : sourceAt true M x i) : i=v ∧ h=j+2 ∧ M=j+2 := by
  obtain ⟨q,hq,hqM,hbal,hkey⟩:=he
  let y:=List.replicate q true++x
  have hp:=local_profile y i hbal hkey
  have hNy : 1≤cntF y := by simp only [y,cntF_append,cntF_A]; omega
  rw [split_rep true M q hqM] at hmt hat
  have heq:=Recaman.UnitTargetZeroCross.source_zero_cross_boundary y h (M-q) i (j+v) j
    hNy hj (by omega) (by omega) hp.1 hp.2
    (by simpa only [y,List.append_assoc] using hmt)
    (by simpa only [y,List.append_assoc] using hat)
  omega

/-- A positive middle-S source clock forces the other head boundary.
The source's own remaining S count remains positive. -/
theorem middle_clock_above_separator (x : List Bool) (h M m i j v : Nat)
    (hN : 1≤cntF x) (hj : 2≤j) (hM0 : 1≤M) (hM : M≤j+2) (hi : v≤i)
    (hmt : mass ([true]++List.replicate h false++List.replicate M true++List.replicate m false++x++
      List.replicate (j+v) true++List.replicate j false)=1)
    (hat : areaW ([true]++List.replicate h false++List.replicate M true++List.replicate m false++x++
      List.replicate (j+v) true++List.replicate j false)=0)
    (he : sourceAt false m x i) : i=v ∧ h=j+2 ∧ M=j+1 := by
  obtain ⟨q,hq,hqm,hbal,hkey⟩:=he
  let y:=List.replicate q false++x
  let d:=m-q
  have hp:=local_profile y i hbal hkey
  have hNy : 1≤cntF y := by simp only [y,cntF_append,cntF_replicate_S]; omega
  rw [split_rep false m q hqm] at hmt hat
  have htm : mass ([true]++(List.replicate h false++List.replicate M true++List.replicate d false)++y++
      List.replicate (j+v) true++List.replicate j false)=1 := by
    simpa only [d,y,List.append_assoc] using hmt
  have hta : areaW ([true]++(List.replicate h false++List.replicate M true++List.replicate d false)++y++
      List.replicate (j+v) true++List.replicate j false)=0 := by
    simpa only [d,y,List.append_assoc] using hat
  have hd0 : d=0 := by
    by_cases hz : d=0
    · exact hz
    · have hc:=SAS_cross h M d
      have hprod:=Int.mul_pos (show 0<(M : Int) by omega) (show 0<(d : Int) by omega)
      have hcross : 4≤runKey (List.replicate h false++List.replicate M true++List.replicate d false)+
          2*(cntF (List.replicate h false++List.replicate M true++List.replicate d false) : Int)^2 := by
        rw [hc,Int.mul_assoc]
        omega
      have heq:=(Recaman.UnitTargetPrefixParity.unit_target_prefix_cut
        (List.replicate h false++List.replicate M true++List.replicate d false) y i (j+v) j
        hj (by omega) hp.1 hp.2 htm hta).2 hcross
      simp only [ones_append,ones_replicate_S,ones_replicate_A,Int.zero_add,Int.add_zero] at heq
      omega
  rw [hd0] at htm hta
  simp only [List.replicate_zero,List.append_nil] at htm hta
  have heq:=Recaman.UnitTargetZeroCross.source_zero_cross_boundary y h M i (j+v) j
    hNy hj (by omega) hM hp.1 hp.2 htm hta
  omega


end Recaman.UnitEarlyClockBound
