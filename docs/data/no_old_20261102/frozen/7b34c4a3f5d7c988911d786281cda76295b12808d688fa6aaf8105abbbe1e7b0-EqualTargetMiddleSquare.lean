import Recaman.SourceCrossSurplus
import Recaman.LowSeparatorCounterMiddle

namespace Recaman.EqualTargetMiddleSquare

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

private theorem prefix_square_impossible (M R d h C : Nat) (p ku V : Int)
    (hM : M≤6) (hR : 5≤R) (hC : 4≤C) (hh : 1≤h)
    (hp : 0≤p) (hV : 0≤V) (hklo : -2≤ku)
    (hmass : (M : Int)-p=(h : Int)+(d : Int)-(C : Int))
    (hid : 2*((M : Int)-p)^2=2*(R : Int)^2+ku+2*(C : Int)^2-2+
      4*(M : Int)*(d : Int)+4*p*V) : False := by
  have hRR:=Int.mul_nonneg (show 0≤(R : Int)-5 by omega) (show 0≤(R : Int)+5 by omega)
  have hCC:=Int.mul_nonneg (show 0≤(C : Int)-4 by omega) (show 0≤(C : Int)+4 by omega)
  have hMd:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(d : Int) by omega)
  have hpV:=Int.mul_nonneg hp hV
  by_cases hx : 0≤(M : Int)-p
  · have hXX:=Int.mul_nonneg (show 0≤6-((M : Int)-p) by omega) (show 0≤6+((M : Int)-p) by omega)
    grind only
  · have hXX:=Int.mul_nonneg (show 0≤(C : Int)-1+((M : Int)-p) by omega)
      (show 0≤(C : Int)-1-((M : Int)-p) by omega)
    grind only

/-- The same target and middle-S source retain the complete prefix
cross term 4*M*(m-q). The critical M6/R5 bounds then exclude every q,
including q=m, without enumerating heads or bounding the old history. -/
theorem equal_target_middle_positive_excluded (u : List Bool) (hu : BlockWord u) (C : Nat) (hcu : mass u=(C : Int)) (hC4 : 4≤C)
    (h M m L s U v T j i q : Nat) (hh : 1≤h) (hM6 : M≤6)
    (hR5 : 5≤j+1) (hi : 1≤i) (hv : v=C) (hT : T=j+1)
    (hq : 1≤q) (hqm : q≤m)
    (hm : mass (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)+(i : Int)=1)
    (hk : runKey (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)= -2)
    (hmt : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (hat : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) : False := by
  let d:=m-q
  let p : Int:=(i : Int)+(j : Int)-(T : Int)
  let b:=List.replicate h false++List.replicate M true++List.replicate d false
  let x:=List.replicate q false++List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hsrep : List.replicate m false=List.replicate d false++List.replicate q false := by
    rw [List.replicate_append_replicate]
    congr 1
    dsimp [d]
    omega
  have hcat : b++x=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false := by
    simp only [b,x,hsrep,List.append_assoc]
  have hlmass : mass (x++List.replicate i true)=1 := by
    rw [mass_append,mass_replicate_A]
    exact hm
  have hlkey : runKey (x++List.replicate i true)= -2 := by
    rw [runKey_append_A]
    exact hk
  have hlarea : areaW (x++List.replicate i true)=0 := by
    unfold runKey at hlkey
    rw [hlmass] at hlkey
    omega
  have he:=Recaman.SourceCrossSurplus.two_source_cross_identity u b x i T j hlmass hlarea
    (by rw [List.append_assoc u b x,hcat]; simpa only [List.append_assoc] using hmt)
    (by rw [List.append_assoc u b x,hcat]; simpa only [List.append_assoc] using hat)
  have hon : ones b=(M : Int) := by simp [b,ones_append]
  have hcntFA : cntF (List.replicate M true)=0 := by
    have hc:=mass_cntF (List.replicate M true)
    rw [mass_replicate_A,List.length_replicate] at hc
    omega
  have hcb : cntF b=h+d := by simp [b,cntF_append,cntF_replicate_S,hcntFA]
  have hcross : runKey b+2*(cntF b : Int)^2=4*(M : Int)*(d : Int) := by
    change runKey (List.replicate h false++List.replicate M true++List.replicate d false)+2*(cntF b : Int)^2=_
    rw [runKey_S_A_S,hcb]
    grind only
  have hp : 0≤p := by
    dsimp [p]
    omega
  have hmass : (M : Int)-p=(h : Int)+(d : Int)-(C : Int) := by
    have h1:=hm
    have h2:=hmt
    simp only [mass_append,mass_rep_false,mass_replicate_A,hcu] at h1 h2
    have hd : (d : Int)=(m : Int)-(q : Int) := by dsimp [d]; omega
    dsimp [p]
    omega
  have hklo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  rw [hon,hcu,hcross] at he
  have hid : 2*((M : Int)-p)^2=2*((j+1 : Nat) : Int)^2+runKey u+2*(C : Int)^2-2+
      4*(M : Int)*(d : Int)+4*p*(cntF x : Int) := by
    dsimp [p]
    grind only
  exact prefix_square_impossible M (j+1) d h C p (runKey u) (cntF x : Int)
    hM6 hR5 hC4 hh hp (by omega) hklo hmass hid

end Recaman.EqualTargetMiddleSquare
