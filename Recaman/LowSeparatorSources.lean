import Recaman.FirstATargetSquare

namespace Recaman.LowSeparatorSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.SourceFamilyFreeCount

/-- Same-target exclusion of the initial S family for final S1/S2. -/
theorem low_separator_initial_source_excluded (u x : List Bool) (hu : BlockWord u)
    (h v R i : Nat) (hv : v=1 ∨ v=2) (hR : 1≤R)
    (hmz : mass (List.replicate h false++x)=0)
    (hkeyTarget : runKey u= -runKey (List.replicate h false++x)-
      12*((cntF (List.replicate h false++x) : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) :
    ¬sourceAt false h (x++List.replicate v false) i := by
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
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hb
    omega
  have hkz : runKey (List.replicate h false++x)=
      runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  have hku : runKey u= -2*(R : Int)^2+2+
      4*((d : Int)-3)*(S+(v : Int))-2*(d : Int)^2 := by
    change runKey u= -runKey (List.replicate h false++x)-12*(S+(v : Int))+2*(v : Int)^2-2*(R : Int)^2 at hkeyTarget
    rw [hkz] at hkeyTarget
    grind only
  have hlu : -2≤runKey u := by
    have hh:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hRR:=Int.mul_nonneg (show 0≤(R : Int)-1 by omega)
    (show 0≤(R : Int)+1 by omega)
  have hvpos : 1≤v := by rcases hv with rfl|rfl <;> omega
  have hvmax : v≤2 := by rcases hv with rfl|rfl <;> omega
  have hS0 : 0≤S := by dsimp [S]; omega
  have hd3 : d≤3 := by omega
  by_cases hd : d=3
  · rw [hd] at hku
    grind only
  · have hp:=Int.mul_nonneg (show 0≤2-(d : Int) by omega)
      (show 0≤S+(v : Int) by omega)
    have hq:=Int.sq_nonneg (d : Int)
    grind only

/-- The same target and explicit first-A budget exclude every first-A
source for S1/S2. Actual counter bounds are supplied in a separate core. -/
theorem low_separator_first_A_excluded (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U v R i : Nat) (hv : v=1 ∨ v=2) (hzero : M+L+U=h+m+s) (hbudget : M≤R+1)
    (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2)
    (he : sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i) : False := by
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
  have hd0 : 0≤(M : Int)-(e : Int) := by omega
  have hdR : (M : Int)-(e : Int)≤(R : Int) := by omega
  have hp:=Int.mul_nonneg (show 0≤(R : Int)-((M : Int)-(e : Int)) by omega)
    (show 0≤(R : Int)+((M : Int)-(e : Int)) by omega)
  have hv2 : v≤2 := by rcases hv with rfl|rfl <;> omega
  have hq:=Int.mul_nonneg (show 0≤(i : Int)+2-(v : Int) by omega)
    (show 0≤(h : Int)+(m : Int)+(s : Int) by omega)
  have hr:=Int.sq_nonneg ((i : Int)-1)
  rcases hv with rfl|rfl <;> grind only

end Recaman.LowSeparatorSources
