import Recaman.TenHeadFirstASource

namespace Recaman.TenHeadLocalBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.TenHeadSourcePruning Recaman.TenHeadFirstASource

private theorem const_no_source (b : Bool) (N K : Nat) (x : List Bool)
    (hn : ∀ i, i<K → ∀ e, 1≤e → e≤N →
      ¬(mass (List.replicate e b++x)+(i : Int)=1 ∧ runKey (List.replicate e b++x)= -2)) :
    rayCount (List.replicate N b++x) K=rayCount x K := by
  apply cN_congr
  intro i _ hi
  let P:=fun y : List Bool=>mass y+(i : Int)=1 ∧ runKey y= -2
  have h1 : Recaman.ThreeNonsuppliedData.localSupply ((List.replicate N b++x)++List.replicate i true)=true ↔
      ∃ t, t<(List.replicate N b++x).length ∧ P ((List.replicate N b++x).drop t) := by
    simpa [P] using localSupply_A_S_iff (List.replicate N b++x) i 0
  have h2 : Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate i true)=true ↔
      ∃ t, t<x.length ∧ P (x.drop t) := by
    simpa [P] using localSupply_A_S_iff x i 0
  rw [h1,exists_drop_append,←h2]
  apply or_iff_right
  rintro ⟨t,ht,hp⟩
  simp only [List.length_replicate] at ht
  apply hn i (by omega) (N-t) (by omega) (by omega)
  simpa only [P,List.drop_replicate] using hp

/-- First-A and second-A source families cannot both contribute in the
first target case. Together with the impossible initial-S family, this
bounds the local supply by four, without enumerating all61 heads. -/
theorem first_case_local_four (h M m L s U : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : h+m+s=10) (hA : M+L+U=10)
    (haz : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -46) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 1 false) 5≤4 := by
  let a:=List.replicate U true++List.replicate 1 false
  let b:=List.replicate s false++a
  let c:=List.replicate L true++b
  let d:=List.replicate m false++c
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF (List.replicate h false++x)=10 := by
    have hc:=mass_cntF (List.replicate h false++x)
    rw [hmz] at hc
    simp only [x,List.length_append,List.length_replicate,Int.natCast_add] at hc
    omega
  have herase:=initial_S_ray_erasure h 1 5 x 46 hmz hSz
    (by simpa only [x,List.append_assoc] using haz) (Or.inl ⟨rfl,rfl⟩)
  have ha : rayCount a 5≤1 := rayCount_A_S_le_one U 1 5 (by decide)
  have hb : rayCount b 5≤2 := by
    have h:=rayCount_const_append false s a 5
    change rayCount b 5≤1+rayCount a 5 at h
    omega
  have hbound : rayCount (List.replicate M true++d) 5≤4 := by
    by_cases hex : ∃ i, i<5 ∧ ∃ e, 1≤e ∧ e≤M ∧
        mass (List.replicate e true++d)+(i : Int)=1 ∧ runKey (List.replicate e true++d)= -2
    · obtain ⟨i,hi,e,he,heM,hbal,hkey⟩:=hex
      have hodd:=first_A_source_odd_separator h M m L s U e i hh hm hL hs hU hS hA he heM hi haz
        (by simpa only [d,c,b,a,List.append_assoc] using hbal)
        (by simpa only [d,c,b,a,List.append_assoc] using hkey)
      have hceq : rayCount c 5=rayCount b 5 := by
        apply const_no_source true L 5 b
        intro k hk e he heL hp
        have hn:=second_A_odd_source_excluded e s U hodd.2.2
        apply hn
        simpa only [b,a,List.append_assoc] using hp.2
      have hd : rayCount d 5≤3 := by
        have h:=rayCount_const_append false m c 5
        change rayCount d 5≤1+rayCount c 5 at h
        omega
      have h:=rayCount_const_append true M d 5
      omega
    · have hdeq : rayCount (List.replicate M true++d) 5=rayCount d 5 := by
        apply const_no_source true M 5 d
        intro i hi e he heM hp
        exact hex ⟨i,hi,e,he,heM,hp.1,hp.2⟩
      have hd:=run_prefix_ray_budget [(false,m),(true,L),(false,s)] a 5
      have hd' : rayCount d 5≤3+rayCount a 5 := by
        simpa only [d,c,b,runWord,List.length_cons,List.length_nil,List.append_nil,
          Nat.reduceAdd,List.append_assoc] using hd
      omega
  have hnorm : rayCount (x++List.replicate 1 false) 5≤4 := by
    simpa only [x,d,c,b,a,List.append_assoc] using hbound
  simp only [x,List.append_assoc] at herase hnorm
  simp only [List.append_assoc] at ⊢
  omega

end Recaman.TenHeadLocalBudget
