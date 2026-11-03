import Recaman.NoOldTargetBounds
import Recaman.ShortTargetHeadBound
import Recaman.TargetMassKeyComparison
import Recaman.ShortCounterFactorBounds

namespace Recaman.MassOneTargetCounter

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.ASourceReuse

theorem mass_one_target_counter (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : 1≤v) (hC1 : C=1)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hC : mass (w.drop t)=(C : Int))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    T+C=v+j+1 ∧ 5≤j+1 ∧ M≤j+2 ∧
      runKey (w.drop t)= -runKey (seg f n (h+M+m+L+s+U))-
        4*(C : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  have hprof:=actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T+C=v+j+1 := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hkt:=actual_zero_mass_target_key f n t H v T j w z hpre ht rfl hmz B
    (by dsimp [B]; omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  rw [hC,hSz] at hkt
  have hkey : runKey (w.drop t)= -runKey z-4*(C : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
      2*(v : Int)^2-2*((j : Int)+1)^2 := by
    simp only [Int.natCast_add] at hkt
    grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hword : seg f n (H+v+T)=z++List.replicate v false++List.replicate T true := by
    rw [seg_add,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
    have hAt : seg f (n+(H+v)) T=List.replicate T true := by
      apply seg_A
      intro x hx hxT
      have ha:=hA4 (x-(n+H+v)) (by omega)
      rw [show n+h+M+m+L+s+U+v+(x-(n+H+v))=x by dsimp [H]; omega] at ha
      exact ha
    rw [hAt]
  have hAc : cN (fun x=>f x=true) n (H+v+T)=h+m+s+T := by
    have hc:=ones_seg_eq_count f n (H+v+T)
    rw [hword] at hc
    have hone : ones z=(h+m+s : Nat) := by
      have hc:=mass_cntF z
      have hm:=mass_eq z
      rw [hmz,hSz] at hc
      rw [hmz] at hm
      omega
    simp only [ones_append,ones_replicate_S,ones_replicate_A,hone] at hc
    omega
  have hlowz:=runKey_count_lower z
  have hlowu : -2≤runKey (w.drop t) := by
    have hl:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hSnonneg : 0≤(h : Int)+(m : Int)+(s : Int) := by omega
  have hR : 5≤j+1 := by
    by_cases hR5 : 5≤j+1
    · exact hR5
    · have hf : cN P n (H+v+T)≤3 := by
        change cN P n (H+v+T)<j+1 at hbad
        omega
      have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 (H+v+T) hw hpre0
        (by simpa only [H,Nat.add_assoc] using hpos) hf
      change cN (fun x=>f x=true) n (H+v+T)≤2*cN P n (H+v+T)+1 at hb
      rw [hAc] at hb
      change cN P n (H+v+T)<j+1 at hbad
      have hSleR : h+m+s+v≤j+1 := by omega
      have hS3 : 3≤h+m+s := by omega
      have hv1 : v=1 := by omega
      have hSval : h+m+s=3 := by omega
      have hj3 : j=3 := by omega
      rw [hSz] at hlowz
      simp only [Int.natCast_add] at hlowz
      rw [hC1,hv1,hj3] at hkey
      have hSi : (h : Int)+(m : Int)+(s : Int)=3 := by omega
      rw [hSi] at hlowz hkey
      change runKey (w.drop t)= -runKey z-46 at hkey
      change -18≤runKey z at hlowz
      omega
  have hbudget : M≤j+2 := by
    have hpreA : seg f 0 (n+h)=w++List.replicate h false := by
      rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
    have hE:=endable_A_run_count f (n+h) M (w++List.replicate h false) hpreA hA
    have hE2:=block_rayCount_after_S hw h M
    have hpartA:=addition_endable_partition f (n+h) M
    rw [count_A_run f (n+h) M hA] at hpartA
    have h1:=cN_add P n h M
    have h2:=cN_add P n (h+M) (m+L+s+U+v+T)
    change cN P n (H+v+T)<j+1 at hbad
    change M=cN (EndN f 0) (n+h) M+cN P (n+h) M at hpartA
    dsimp only [H] at hbad
    simp only [Nat.add_assoc] at h1 h2 hpartA hE hbad
    omega
  exact ⟨hT,hR,hbudget,hkey⟩

end Recaman.MassOneTargetCounter
