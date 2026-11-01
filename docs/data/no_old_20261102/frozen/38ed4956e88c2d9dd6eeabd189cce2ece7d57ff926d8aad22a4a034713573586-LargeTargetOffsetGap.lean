import Recaman.TargetOffsetKey
import Recaman.TargetMassKeyComparison
import Recaman.MomentTargetProfile

namespace Recaman.LargeTargetOffsetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Uniform mass-three target gap for every separator v>=6.
The counter supplies its own small head budget; no bounded history
classification or independent free-count hypothesis is used. -/
theorem large_target_offset_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : C+3≤v) (hC4 : 4≤C)
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
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let r:=cN P n H
  let delta:=v-C
  have hdelta : (v : Int)=(C : Int)+(delta : Int) := by dsimp [delta]; omega
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
  have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T+C=v+j+1 := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have hlast:=Recaman.FourthActualSeven.fourth_actual_seven f n h M m L s U v T w hw hpre
    hh hm hs (by omega) hS hA hS2 hA2 hS3 hA3 hS4 hA4
  simp only [H,P,Nat.add_assoc] at hc1 hc2 hp hlast hbad
  have hcost : r+delta≤6 := by
    dsimp [r,H,P,delta]
    simp only [Nat.add_assoc]
    omega
  have hr3 : cN P n H≤3 := by change r≤3; dsimp [delta] at hcost; omega
  have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  have hsml:=positive_r3_additions_free_bound f n 0 H hw hpre0
    (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hr3
  have hAh:=ones_seg_eq_count f n H
  change ones (seg f n (h+M+m+L+s+U))=_ at hAh
  rw [hhead] at hAh
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at hAh
  have hsmall : h+m+s≤2*r+1 := by
    change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hsml
    dsimp [r]
    omega
  have hR : r+1≤j+1 := by
    dsimp [r,H,P,delta]
    simp only [Nat.add_assoc]
    omega
  let B : Int:= -areaW z
  have hkt:=Recaman.MomentTargetProfile.actual_zero_mass_target_key f n t H v T j w z hpre ht rfl hmz B
    (by dsimp [B]; omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz]; dsimp [B]; grind only
  rw [hC,hSz] at hkt
  have hkey : runKey (w.drop t)≤ -runKey z-12*((h : Int)+(m : Int)+(s : Int))-18+
      2*(delta : Int)^2-2*((j+1 : Nat) : Int)^2 := by
    have hex : runKey (w.drop t)= -runKey z-4*(C : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
        2*(v : Int)^2-2*((j : Int)+1)^2 := by
      simp only [Int.natCast_add] at hkt
      grind only
    have hc:=Recaman.TargetMassKeyComparison.target_mass_key_upper (runKey (w.drop t)) (runKey z)
      C ((h : Int)+(m : Int)+(s : Int)) v ((j : Int)+1) delta (by omega) (by omega) hdelta hex
    simpa only [Int.natCast_add,Int.natCast_one] using hc

  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  exact False.elim (Recaman.TargetOffsetKey.target_offset_key_excluded (w.drop t) z hu h M m L s U
    (j+1) delta r hh hM hm hL hs hU (by dsimp [z,H]; exact hhead) hzeroMass (by dsimp [delta]; omega) hcost hsmall hR hkey)

end Recaman.LargeTargetOffsetGap
