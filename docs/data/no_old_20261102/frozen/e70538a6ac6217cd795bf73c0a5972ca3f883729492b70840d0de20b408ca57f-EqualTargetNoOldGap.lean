import Recaman.EqualTargetNoOldBounds
import Recaman.EqualTargetHeadBound
import Recaman.EqualTargetLocalFour
import Recaman.OffsetHeadBound
import Recaman.EqualTargetLocalFive

namespace Recaman.EqualTargetNoOldGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The no-old v=C, C>=4 full-gap. All R/M/head-free bounds are supplied internally from actual positivity and the same target; no area band or local-band premise. -/
theorem equal_target_no_old_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=C) (hC4 : 4≤C)
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
    (hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hb:=Recaman.EqualTargetNoOldBounds.equal_target_no_old_bounds f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hno hpos hbad
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
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hkt:=Recaman.MomentTargetProfile.actual_zero_mass_target_key f n t H v T j w z hpre ht rfl hmz B
    (by dsimp [B]; omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  rw [hC,hSz] at hkt
  have hkeyB : runKey (w.drop t)=2*B-4*(v : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
      2*(v : Int)^2-2*((j : Int)+1)^2 := by
    have hcV : (C : Int)=(v : Int) := by omega
    simp only [Int.natCast_add] at hkt
    rw [hcV] at hkt
    exact hkt
  have hraw:=Recaman.EqualTargetLocalFive.equal_target_local_five (w.drop t) hu h M m L s U (j+1) T v
    (by omega) hb.2.1 hzeroMass (by omega) (by omega) B (by rw [←hhead]; exact hB)
    (by simpa only [Int.natCast_add,Int.natCast_one] using hkeyB)
  have heq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hno)
  have hlast : cN (EndN f 0) (n+H+v) T≤5 := by
    rw [heq]
    simpa only [z,H,hhead,List.append_assoc] using hraw
  have hbcore:=Recaman.EqualTargetCounter.equal_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hS8:=Recaman.EqualTargetHeadBound.equal_target_head_eight (w.drop t) z hu (j+1)
    (by
      rw [hSz]
      have hk:=hbcore.2.2.2
      simpa only [Int.natCast_add,Int.natCast_one] using hk)
  rw [hSz] at hS8
  have hAh:=ones_seg_eq_count f n H
  change ones (seg f n (h+M+m+L+s+U))=_ at hAh
  rw [hhead] at hAh
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at hAh
  have hfhead : 4≤cN P n H := by
    by_cases hf : cN P n H≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hc:=positive_r3_additions_free_bound f n 0 H hw hpre0
        (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hf
      change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hc
      omega
    · omega
  have hf1:=cN_add P n H v
  have hf2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have hT:=hb.1
  have hfH4 : cN P n H≤4 := by
    change cN P n (H+v+T)<j+1 at hbad
    simp only [Nat.add_assoc] at hf1 hf2 hp hlast hbad
    omega
  have hM6 : M≤6 := by
    have hpreA : seg f 0 (n+h)=w++List.replicate h false := by
      rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
    have hE:=endable_A_run_count f (n+h) M (w++List.replicate h false) hpreA hA
    have hE2:=block_rayCount_after_S hw h M
    have hpartA:=addition_endable_partition f (n+h) M
    rw [count_A_run f (n+h) M hA] at hpartA
    have h1:=cN_add P n h M
    have h2:=cN_add P n (h+M) (m+L+s+U)
    change M=cN (EndN f 0) (n+h) M+cN P (n+h) M at hpartA
    dsimp only [H] at hfH4
    simp only [Nat.add_assoc] at h1 h2 hpartA hE hfH4
    omega
  have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hraw4:=Recaman.EqualTargetLocalFour.equal_target_local_four (w.drop t) hu C hC hC4
    h M m L s U v T j T hh hv hT hb.2.1 hM6 hzeroMass (by omega) B
    (by rw [←hhead]; exact hB) hkeyB
    (by simpa only [z,H,hhead,List.append_assoc] using hprof.1)
    (by simpa only [z,H,hhead,List.append_assoc] using hprof.2)
  have hlast4 : cN (EndN f 0) (n+H+v) T≤4 := by
    rw [heq]
    simpa only [z,H,hhead,List.append_assoc] using hraw4
  change j+1≤cN P n (H+v+T)
  simp only [Nat.add_assoc] at hf1 hf2 hp hlast4 ⊢
  omega

end Recaman.EqualTargetNoOldGap
