import Recaman.MassTwoNoOldLast
import Recaman.MomentNoOld
import Recaman.MassTwoSmallHeadKey
import Recaman.MassTwoTargetCounter
import Recaman.MomentTargetProfile

namespace Recaman.NoOldMassTwoGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Uniform mass-two target gap for every separator v>=5.
The counter supplies its own small head budget; no bounded history
classification or independent free-count hypothesis is used. -/
theorem no_old_mass_two_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : 1≤v)
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
    (hC : mass (w.drop t)=2)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r))
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hb:=Recaman.MassTwoTargetCounter.mass_two_target_counter f n t h M m L s U v T j 2 w hw hpre ht
    hh hM hm hL hs hU (by omega) rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let r:=cN P n H
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
  have hT : T+1=v+j := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have heq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hnoOld)
  have hl:=Recaman.AdjacentRunSupply.fourth_ray_local_le_six h M m L s U v T hv
  have hlast : cN (EndN f 0) (n+H+v) T≤6 := by
    rw [heq]
    simpa only [z,H,hhead,List.append_assoc] using hl
  have hlastV:=Recaman.MassTwoNoOldLast.mass_two_no_old_last_budget f n t h M m L s U v T j 2 w hw hpre ht
    hh hM hm hL hs hU hv rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hnoOld
  simp only [H,P,Nat.add_assoc] at hc1 hc2 hp hlast hbad
  have hcost : r+v≤7 := by
    dsimp [r,H,P]
    simp only [Nat.add_assoc]
    omega
  have hr3 : cN P n H≤3 := by
    change r≤3
    dsimp [r,H,P]
    simp only [Nat.add_assoc] at hlastV
    omega
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
    dsimp [r,H,P]
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
  have hkey : runKey (w.drop t)= -runKey z-8*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
      2*(v : Int)^2-2*((j+1 : Nat) : Int)^2 := by
    simp only [Int.natCast_add,Int.natCast_one]
    grind only
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hlo : -2≤runKey (w.drop t) := by
    have hl:=block_area_quadratic_lower hu
    unfold runKey
    omega
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hheadkey : runKey z=4*K-2*((h : Int)+(m : Int)+(s : Int))^2 := by
    dsimp [z,H]
    rw [hhead,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    dsimp [K]
    grind only
  have hK3 : 3≤K := by
    have hp:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have he : ((M : Int)-1)*((m : Int)+(s : Int))=
      (M : Int)*((m : Int)+(s : Int))-(m : Int)-(s : Int) := by grind only
    have hq:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
    have heq : ((L : Int)-1)*(s : Int)=(L : Int)*(s : Int)-(s : Int) := by grind only
    dsimp [K]
    omega
  have he : runKey (w.drop t)=2*((h : Int)+(m : Int)+(s : Int))^2-4*K-
      8*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by
    rw [hheadkey] at hkey
    simp only [Int.natCast_add,Int.natCast_one] at hkey
    grind only
  exact False.elim (Recaman.MassTwoSmallHeadKey.no_old_small_free_key_excluded
    ((h : Int)+(m : Int)+(s : Int)) (v : Int) ((j : Int)+1) K (r : Int) (runKey (w.drop t))
    (by omega) (by change cN P n H≤3 at hr3; dsimp [r]; omega) (by omega) (by omega) (by omega)
    (by omega) (by have hx:=hb.2.1; omega) (by omega) hlo he)

end Recaman.NoOldMassTwoGap
