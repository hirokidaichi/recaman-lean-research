import Recaman.FourthActualSeven
import Recaman.LowTargetActualCircle
import Recaman.MassOneTargetCounter
import Recaman.MomentTargetProfile

namespace Recaman.MassOneOldTwoGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_one_old_two_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hC : mass (w.drop t)=1)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r))
    (hD : mass (w.drop r)=2)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j 1 w hw hpre ht
    hh hM hm hL hs hU (by omega) rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let free:=cN P n H
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
  have hT : T=v+j := by
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
  have hcost : free+v≤7 := by
    dsimp [free,H,P]
    simp only [Nat.add_assoc]
    omega
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hc:=ones_seg_eq_count f n H
    dsimp [H] at hc ⊢
    rw [hhead] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hpart:=addition_endable_partition f n H
  rw [hAc] at hpart
  have hE : h+m+s+v≤17 := by
    dsimp [free,H,P] at hcost
    simp only [H,Nat.add_assoc] at hhead10 hpart hcost
    omega
  have hc:=Recaman.LowTargetActualCircle.actual_old_two_target_circle f n t h M m L s U v T j 1 w hw hpre ht
    hh hM hm hL hs hU hv rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC r i hr hi hseed hD
  have hR5 : (5 : Int)≤(j : Int)+1 := by have hx:=hb.2.1; omega
  have hsq : (j : Int)+1≤5 := by
    apply Classical.byContradiction
    intro hn
    have hp:=Int.mul_nonneg (show 0≤(j : Int)+1-6 by omega) (show 0≤(j : Int)+1+6 by omega)
    have he : ((j : Int)+1-6)*((j : Int)+1+6)=((j : Int)+1)^2-36 := by grind only
    have hs:=hc.2
    omega
  have hpar:=hc.1
  exact False.elim (by omega)

end Recaman.MassOneOldTwoGap
