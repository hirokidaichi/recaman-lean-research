import Recaman.OldTargetMiddleCharge

namespace Recaman.ThreeRunOldTargetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.OldTargetMiddleCharge

theorem three_run_old_target_free_gap (f : Nat → Bool) (n t h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hB : 0<h+M+m+L+s+T)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) :
    j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) := by
  by_cases hgood : j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)
  · exact hgood
  · exfalso
    have hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1 := by omega
    have hr := Recaman.OldTargetAreaBudget.old_target_counterexample_band f n t h M m L s T j w hw hpre ht hs
      hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad hwin
    let B2 := h+M+m+L
    let B := B2+s
    let P := fun x => f x=true ∧ ¬EndN f 0 x
    let v := List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false
    have hv : seg f n B=v := by
      have hh := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
        hS hA hS2 hA2 hS3 (by intro i hi; omega)
      simpa only [Nat.add_zero,List.replicate_zero,List.append_nil] using hh
    have hshape := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
    have hword : seg f n (h+M+m+L+s+T+j)=v++List.replicate T true++List.replicate j false := by
      rw [seg_add,show n+(h+M+m+L+s+T)=n+h+M+m+L+s+T by omega,
        seg_false f (n+h+M+m+L+s+T) j hgap,hshape]
    have ho := Recaman.OldTargetAreaBudget.actual_old_target_budget f n t h M m L s T j w hw hpre ht
      (by simpa only [v,List.append_assoc] using hword) hwin
    have hc10 := Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s T w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 hpos
    have hones := ones_seg_eq_count f n (h+M+m+L+s+T)
    rw [hshape] at hones
    simp only [ones_append,ones_replicate_S,ones_replicate_A] at hones
    have hpartall := addition_endable_partition f n (h+M+m+L+s+T)
    have hbudget : M+L+T≤j+10 := by omega
    have hlen : w.length=n := by rw [←hpre,seg_length]
    have hd := seg_drop f 0 n t (by omega)
    simp only [Nat.zero_add] at hd
    rw [hpre] at hd
    have htarget : seg f t (n-t+(B+T+j))=w.drop t++v++List.replicate T true++List.replicate j false := by
      rw [seg_add,show t+(n-t)=n by omega,←hd]
      have hh : seg f n (B+T+j)=v++List.replicate T true++List.replicate j false := hword
      rw [hh]
      simp only [List.append_assoc]
    have hwin' : Win f t (n+B+T+j-t) := by simpa only [B,B2,Nat.add_assoc] using hwin
    have hmass : mass (w.drop t++v++List.replicate T true++List.replicate j false)=1 := by
      rw [←htarget,seg_mass]
      have hh := hwin'.2.1
      rw [show t+(n+B+T+j-t)=n+B+T+j by omega] at hh
      rw [show t+(n-t+(B+T+j))=n+B+T+j by omega]
      omega
    have harea : areaW (w.drop t++v++List.replicate T true++List.replicate j false)=0 := by
      rw [←htarget,←Ar_areaW]
      have hh : n-t+(B+T+j)=n+B+T+j-t := by omega
      rw [hh]
      exact hwin'.2.2
    have hpre3 : seg f 0 (n+B)=w++v := by
      rw [seg_add,show 0+n=n by omega,hpre,hv]
    have hA3' : ∀ i, i<T → f (n+B+i)=true := by
      intro i hi
      simpa only [B,B2,Nat.add_assoc] using hA3 i hi
    have hrun := endable_A_run_count f (n+B) T (w++v) hpre3 hA3'
    have hp3 := addition_endable_partition f (n+B) T
    rw [count_A_run f (n+B) T hA3',hrun] at hp3
    have hhead := Recaman.ThreeRunSupplyBudget.two_run_additions_free_bound f n h M m L w hw hpre
      hS hA hS2 hA2 (by intro k hk hkB; exact hpos k hk (by omega))
    have hsupply := Recaman.ThreeRunSupplyBudget.two_run_supply_of_positive f n h M m L w hw hpre
      hS hA hS2 hA2 (by intro hk; exact hpos _ hk (by omega))
    have hheadword := Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0
      hS hA hS2 hA2 (by intro x hx hx0; omega) (by intro i hi; omega)
    have hheadones := ones_seg_eq_count f n (h+M+m+L)
    have hheadword' : seg f n (h+M+m+L)=List.replicate h false++List.replicate M true++
        List.replicate m false++List.replicate L true := by simpa using hheadword
    rw [hheadword'] at hheadones
    simp only [ones_append,ones_replicate_S,ones_replicate_A] at hheadones
    have hheadpart := addition_endable_partition f n (h+M+m+L)
    have hhead2 : M+L≤2*cN P n B2+1 := by dsimp [P,B2]; omega
    have hhead5 : M+L≤cN P n B2+5 := by dsimp [P,B2]; omega
    have hz : cN P (n+B2) s=0 := by
      apply cN_zero_of
      intro x hx hxs hh
      have hf := hS3 x (by dsimp [B2] at hx; omega) (by dsimp [B2] at hxs; omega)
      exact Bool.noConfusion (hh.1.symm.trans hf)
    have hsplit1 := cN_add P n B2 s
    have hsplit2 := cN_add P n B T
    have hF : cN P n (B+T)=cN P n B2+cN P (n+B) T := by
      change cN P n (B2+s)=cN P n B2+cN P (n+B2) s at hsplit1
      rw [hz] at hsplit1
      change cN P n (B+T)=cN P n B+cN P (n+B) T at hsplit2
      simpa only [B] using hsplit2.trans (by rw [hsplit1]; simp only [Nat.add_zero])
    have hp := old_target_count_charge w hw t h M m L s T j (cN P n B2) (cN P (n+B) T)
      (by omega) hr.2.2.2.1 hm hL hs hM hbudget ho.2.2.2.2
      (by simpa only [v,List.append_assoc] using hmass)
      (by simpa only [v,List.append_assoc] using harea) hhead2 hhead5
      (by simpa only [P,v,List.append_assoc,Nat.add_comm] using Nat.le_of_eq hp3)
    change cN P n (B+T)<j+1 at hbad
    omega

end Recaman.ThreeRunOldTargetGap
