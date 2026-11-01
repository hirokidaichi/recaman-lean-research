import Recaman.InitialSTargetCountCharge

namespace Recaman.ThreeRunInitialSTargetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.OldTargetMiddleCharge

open Recaman.InitialSTargetCountCharge Recaman.InitialSTargetBounds

theorem three_run_initial_S_target_free_gap (f : Nat → Bool) (n h q M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hq : 1≤q) (hqh : q≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hwin : Win f (n+h-q) (q+M+m+L+s+T+j)) :
    j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) := by
  by_cases hgood : j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)
  · exact hgood
  · exfalso
    have hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1 := by omega
    have hr := Recaman.ThreeRunSupplyBudget.three_run_free_gap_residual f n h M m L s T j w hw hpre
      hS hA hS2 hA2 hS3 hA3 (by omega) hpos hgap he hbad
    have htargetword := initial_S_source_word f n h q M m L s T j hqh hS hA hS2 hA2 hS3 hA3 hgap
    have hmass : mass (List.replicate q false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1 := by
      rw [←htargetword,seg_mass]
      have hh := hwin.2.1
      omega
    have harea : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0 := by
      rw [←htargetword,←Ar_areaW]
      exact hwin.2.2
    have htarget := initial_S_target_equations q M m L s T j hM hm hmass harea
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
    have hc10 := Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s T w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 hpos
    have hones := ones_seg_eq_count f n (h+M+m+L+s+T)
    rw [hshape] at hones
    simp only [ones_append,ones_replicate_S,ones_replicate_A] at hones
    have hpartall := addition_endable_partition f n (h+M+m+L+s+T)
    have hbudget : M+L+T≤j+10 := by omega
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
      have hh : cN P n B=cN P n B2 := by simpa only [Nat.add_zero] using hsplit1
      rw [hsplit2,hh]
    have hp := initial_S_target_count_charge w hw h q M m L s T j (cN P n B2) (cN P (n+B) T)
      hqh hM hm hL hs (by omega) hbudget hmass harea hhead2 hhead5
      (by simpa only [P,v,List.append_assoc,Nat.add_comm] using Nat.le_of_eq hp3)
    change cN P n (B+T)<j+1 at hbad
    omega

end Recaman.ThreeRunInitialSTargetGap
