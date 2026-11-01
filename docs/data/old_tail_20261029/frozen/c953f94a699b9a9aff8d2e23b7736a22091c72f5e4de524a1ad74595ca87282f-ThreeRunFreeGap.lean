import Recaman.ThreeRunInitialSTargetGap

namespace Recaman.ThreeRunFreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.OldTargetMiddleCharge

open Recaman.ThreeRunInitialSTargetGap Recaman.ThreeRunOldTargetGap

theorem three_run_free_gap (f : Nat → Bool) (n h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j)) :
    j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) := by
  by_cases hgood : j+1≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)
  · exact hgood
  · have hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1 := by omega
    obtain ⟨hAt,t,k,ht,heq,hwin⟩ := he
    have hk : k=n+h+M+m+L+s+T+j-t := by omega
    have hW : Win f t (n+h+M+m+L+s+T+j-t) := by simpa only [hk] using hwin
    have hbefore := Recaman.MiddleSTargetFreeGap.three_run_counterexample_source_before_first_A
      f n h M m L s T j t w hw hpre hM hm hL hs hS hA hS2 hA2 hS3 hA3 hpos hgap
      ⟨hAt,t,k,ht,heq,hwin⟩ hbad hW
    by_cases htn : t<n
    · exact three_run_old_target_free_gap f n t h M m L s T j w hw hpre htn hM hm hL hs hT
        hS hA hS2 hA2 hS3 hA3 (by omega) hpos hgap ⟨hAt,t,k,ht,heq,hwin⟩ hW
    · let q := n+h-t
      have hq : 1≤q := by dsimp [q]; omega
      have hqh : q≤h := by dsimp [q]; omega
      have hsource : n+h-q=t := by dsimp [q]; omega
      have hlen : q+M+m+L+s+T+j=n+h+M+m+L+s+T+j-t := by dsimp [q]; omega
      have hinit : Win f (n+h-q) (q+M+m+L+s+T+j) := by rw [hsource,hlen]; exact hW
      exact three_run_initial_S_target_free_gap f n h q M m L s T j w hw hpre hq hqh hM hm hL hs hT
        hS hA hS2 hA2 hS3 hA3 hpos hgap ⟨hAt,t,k,ht,heq,hwin⟩ hinit

end Recaman.ThreeRunFreeGap
