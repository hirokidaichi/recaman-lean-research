import Recaman.PositiveHeadCut
import Recaman.MixedActualCircle
import Recaman.OldSourceKeyOrder

namespace Recaman.PositiveOldExcluded

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem positive_old_counter_excluded (f : Nat → Bool) (n t h M m L s U v T j μ : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hμ : 1≤μ) (hv : v=μ+1)
    (hheadMass : M+L+U=h+m+s+μ)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1)
    (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r)) : False := by
  have hb:=Recaman.PositiveHeadCounter.positive_head_counter f n t h M m L s U v T j μ w hw hpre ht
    hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hcut:=Recaman.PositiveHeadCut.positive_head_cut f n t h M m L s U v T j μ w hw hpre ht
    hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=(μ : Int) := by simp only [z,H,hword,mass_append,mass_rep_false,mass_replicate_A]; omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    rw [hmz,show z.length=H from seg_length f n H] at hc
    dsimp [H] at hc
    omega
  have hAc : cN (fun x=>f x=true) n H=M+L+U := by
    have hc:=ones_seg_eq_count f n H
    dsimp [H] at hc ⊢
    rw [hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hR : 5≤j+1 := hb.2.1
  have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intros; omega) (by simpa only [Nat.add_zero] using (by simpa only [H,Nat.add_assoc] using hseed))
  have hord:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (H+v) i T j
    (by rw [hpre]; exact hw) hr ht (by omega) (by omega)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using (by simpa only [H,Nat.add_assoc] using hseed))
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hdt:=seg_drop f 0 n t (by omega)
  have hdr:=seg_drop f 0 n r (by omega)
  simp only [Nat.zero_add,hpre] at hdt hdr
  have hDlo : 2≤mass (w.drop r) := by rw [←hdt,←hdr,hC] at hord; omega
  have hD : mass (w.drop r)=2 := by
    have he:=hprof.1
    simp only [mass_append,hmz,mass_rep_false,mass_replicate_A] at he
    omega
  have hc:=Recaman.MixedActualCircle.actual_mixed_old_two_circle f n H t r v T j i w z hw hpre rfl ht hr hi hC hD
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using hseed) (by simpa only [H,Nat.add_assoc] using htarget)
  have hh10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hpart:=addition_endable_partition f n H
  rw [hAc] at hpart
  have hfree4:=hcut.2.1
  change cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H≤4 at hfree4
  change cN (EndN f 0) n H≤10 at hh10
  have hE : (cntF z : Int)+(v : Int)≤15 := by rw [hSz]; omega
  have hR6 : (6 : Int)≤(j : Int)+1 := by have he:=hc.1; omega
  have hsquare:=hc.2.1
  have hmul:=Int.mul_nonneg (show 0≤(j : Int)+1-6 by omega) (show 0≤(j : Int)+1+6 by omega)
  grind only

end Recaman.PositiveOldExcluded
