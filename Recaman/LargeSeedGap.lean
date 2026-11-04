import Recaman.FourthActualSeven
import Recaman.BoundedOldActualFree
import Recaman.ZeroHeadCounterCost
import Recaman.EarlyOldFourFree

namespace Recaman.LargeSeedGap


open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem large_seed_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hD : 4≤mass (w.drop r))
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let free:=cN P n H
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by simp only [z,H,hword,mass_append,mass_rep_false,mass_replicate_A]; omega
  have hlast:=Recaman.FourthActualSeven.fourth_actual_seven f n h M m L s U v T w hw hpre
    hh hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hcost:=Recaman.ZeroHeadCounterCost.counter_count_cost f n H t v T j 1 7 w z hpre rfl hmz ht hC
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
    (by simpa only [H,Nat.add_assoc] using hbad)
    (by simpa only [H,Nat.add_assoc] using hlast)
  change T+1=v+j+1 ∧ free+v+1≤8 at hcost
  have hfree1 : 1≤free := Recaman.ZeroHeadCounterCost.zero_head_free_pos f n H hmz
    (hpos H (by dsimp [H]; omega) (by dsimp [H]; omega))
  have hv6 : v≤6 := by omega
  have hfree4:=Recaman.BoundedOldActualFree.bounded_old_head_free_four f n h M m L s U v T w hw hpre
    hh hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hzeroMass r i hr hi hseed
    (Or.inr ⟨hD,hv6⟩) hM hL hU (fun k hk hkB=>hpos k hk (by omega))
  change 4≤free at hfree4
  have hpseed:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intros; omega) (by simpa only [H,Nat.add_zero,Nat.add_assoc] using hseed)
  have hmass : mass (w.drop r)+(i : Int)=(v : Int)+1 := by
    have he:=hpseed.1
    simp only [mass_append,hmz,mass_rep_false,mass_replicate_A] at he
    omega
  have hv3 : 3≤v := by omega
  have hvEq : v=3 := by omega
  have hi2 : i≤2 := by omega
  have hf5:=Recaman.EarlyOldFourFree.early_old_mass_four_free f n h M m L s U v T r i w hw hpre
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hr hi hseed hi2 hD
    (fun k hk hkB=>hpos k hk (by omega))
  have h5 : 5≤free := hf5.2
  omega

end Recaman.LargeSeedGap
