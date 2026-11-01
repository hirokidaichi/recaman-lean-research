import Recaman.EarlyOldFourResidual
import Recaman.EarlyOldSixFree
import Recaman.OldFourThirteenActual
import Recaman.ThirteenSixSources
import Recaman.SmallInversionActual
import Recaman.InversionNineActual

namespace Recaman.EarlyOldFourFree

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.MomentSmallHeadPruning Recaman.OldSeedInversionKey
open Recaman.ASourceReuse

theorem early_old_mass_four_free (f : Nat → Bool) (n h M m L s U v T sOld kOld : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hsOld : sOld<n) (hkOld : kOld<T)
    (hseedWin : Win f sOld (n+h+M+m+L+s+U+v+kOld-sOld))
    (hkTwo : kOld≤2) (hD : 4≤mass (w.drop sOld))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    11≤h+m+s ∧ 5≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U) := by
  have hr:=Recaman.EarlyOldFourResidual.early_old_mass_four_residual f n h M m L s U v T sOld kOld w hw hpre
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hsOld hkOld hseedWin hkTwo hD hpos
  refine ⟨hr.1,?_⟩
  rcases hr.2 with hThirteen|hfree
  · by_cases hD5 : 5≤mass (w.drop sOld)
    · have hh:=Recaman.EarlyOldSixFree.early_old_mass_five_six_free f n h M m L s U v T sOld kOld w hw hpre
        hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hsOld hkOld hseedWin hkTwo hD5 hpos
      omega
    have hD4 : mass (w.drop sOld)=4 := by omega
    have hIb:=Recaman.OldFourThirteenActual.actual_old_four_thirteen f n h M m L s U v T sOld kOld w hw hpre
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hsOld hkOld hseedWin hkTwo hD4 hThirteen
    have hj:=Recaman.ThirteenSixSources.thirteen_joint_four h M m L s U hM hm hL hs (by omega) hIb.1 hIb.2
    have hb:=Recaman.InversionActualBudget.three_run_min_joint_budget f n h M m L s U w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 hM hm hL hpos
    have hm2:=Nat.min_le_right M 2
    have hE8 : cN (EndN f 0) n (h+M+m+L+s+U)≤8 := by omega
    have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
    have hAc:=ones_seg_eq_count f n (h+M+m+L+s+U)
    rw [hhead] at hAc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hAc
    have hp:=addition_endable_partition f n (h+M+m+L+s+U)
    omega
  · exact hfree

end Recaman.EarlyOldFourFree
