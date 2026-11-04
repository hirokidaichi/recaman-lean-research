import Recaman.AdjacentRunSupply
import Recaman.LowOldInitialSources
import Recaman.MomentTargetProfile

namespace Recaman.LowOldActualSix

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- One actual old supplier of mass2 or3 eliminates the initial-S family.
All other old masses remain in the common BlockWord count. -/
theorem low_old_actual_six (f : Nat → Bool) (n h M m L s U v T : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hh : 1≤h) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hzero : M+L+U=h+m+s) (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r))
    (hD : mass (w.drop r)=2 ∨ mass (w.drop r)=3) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤6 := by
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  have hz:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hshape : seg f 0 (n+H+v)=w++(z++List.replicate v false) := by
    rw [show n+H+v=n+(H+v) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
  have hc : 3≤cntF (z++List.replicate v false) := by
    have ha (k : Nat) : cntF (List.replicate k true)=0 := by
      have hh:=mass_cntF (List.replicate k true)
      rw [mass_replicate_A,List.length_replicate] at hh
      omega
    simp only [z,H,hz,cntF_append,cntF_replicate_S,ha]
    omega
  have he:=endable_A_run_count f (n+H+v) T (w++(z++List.replicate v false)) hshape
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hb:=block_rayCount_append hw (z++List.replicate v false) hc T
  have hu:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hseedProfile:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intros; omega) (by simpa only [H,Nat.add_zero,Nat.add_assoc] using hseed)
  have hkey:=Recaman.ASourceReuse.source_key_before_gap (w.drop r++z++List.replicate v false) i 0
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hseedProfile.1)
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hseedProfile.2)
  have hseedKey : runKey (w.drop r++(z++List.replicate v false))= -2 := by
    simpa [List.append_assoc] using hkey
  rw [show z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true from hz] at hseedKey
  have hl:=Recaman.LowOldInitialSources.low_old_local_five (w.drop r) h M m L s U v T hu hD hm hs hv hzero hseedKey
  suffices hh : cN (EndN f 0) (n+H+v) T≤6 by
    simpa only [H,Nat.add_assoc] using hh
  rw [he]
  simp only [z,H,hz,List.append_assoc] at hb hl ⊢
  omega

end Recaman.LowOldActualSix
