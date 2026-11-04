import Recaman.MixedSeedParity
import Recaman.MomentTargetProfile

namespace Recaman.MixedActualCircle

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ASourceReuse
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Two actual old windows share an arbitrary mixed head.
The mass1 target suffix is derived from BlockWord, not assumed to end A. -/
theorem actual_mixed_old_two_circle (f : Nat → Bool) (n B t r v T j i : Nat)
    (w z : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hz : seg f n B=z) (ht : t<n) (hr : r<n) (hi : i<T)
    (hC : mass (w.drop t)=1) (hD : mass (w.drop r)=2)
    (hS : ∀ x, n+B≤x → x<n+B+v → f x=false)
    (hA : ∀ k, k<T → f (n+B+v+k)=true)
    (hgap : ∀ x, n+B+v+T≤x → x<n+B+v+T+j → f x=false)
    (hseed : Win f r (n+B+v+i-r)) (htarget : Win f t (n+B+v+T+j-t)) :
    ((j : Int)+1)%2=0 ∧ ((j : Int)+1)^2=2*((cntF z : Int)+(v : Int)) ∧
      runKey (w.drop r)= -2 := by
  have hp1:=Recaman.MomentTargetProfile.actual_target_word_profile f n r B v i 0 w z hpre hr hz hS
    (fun k hk=>hA k (by omega)) (by intros; omega) (by simpa only [Nat.add_zero] using hseed)
  have hp2:=Recaman.MomentTargetProfile.actual_target_word_profile f n t B v T j w z hpre ht hz hS hA hgap htarget
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hrw:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hk1:=source_key_before_gap (w.drop r++z++List.replicate v false) i 0
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hp1.1)
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hp1.2)
  have hseedKey : runKey (w.drop r++z++List.replicate v false)= -2 := by simpa using hk1
  have hk2:=source_key_before_gap (w.drop t++z++List.replicate v false) T j hp2.1 hp2.2
  rw [hu1] at hk2
  simpa only [Int.natCast_add,Int.natCast_one] using
    Recaman.MixedSeedParity.mixed_old_two_circle (w.drop r) z hrw hD v (j+1) hseedKey hk2

end Recaman.MixedActualCircle
