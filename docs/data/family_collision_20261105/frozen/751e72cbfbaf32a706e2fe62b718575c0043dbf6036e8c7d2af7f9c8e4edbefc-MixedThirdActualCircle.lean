import Recaman.MixedSeedParity
import Recaman.MomentTargetProfile

namespace Recaman.MixedThirdActualCircle

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ASourceReuse Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem mass_three_circle (E R k Z : Int)
    (hk : k= -2 ∨ k=0 ∨ k=2) (hZ : k=2*E-2+4*Z)
    (hdiff : -k=8*E+2-2*R^2) : R%2=0 ∧ R^2=4*E ∧ k= -2 ∧ E%2=0 := by
  have heven : R%2=0 := by
    by_cases he : R%2=0
    · exact he
    have ho : R%2=1 := by omega
    obtain ⟨q,hq⟩:=Recaman.OldThreeKeyParity.odd_square_eight R ho
    rw [hq] at hdiff
    rcases hk with hm|hz|hp <;> omega
  let q:=R/2
  have hRq : R=2*q := by dsimp [q]; omega
  have hsquare : R^2=4*q^2 := by rw [hRq]; grind only
  have hminus : k= -2 := by
    rcases hk with hm|hz|hp
    · exact hm
    · rw [hsquare] at hdiff; omega
    · rw [hsquare] at hdiff; omega
  have hcircle : R^2=4*E := by omega
  have hEeven : E%2=0 := by omega
  exact ⟨heven,hcircle,hminus,hEeven⟩

/-- An arbitrary mixed head retains the mass3/mass1 coupled
circle and seed key. Primitive suffix spectrum is used literally. -/
theorem mixed_old_three_circle (u z : List Bool) (hu : BlockWord u)
    (hD : mass u=3) (v R : Nat)
    (hseed : runKey (u++z++List.replicate v false)= -2)
    (htarget : runKey ([true]++z++List.replicate v false)= -2*(R : Int)^2) :
    (R : Int)%2=0 ∧ (R : Int)^2=4*((cntF z : Int)+(v : Int)) ∧ runKey u= -2 ∧
      ((cntF z : Int)+(v : Int))%2=0 := by
  obtain ⟨Z,hZ⟩:=Recaman.MixedSeedParity.mixed_seed_parity u z v hseed
  have hmu : mass [true]=1 := by decide
  have hku : runKey [true]=0 := by decide
  have hs:=hseed
  have ht:=htarget
  rw [runKey_append_S,runKey_append,mass_append,hD] at hs
  rw [runKey_append_S,runKey_append,mass_append,hmu,hku] at ht
  have hdiff : -runKey u=8*((cntF z : Int)+(v : Int))+2-2*(R : Int)^2 := by grind only
  exact mass_three_circle _ _ _ Z (Recaman.MassTwoThreeKeys.mass_three_keys u hu hD) hZ hdiff


/-- Two actual old windows share an arbitrary mixed head.
The mass1 target suffix is derived from BlockWord, not assumed to end A. -/
theorem actual_mixed_old_three_circle (f : Nat → Bool) (n B t r v T j i : Nat)
    (w z : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hz : seg f n B=z) (ht : t<n) (hr : r<n) (hi : i<T)
    (hC : mass (w.drop t)=1) (hD : mass (w.drop r)=3)
    (hS : ∀ x, n+B≤x → x<n+B+v → f x=false)
    (hA : ∀ k, k<T → f (n+B+v+k)=true)
    (hgap : ∀ x, n+B+v+T≤x → x<n+B+v+T+j → f x=false)
    (hseed : Win f r (n+B+v+i-r)) (htarget : Win f t (n+B+v+T+j-t)) :
    ((j : Int)+1)%2=0 ∧ ((j : Int)+1)^2=4*((cntF z : Int)+(v : Int)) ∧
      runKey (w.drop r)= -2 ∧ ((cntF z : Int)+(v : Int))%2=0 := by
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
    mixed_old_three_circle (w.drop r) z hrw hD v (j+1) hseedKey hk2

end Recaman.MixedThirdActualCircle
