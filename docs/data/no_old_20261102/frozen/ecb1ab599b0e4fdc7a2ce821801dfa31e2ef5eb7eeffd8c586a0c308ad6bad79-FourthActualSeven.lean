import Recaman.FourthLocalSix

namespace Recaman.FourthActualSeven

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Every old mass is retained; the common BlockWord costs at most one
additional clock after the actual tail has three S signs. -/
theorem fourth_actual_seven (f : Nat → Bool) (n h M m L s U v T : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hh : 1≤h) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤7 := by
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
  have hl:=Recaman.FourthLocalSix.fourth_local_six h M m L s U v T hv
  suffices hh : cN (EndN f 0) (n+H+v) T≤7 by
    simpa only [H,Nat.add_assoc] using hh
  rw [he]
  simp only [z,H,hz,List.append_assoc] at hb
  omega

end Recaman.FourthActualSeven
