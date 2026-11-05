import Recaman.FourLongFinalRayGap
import Recaman.ThirdSTargetProfile
import Recaman.ThirdSShortTwo

namespace Recaman.FourThirdSTargetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The original third-S target is covered for the last two
possible starts, and for the long-final-ray relation q+gap+1<=v. -/
theorem four_third_S_target_free_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (hta : n+h+M+m+L≤t) (htb : t<n+h+M+m+L+s)
    (hshort : n+h+M+m+L+s-t≤2 ∨ n+h+M+m+L+s-t+(j+1)≤v)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t)) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  let R:=j+1
  let a:=n+h+M+m+L
  let q:=a+s-t
  have hq : 1≤q := by dsimp [q,a]; omega
  obtain ⟨hbalance,hsq⟩:=Recaman.ThirdSTargetProfile.actual_third_S_target_profile f a s U v T j t
    hta htb hS3 hA3 hS4 hA4 hgap htarget
  change T+U=R+q+v at hbalance
  have hbal : (T : Int)+(U : Int)=(R : Int)+(q : Int)+(v : Int) := by omega
  have hsqi : ((q : Int)+(v : Int))^2=(R : Int)^2+2*(U : Int)*(v : Int) := by
    simpa only [q,R,Int.natCast_add,Int.natCast_one] using hsq
  by_cases hlong : q+R≤v
  · have hl:=Recaman.ThirdSShortTwo.third_S_target_long_ray (q : Int) (U : Int) (v : Int) (T : Int) (R : Int)
      (by omega) (by omega) (by omega) hbal hsqi
    exact Recaman.FourLongFinalRayGap.four_long_final_ray_gap f n h M m L s U v T j w hw hpre
      hM hL hU hT hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
      (by change R≤v; omega) (by change 2*R≤T; omega)
  change q≤2 ∨ q+R≤v at hshort
  have hqs : q≤2 := by omega
  have hcases:=Recaman.ThirdSShortTwo.third_S_short_two (q : Int) (U : Int)
    (v : Int) (T : Int) (R : Int) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by dsimp [R]; omega) hbal hsqi
  let H:=h+M+m+L+s+U
  let B:=H+v
  let N:=M+L+U
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let E:=cN (EndN f 0) (n+B) T
  change R≤F
  by_cases hf : R≤F
  · exact hf
  exfalso
  obtain ⟨_,hE7,_,hfree,_,hword⟩:=Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
    hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change E≤7 at hE7
  change T+r≤F+E at hfree
  have hET : E≤T := Recaman.ClockCountSaturation.count_le_length (EndN f 0) (n+B) T
  have hNA : cN (fun x=>f x=true) n H=N := by
    have he:=ones_seg_eq_count f n H
    have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
    rw [hhead] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    dsimp [N]
    omega
  have hNcut (hr : r≤3) : N≤2*r+1 := by
    have hh:=positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre)
      (fun k hk hkH=>hpos k hk (by omega)) hr
    change cN (fun x=>f x=true) n H≤2*r+1 at hh
    rwa [hNA] at hh
  rcases hcases with hV|⟨hR2,hU3,_,_⟩
  · omega
  · have hN3:=hNcut (by omega)
    dsimp [N] at hN3
    omega

end Recaman.FourThirdSTargetGap
