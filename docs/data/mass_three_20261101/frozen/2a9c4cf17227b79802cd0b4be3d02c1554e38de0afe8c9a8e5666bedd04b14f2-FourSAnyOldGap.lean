import Recaman.OldZeroTargetGap
import Recaman.MassThreeOldOneGap
import Recaman.MomentTargetProfile
import Recaman.FourRunSupplySeventeen

namespace Recaman.FourSAnyOldGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunSupplySeventeen Recaman.FourRunTargetArea Recaman.MomentTargetProfile
open Recaman.MomentActualTarget Recaman.OldSourceKeyOrder
open Recaman.ASourceReuse

/-- Target mass at least six is excluded in the old-seeded final-band
branch by original actual counts. No head, gap or old-mass cutoff is input. -/
theorem four_S_any_old_gap (f : Nat → Bool) (n t h M m L s U T j q i sOld kOld : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+4 → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+4+k)=true)
    (hq : 1≤q) (hqv : q≤4) (hi : i<T) (hband : T≤i+j)
    (hgap : ∀ x, n+h+M+m+L+s+U+4+T≤x → x<n+h+M+m+L+s+U+4+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+4+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+4-q) (q+i))
    (hsOld : sOld<n) (hkOld : kOld<T)
    (hseedWin : Win f sOld (n+h+M+m+L+s+U+4+kOld-sOld))
    (hC : mass (w.drop t)=3)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+4+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T)
  · exact hgood
  have hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T)<j+1 := by omega
  let H:=h+M+m+L+s+U
  let S:=h+m+s
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hword:=four_run_word f n h M m L s U 4 T hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=S := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H,S] at *
    omega
  have hsrc:=actual_final_S_source_A_budget f n t h M m L s U 4 T j q i w hw hpre ht
    hM hm hL hs hU (by decide) hq hqv hi hband hword hS4 hA4 hgap htarget hlocal
  have hF4 : 4≤cN P n (H+4+T) := by
    by_cases hf : cN P n (H+4+T)≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 (H+4+T) hw hpre0
        (by simpa only [H,Nat.add_assoc] using hpos) hf
      have hAbound : 2*(j+1)+2≤cN (fun x=>f x=true) n (H+4+T) := by
        simpa only [H,Nat.add_assoc] using hsrc.2.2
      change cN (fun x=>f x=true) n (H+4+T)≤2*cN P n (H+4+T)+1 at hb
      change cN P n (H+4+T)<j+1 at hcounter
      omega
    · omega
  have hj : 2≤j := by change cN P n (H+4+T)<j+1 at hcounter; omega
  have hprof:=actual_target_word_profile f n t H 4 T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hmass:=hprof.1
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hmass
  have hprior:=actual_old_target_prior_clock f n sOld t (H+4) kOld T j
    (by rw [hpre]; exact hw) hsOld ht (by omega) hj
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using hseedWin)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hmTarget:=hmass
  have hTj : T=j+2 := by rw [hC] at hmTarget; omega
  have hkOne : kOld=0 ∨ kOld=1 := by omega
  rcases hkOne with hk0|hk1
  · exact Recaman.OldZeroTargetGap.old_zero_short_target_free_gap f n t h M m L s U 4 T j sOld w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 (by decide)
      hgap htarget hsOld (by simpa only [hk0,Nat.add_zero] using hseedWin) (by simpa using hC) hpos
  · exact Recaman.MassThreeOldOneGap.mass_three_old_one_gap f n t h M m L s U T j sOld w hw hpre ht
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hsOld
      (by simpa only [hk1] using hseedWin) hC hpos

end Recaman.FourSAnyOldGap
