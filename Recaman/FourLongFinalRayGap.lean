import Recaman.FourMeasuredCounts
import Recaman.FinalSSmallHeadCaps
import Recaman.MixedFinalRayOldBudget

namespace Recaman.FourLongFinalRayGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Long final S and A runs already force the required free count,
independent of where a target starts. -/
theorem four_long_final_ray_gap (f : Nat → Bool) (n h M m L s U v T j : Nat)
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
    (hV : j+1≤v) (hTlen : 2*(j+1)≤T) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  let H:=h+M+m+L+s+U
  let B:=H+v
  let R:=j+1
  let N:=M+L+U
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let E:=cN (EndN f 0) (n+B) T
  change R≤F
  by_cases hf : R≤F
  · exact hf
  exfalso
  have hF : F≤R-1 := by omega
  obtain ⟨_,hE7,_,hfree,_,hword⟩:=Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
    hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change E≤7 at hE7
  change T+r≤F+E at hfree
  have hE_T : E≤T := Recaman.ClockCountSaturation.count_le_length (EndN f 0) (n+B) T
  change 2*R≤T at hTlen
  change R≤v at hV
  have hr2 : r≤2 := by omega
  have hNcut := positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre)
    (fun k hk hkH=>hpos k hk (by omega)) (show r≤3 by omega)
  change cN (fun x=>f x=true) n H≤2*r+1 at hNcut
  have hNA : cN (fun x=>f x=true) n H=N := by
    have he:=ones_seg_eq_count f n H
    have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
    rw [hhead] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    dsimp [N]
    omega
  rw [hNA] at hNcut
  have hN3 : 3≤N := by dsimp [N]; omega
  have hr1 : 1≤r := by omega
  let y:=List.replicate h false++(List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,Nat.add_zero]
    omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  obtain ⟨hbudget,hnot⟩:=Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y
    hw hpre hword hy hA4'
  change E≤1+rayCount y T at hbudget
  have hmissing (hv' : 3≤v ∨ (M+L+U=3 ∧ 2≤v)) : E<T := by
    apply hnot (by omega)
    intro i hi
    have hh:=Recaman.FinalSLocalKey.small_head_no_local_early h M m L s U v i hM hm hL hs hU
      (by change N≤5; omega) hv' hi
    simpa only [y,List.append_assoc] using hh
  by_cases hr : r=1
  · have hUnit : M=1 ∧ L=1 ∧ U=1 := by dsimp [N] at *; omega
    by_cases hR : R=2
    · have hmiss:=hmissing (Or.inr ⟨by omega,by omega⟩)
      omega
    · obtain ⟨hM1,hL1,hU1⟩:=hUnit
      have hlocal : rayCount y T≤3 := by
        simpa only [y,hM1,hL1,hU1,List.append_assoc] using
          Recaman.FinalSSmallHeadCaps.unit_head_final_local_three h m s v T hs (by omega)
      omega
  · by_cases hR : R=3
    · have hmiss:=hmissing (Or.inl (by omega))
      omega
    · have hv4 : 4≤v := by omega
      have hlocal : rayCount y T≤5 := by
        simpa only [y,List.append_assoc] using
          Recaman.FinalSSmallHeadCaps.small_head_large_separator_local_five h M m L s U v T
            hM hL hs (by change N≤5; omega) hv4
      omega

end Recaman.FourLongFinalRayGap
