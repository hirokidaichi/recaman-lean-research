import Recaman.UnitNoOldGap
import Recaman.MassThreeSeedGap
import Recaman.LargeSeedGap
import Recaman.MassOneOldTwoGap
import Recaman.OldSourceKeyOrder

namespace Recaman.MassOneFullGap



open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_one_full_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  by_cases hex : ∃ i, i<T ∧ ∃ r, r<n ∧ Win f r (n+h+M+m+L+s+U+v+i-r)
  · obtain ⟨i,hi,r,hr,hseed⟩:=hex
    have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j 1 w hw hpre ht
      hh hM hm hL hs hU hv rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
    have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
    have hord:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (h+M+m+L+s+U+v) i T j
      hw' hr ht (by omega) (by have hx:=hb.2.1; omega)
      (by simpa only [Nat.add_assoc] using hA4)
      (by simpa only [Nat.add_assoc] using hgap)
      (by simpa only [Nat.add_assoc] using hseed)
      (by simpa only [Nat.add_assoc] using htarget)
    have hdt:=seg_drop f 0 n t (by omega)
    have hdr:=seg_drop f 0 n r (by omega)
    simp only [Nat.zero_add,hpre] at hdt hdr
    have hD2 : 2≤mass (w.drop r) := by rw [←hdt,←hdr,hC] at hord; omega
    by_cases hD3 : mass (w.drop r)≤3
    · rcases (show mass (w.drop r)=2 ∨ mass (w.drop r)=3 by omega) with h2|h3
      · exact Recaman.MassOneOldTwoGap.mass_one_old_two_gap f n t h M m L s U v T j w hw hpre ht
          hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos r i hr hi hseed h2
      · exact Recaman.MassThreeSeedGap.mass_three_seed_gap f n t h M m L s U v T j w hw hpre ht
          hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos r i hr hi hseed h3
    · exact Recaman.LargeSeedGap.large_seed_gap f n t h M m L s U v T j w hw hpre ht
        hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos r i hr hi hseed (by omega)
  · have hnoOld : ∀ i, i<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+i-r) := by
      intro i hi r hr hw
      exact hex ⟨i,hi,r,hr,hw⟩
    exact Recaman.UnitNoOldGap.unit_no_old_gap f n t h M m L s U v T j w hw hpre ht
      hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hnoOld

end Recaman.MassOneFullGap
