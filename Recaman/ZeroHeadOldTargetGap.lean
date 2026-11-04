import Recaman.MassOneFullGap
import Recaman.MassTwoFullGap
import Recaman.MassThreeAllSeparators
import Recaman.EqualTargetGap
import Recaman.OffsetOneTargetGap
import Recaman.OffsetTwoTargetGap
import Recaman.LargeTargetOffsetGap
import Recaman.ShortCounterJointCuts
import Recaman.MassFourOneGap
import Recaman.MassFourTwoGap
import Recaman.MassFourThreeGap
import Recaman.MassFiveOneGap
import Recaman.MassFiveTwoGap

namespace Recaman.ZeroHeadOldTargetGap


open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Coverage integration of the independently audited mass branches.
This corollary is not an additional source mechanism or general C1. -/
theorem zero_head_old_target_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hC : mass (w.drop t)=(C : Int))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)

 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hne : w.drop t≠[] := by
    intro he
    have hn : w.length=n := by rw [←hpre,seg_length]
    have hl:=List.length_drop (l:=w) (i:=t)
    rw [he,hn] at hl
    simp only [List.length_nil] at hl
    omega
  have hCp : 1≤C := by
    have hp:=(sufPos_block hu [] (w.drop t) rfl hne).1
    omega
  by_cases hC1 : C=1
  · exact Recaman.MassOneFullGap.mass_one_full_gap f n t h M m L s U v T j w hw hpre ht
      hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget (by omega) hpos
  by_cases hC2 : C=2
  · exact Recaman.MassTwoFullGap.mass_two_full_gap f n t h M m L s U v T j w hw hpre ht
      hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget (by omega) hpos
  by_cases hC3 : C=3
  · exact Recaman.MassThreeAllSeparators.mass_three_all_separators_gap f n t h M m L s U v T j w hw hpre ht
      hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget (by omega) hpos
  have hC4 : 4≤C := by omega
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  by_cases hvC : v<C
  · have hc:=Recaman.ShortCounterJointCuts.short_counter_joint_cuts f n t h M m L s U v T j C w hw hpre ht
      hh hM hm hL hs hU hvC hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
    rcases (show C=4 ∨ C=5 by have hh:=hc.1; omega) with h4|h5
    · have hv3:=hc.2.1
      rcases (show v=1 ∨ v=2 ∨ v=3 by omega) with h1|h2|h3
      · exact Recaman.MassFourOneGap.mass_four_one_gap f n t h M m L s U v T j C w hw hpre ht
          hh hM hm hL hs hU h1 h4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
      · exact Recaman.MassFourTwoGap.mass_four_two_gap f n t h M m L s U v T j C w hw hpre ht
          hh hM hm hL hs hU h2 h4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
      · exact Recaman.MassFourThreeGap.mass_four_three_gap f n t h M m L s U v T j C w hw hpre ht
          hh hM hm hL hs hU h3 h4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
    · have hv2 : v≤2 := hc.2.2.2 (by have hh:=hc.2.1; omega)
      rcases (show v=1 ∨ v=2 by omega) with h1|h2
      · exact Recaman.MassFiveOneGap.mass_five_one_gap f n t h M m L s U v T j C w hw hpre ht
          hh hM hm hL hs hU h1 h5 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
      · exact Recaman.MassFiveTwoGap.mass_five_two_gap f n t h M m L s U v T j C w hw hpre ht
          hh hM hm hL hs hU h2 h5 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
  · by_cases he : v=C
    · exact Recaman.EqualTargetGap.equal_target_gap f n t h M m L s U v T j C w hw hpre ht
        hh hM hm hL hs hU he hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
    by_cases he1 : v=C+1
    · exact Recaman.OffsetOneTargetGap.offset_one_target_gap f n t h M m L s U v T j C w hw hpre ht
        hh hM hm hL hs hU he1 hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
    by_cases he2 : v=C+2
    · exact Recaman.OffsetTwoTargetGap.offset_two_target_gap f n t h M m L s U v T j C w hw hpre ht
        hh hM hm hL hs hU he2 hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos
    exact Recaman.LargeTargetOffsetGap.large_target_offset_gap f n t h M m L s U v T j C w hw hpre ht
      hh hM hm hL hs hU (by omega) hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos

end Recaman.ZeroHeadOldTargetGap
