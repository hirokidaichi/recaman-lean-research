import Recaman.ShortCounterWeightedCounts
import Recaman.ShortCounterJointQuadratic
import Recaman.MassFourTwoResidual
import Recaman.OldRayPrefixInequality
import Recaman.SecondRaySmallShapes
import Recaman.FirstTwoActualBounds
import Recaman.ShortCounterSourceCounts
import Recaman.ShortCounterJointCuts

namespace Recaman.MassFourTwoGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The same old mass4 target and final S2 have the full actual free-gap, at all lengths and old histories. -/
theorem mass_four_two_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=2) (hC4 : C=4)
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
    : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hres:=Recaman.MassFourTwoResidual.mass_four_two_residual f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hL4 : L≤4 := by omega
  have hfirst:=Recaman.HeadRunSupplyBudgets.first_long_one f n h M w hw hpre (by omega) hS hA
  have hsecond:=Recaman.OldRayPrefixInequality.seed_second_actual_two f n h M m L w hw hpre hS hA hS2 hA2
    hres.1 hres.2.1 hres.2.2.1 hL4
  have heq:=Recaman.HeadRunSupplyBudgets.two_prefix_count f n h M m L hS hS2
  have hprefix : cN (EndN f 0) n (h+M+m+L)≤3 := by omega
  have hhead:=Recaman.HeadRunCountBounds.head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) 3 hprefix
  have hbudget:=Recaman.ShortCounterSourceCounts.short_counter_source_head_budget f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
    (Or.inl (by omega)) 8 hhead
  omega
end Recaman.MassFourTwoGap
