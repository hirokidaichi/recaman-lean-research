import Recaman.HeadRunCountBounds
namespace Recaman.FirstTwoActualBounds
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.HeadRunSupplyBudgets Recaman.HeadRunCountBounds

theorem prefix_first_one (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hpos : cN (EndN f 0) n (h+M+m+L)+1≤cN (fun x=>f x=false) n (h+M+m+L))
    (hfirst : M≤3 ∨ 2*M≤h+3) : cN (EndN f 0) n (h+M+m+L)≤4 := by
  by_cases hsum : 3≤h+m
  · have h1 : cN (EndN f 0) (n+h) M≤1 := by
      rcases hfirst with hsmall | hlong
      · exact Recaman.OldTargetFirstRun.first_run_supply_le_one f n h M w hw hpre hsmall hS hA
      · exact first_long_one f n h M w hw hpre hlong hS hA
    have h2:=second_actual_bound f n h M m L 2 w hw hpre hsum hS hA hS2 hA2 (rayCount_S_A_S h M m L)
    have he:=two_prefix_count f n h M m L hS hS2
    omega
  · have hsml:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2 hpos
    omega
end Recaman.FirstTwoActualBounds
