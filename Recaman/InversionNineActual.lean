import Recaman.InversionActualBudget
import Recaman.SmallInversionBudget

namespace Recaman.InversionNineActual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem inversion_nine_actual_six (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤9)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤6 := by
  have hb:=Recaman.InversionActualBudget.three_run_min_joint_budget f n h M m L s T w hw hpre hs hSsum
    hS hA hS2 hA2 hS3 hA3 hM hm hL hpos
  by_cases hM1 : M=1
  · have hj:=Recaman.SmallInversionJoint.small_inversion_joint_count h M m L s T hM hm hL hs (by omega)
    have hm1 : min M 2≤1 := by omega
    omega
  · have ha:=Recaman.InversionNine.second_local_one h M m L s (by omega) hm hL hs hI
    have hc:=Recaman.InversionNine.third_local_one h M m L s T (by omega) hm hL hs hI
    have hm2:=Nat.min_le_right M 2
    omega

end Recaman.InversionNineActual
