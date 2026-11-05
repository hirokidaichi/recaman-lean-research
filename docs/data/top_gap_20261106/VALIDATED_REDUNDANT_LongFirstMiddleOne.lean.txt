import Recaman.HeadRunCountBounds
import Recaman.RunClockClassifier

namespace Recaman.LongFirstMiddleOne

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.HeadRunSupplyBudgets Recaman.HeadRunCountBounds

/-- With one middle S, a first A run of length at least five cannot
supply an initial-S local clock on the second ray. -/
theorem second_one_local (h M K : Nat) (hM : 5≤M) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate 1 false) K≤1 := by
  have only_two (i : Nat) (he : Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate h false++List.replicate M true++List.replicate 1 false)++List.replicate i true)=true) :
      i=2 := by
    have hc:=Recaman.RunClockClassifier.secondClock_sound h M 1 i (by omega) he
    simp only [Recaman.RunClockClassifier.secondClock,decide_eq_true_eq] at hc
    rcases hc with h2|⟨hq,_,hkey⟩
    · exact h2
    · exfalso
      let q:=(i : Int)+(M : Int)-1-1
      change (q+1)^2=2*1*(M : Int)+1 at hkey
      have hsq:=Recaman.ShortCounterFactorBounds.square_lower (q+1) ((M : Int)-1)
        (by omega) (by dsimp [q]; omega)
      have hprod:=Int.mul_pos (show 0<(M : Int) by omega) (show 0<(M : Int)-4 by omega)
      grind only
  unfold rayCount
  apply cN_le_one_of_unique
  intro i _ k _ hi hk
  exact (only_two i hi).trans (only_two k hk).symm

theorem head_middle_one_long_first_nine (f : Nat → Bool) (n h M m L s U : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hh : 1≤h) (hM : 5≤M) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) (hm : m=1) :
    cN (EndN f 0) n (h+M+m+L+s+U)≤9 := by
  have hpref : cN (EndN f 0) n (h+M+m+L)≤4 := by
    by_cases hsum : 3≤h+m
    · have hp : seg f 0 (n+h)=w++List.replicate h false := by
        rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
      have hfirst := endable_A_run_count f (n+h) M _ hp hA
      have hb := block_rayCount_after_S hw h M
      have hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 := by
        rw [hm]
        exact second_one_local h M L hM
      have hsecond:=second_actual_bound f n h M m L 1 w hw hpre hsum hS hA hS2 hA2 hlocal
      have heq:=two_prefix_count f n h M m L hS hS2
      omega
    · have hx:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2
        (hpos (h+M+m+L) (by omega) (by omega))
      omega
  exact head_from_prefix f n h M m L s U w hw hpre (by omega) (by omega) hL hs hU (by omega)
    hS hA hS2 hA2 hS3 hA3 hpos 4 hpref

end Recaman.LongFirstMiddleOne
