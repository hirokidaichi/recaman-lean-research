import Recaman.HeadRunCountBounds
import Recaman.OldTargetFirstRun

namespace Recaman.HeadSixSevenCount

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.HeadRunSupplyBudgets

open Recaman.HeadRunCountBounds

theorem second_six_seven_local (h M K : Nat) (hM : M=6 ∨ M=7) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate 1 false) K≤1 := by
  unfold rayCount
  apply cN_le_one_of_unique
  have only2 (i : Nat) (hi : Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate h false++List.replicate M true++List.replicate 1 false)++List.replicate i true)=true) : i=2 := by
    have he:=localSupply_two_run_iff h M 1 i 0
    simp only [List.replicate_zero,List.append_nil,Nat.zero_add,Int.natCast_zero,Int.zero_add,Nat.mul_one,Int.one_pow] at he
    rcases he.mp hi with ⟨q,hq,hqh,hm,hk⟩|⟨a,ha,haM,hm,hk⟩|hlast
    · change (1 : Int)=((q : Int)+1)^2-2*(M : Int) at hk
      have hsq : ((q : Int)+1)^2=2*(M : Int)+1 := by omega
      by_cases hq2 : q≤2
      · have hx:=Recaman.ShortCounterFactorBounds.square_lower 3 ((q : Int)+1) (by omega) (by omega)
        rcases hM with h6 | h7
        · omega
        · omega
      · have hx:=Recaman.ShortCounterFactorBounds.square_lower ((q : Int)+1) 4 (by omega) (by omega)
        rcases hM with h6 | h7
        · omega
        · omega
    · change (1 : Int)=1*((1 : Int)-2*(a : Int)) at hk
      have hx : (1 : Int)=1-2*(a : Int) := by simpa only [Int.one_mul] using hk
      omega
    · omega
  intro i hi j hj hsi hsj
  have h1:=only2 i hsi
  have h2:=only2 j hsj
  omega

theorem head_six_seven_middle_one_eight (f : Nat → Bool) (n h M m L s U : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hM67 : M=6 ∨ M=7) (hm1 : m=1) (hlong : 2*M≤h+3) : cN (EndN f 0) n (h+M+m+L+s+U)≤8 := by
  have hpref : cN (EndN f 0) n (h+M+m+L)≤3 := by
    by_cases hsum : 3≤h+m
    · have hfirst:=first_long_one f n h M w hw hpre hlong hS hA
      have hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 := by
        rw [hm1]
        exact second_six_seven_local h M L hM67
      have hsecond:=second_actual_bound f n h M m L 1 w hw hpre hsum hS hA hS2 hA2 hlocal
      have heq:=two_prefix_count f n h M m L hS hS2
      omega
    · have hx:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2
        (hpos (h+M+m+L) (by omega) (by omega))
      omega
  exact head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU hSsum
    hS hA hS2 hA2 hS3 hA3 hpos 3 hpref

end Recaman.HeadSixSevenCount
