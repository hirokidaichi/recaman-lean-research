import Recaman.NonsquareHeadSupply
import Recaman.ShortCounterJointCounts

namespace Recaman.NonsquareActualSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MiddleSTargetFreeGap

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc:=cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- The third A-run retains all old sources; old one plus local three in the nonsquare band. -/
theorem third_actual_four (f : Nat → Bool) (n h M m L s U : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hKlo : 18≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))
    (hKhi : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤23) :
    cN (EndN f 0) (n+h+M+m+L+s) U≤4 := by
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
    hS hA hS2 hA2 hS3 (by intro i hi; omega)
  have hp : seg f 0 (n+h+M+m+L+s)=w++(List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false) := by
    rw [show n+h+M+m+L+s=n+(h+M+m+L+s) by omega,seg_add,Nat.zero_add,hpre]
    congr 1
    simpa using hword
  have hcS : 3≤cntF (List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A]
    omega
  have ho:=block_rayCount_append hw _ hcS U
  have hl:=Recaman.NonsquareHeadSupply.third_ray_three h M m L s U hKlo hKhi
  have he:=endable_A_run_count f (n+h+M+m+L+s) U _ hp hA3
  omega


end Recaman.NonsquareActualSupply
