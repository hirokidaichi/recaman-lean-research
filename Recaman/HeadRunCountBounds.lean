import Recaman.HeadRunSupplyBudgets
import Recaman.OldTargetFirstRun

namespace Recaman.HeadRunCountBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.HeadRunSupplyBudgets

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc:=cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

theorem small_S_prefix (f : Nat → Bool) (n h M m L : Nat) (hsmall : h+m≤2)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hp : cN (EndN f 0) n (h+M+m+L)+1≤cN (fun x=>f x=false) n (h+M+m+L)) :
    cN (EndN f 0) n (h+M+m+L)≤1 := by
  have hc:=cntF_seg f n (h+M+m+L)
  have hw:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0 hS hA hS2 hA2
    (by intro x hx hxB; omega) (by intro i hi; omega)
  simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hw
  rw [hw] at hc
  simp only [cntF_append,cntF_replicate_S,cntF_A,Nat.add_zero] at hc
  omega

theorem head_from_prefix (f : Nat → Bool) (n h M m L s U : Nat)
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
    (B : Nat) (hprefix : cN (EndN f 0) n (h+M+m+L)≤B) :
    cN (EndN f 0) n (h+M+m+L+s+U)≤B+5 := by
  have ht:=Recaman.ShortCounterJointCounts.third_actual_five f n h M m L s U w hw hpre hs hSsum
    hS hA hS2 hA2 hS3 hA3
  have hz : cN (EndN f 0) (n+h+M+m+L) s=0 := by
    apply cN_zero_of
    intro x hx hxB he
    have ha:=he.1
    rw [hS3 x hx hxB] at ha
    contradiction
  have h1:=cN_add (EndN f 0) n (h+M+m+L) s
  have h2:=cN_add (EndN f 0) n (h+M+m+L+s) U
  simp only [Nat.add_assoc] at *
  omega

theorem head_first_two_eight (f : Nat → Bool) (n h M m L s U : Nat)
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
    (hM2 : M≤2) : cN (EndN f 0) n (h+M+m+L+s+U)≤8 := by
  have hpref : cN (EndN f 0) n (h+M+m+L)≤3 := by
    by_cases hsum : 3≤h+m
    · have hfirst:=first_two_zero f n h M w hw hpre hM2 hS hA
      have hsecond:=second_actual_bound f n h M m L 2 w hw hpre hsum hS hA hS2 hA2 (rayCount_S_A_S h M m L)
      have heq:=two_prefix_count f n h M m L hS hS2
      omega
    · have hx:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2
        (hpos (h+M+m+L) (by omega) (by omega))
      omega
  exact head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU hSsum
    hS hA hS2 hA2 hS3 hA3 hpos 3 hpref

theorem head_long_first_nine (f : Nat → Bool) (n h M m L s U : Nat)
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
    (hlong : 2*M≤h+3) : cN (EndN f 0) n (h+M+m+L+s+U)≤9 := by
  have hpref : cN (EndN f 0) n (h+M+m+L)≤4 := by
    by_cases hsum : 3≤h+m
    · have hfirst:=first_long_one f n h M w hw hpre hlong hS hA
      have hsecond:=second_actual_bound f n h M m L 2 w hw hpre hsum hS hA hS2 hA2 (rayCount_S_A_S h M m L)
      have heq:=two_prefix_count f n h M m L hS hS2
      omega
    · have hx:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2
        (hpos (h+M+m+L) (by omega) (by omega))
      omega
  exact head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU hSsum
    hS hA hS2 hA2 hS3 hA3 hpos 4 hpref

theorem head_three_middle_one_eight (f : Nat → Bool) (n h M m L s U : Nat)
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
    (hM3 : M=3) (hm1 : m=1) : cN (EndN f 0) n (h+M+m+L+s+U)≤8 := by
  have hpref : cN (EndN f 0) n (h+M+m+L)≤3 := by
    by_cases hsum : 3≤h+m
    · have hfirst:=Recaman.OldTargetFirstRun.first_run_supply_le_one f n h M w hw hpre (by omega) hS hA
      have hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 := by
        rw [hM3,hm1]
        exact second_three_one_local h L
      have hsecond:=second_actual_bound f n h M m L 1 w hw hpre hsum hS hA hS2 hA2 hlocal
      have heq:=two_prefix_count f n h M m L hS hS2
      omega
    · have hx:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2
        (hpos (h+M+m+L) (by omega) (by omega))
      omega
  exact head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU hSsum
    hS hA hS2 hA2 hS3 hA3 hpos 3 hpref

end Recaman.HeadRunCountBounds
