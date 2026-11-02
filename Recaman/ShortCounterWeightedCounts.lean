import Recaman.ShortCounterJointCounts
import Recaman.OldTargetFirstRun

namespace Recaman.ShortCounterWeightedCounts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The two-run weighted free charge is combined with the third and last
runs in one original-base actual partition. Small-first budget is internal. -/
theorem short_counter_weighted_counts (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v<C) (hvpos : 1≤v) (hC4 : 4≤C)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    2*(h+m+s)≤M+L+2*(j+1)+9 ∧
    2*(h+m+s)+2*v≤M+L+2*C+17 ∧
    (v+2≤C → 2*(h+m+s)+2*v≤M+L+2*C+15) ∧
    (M≤3 → h+m+s≤j+9) := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let J:=h+M+m+L
  let E:=J+s
  let H:=E+U
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hW:=Recaman.ThreeRunSupplyBudget.two_run_additions_free_bound f n h M m L w hw hpre
    hS hA hS2 hA2 (fun k hk hkB=>hpos k hk (by omega))
  have hA2count : cN (fun x=>f x=true) n J=M+L := by
    have hx:=ones_seg_eq_count f n (h+M+m+L)
    have hw2:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0 hS hA hS2 hA2
      (by intro x hx hxB; omega) (by intro i hi; omega)
    simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hw2
    rw [hw2] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    dsimp [J]
    omega
  change cN (fun x=>f x=true) n J≤2*cN P n J+1 at hW
  rw [hA2count] at hW
  have hf1:=cN_add P n J s
  change cN P n E=cN P n J+cN P (n+J) s at hf1
  have hf2:=cN_add P n E U
  change cN P n H=cN P n E+cN P (n+E) U at hf2
  have hf3:=cN_add P n H v
  have hf4:=cN_add P n (H+v) T
  have hbad' : cN P n (H+v+T)<j+1 := hbad
  have h3:=Recaman.ShortCounterJointCounts.third_actual_five f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3
  have h3' : cN (EndN f 0) (n+E) U≤5 := by simpa only [E,J,Nat.add_assoc] using h3
  have hpU:=addition_endable_partition f (n+E) U
  rw [count_A_run f (n+E) U (by simpa only [E,J,Nat.add_assoc] using hA3)] at hpU
  change U=cN (EndN f 0) (n+E) U+cN P (n+E) U at hpU
  have hpT:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,E,J,Nat.add_assoc] using hA4)] at hpT
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hpT
  have hlast:=Recaman.ShortTargetLast4.short_counter_last_4 f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hlast' : cN (EndN f 0) (n+H+v) T≤4 := by simpa only [H,E,J,Nat.add_assoc] using hlast
  have hbalance:=hb.1
  refine ⟨?_,?_,?_,?_⟩
  · simp only [Nat.add_assoc] at hf3 hf4 hbad' hpT hlast'
    omega
  · simp only [Nat.add_assoc] at hf3 hf4 hbad' hpT hlast'
    omega
  · intro hdeep
    have hx:=Recaman.ShortTargetLast3.short_counter_last_3 f n t h M m L s U v T j C w hw hpre ht
      hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hdeep
    have hx' : cN (EndN f 0) (n+H+v) T≤3 := by simpa only [H,E,J,Nat.add_assoc] using hx
    simp only [Nat.add_assoc] at hf3 hf4 hbad' hpT hx'
    omega
  · intro hM3
    have hhead9:=Recaman.OldTargetFirstRun.three_run_count_small_first f n h M m L s U w hw hpre hM3 hs
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega))
    have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
    have hAh : cN (fun x=>f x=true) n H=h+m+s := by
      have hx:=ones_seg_eq_count f n (h+M+m+L+s+U)
      rw [hword] at hx
      simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
      dsimp [H,E,J]
      omega
    have hpart:=addition_endable_partition f n H
    rw [hAh] at hpart
    change h+m+s=cN (EndN f 0) n H+cN P n H at hpart
    change cN (EndN f 0) n H≤9 at hhead9
    simp only [Nat.add_assoc] at hf3 hf4 hbad'
    omega

end Recaman.ShortCounterWeightedCounts
