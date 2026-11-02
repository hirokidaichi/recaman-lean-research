import Recaman.ShortCounterHeadCounts

namespace Recaman.ShortCounterJointCounts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MiddleSTargetFreeGap

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc:=cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- The third A-run retains all old sources; old one plus local four. -/
theorem third_actual_five (f : Nat → Bool) (n h M m L s U : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true) :
    cN (EndN f 0) (n+h+M+m+L+s) U≤5 := by
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
  have hl:=third_ray_four_source_bound h M m L s U hs
  have he:=endable_A_run_count f (n+h+M+m+L+s) U _ hp hA3
  omega

/-- Head and third/last disjoint free counts consume one original
counter budget. The run supply bounds are derived, not inputs. -/
theorem short_counter_joint_counts (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    h+m+s≤j+10 ∧ U+v≤C+8 ∧ (v+2≤C → U+v≤C+7) := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let I:=h+M+m+L+s
  let H:=I+U
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega))
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hAh : cN (fun x=>f x=true) n H=h+m+s := by
    have hx:=ones_seg_eq_count f n (h+M+m+L+s+U)
    rw [hword] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    dsimp [H,I]
    omega
  have hph:=addition_endable_partition f n H
  rw [hAh] at hph
  have hf1:=cN_add P n I U
  have hf2:=cN_add P n H v
  have hf3:=cN_add P n (H+v) T
  have hbad' : cN P n (H+v+T)<j+1 := hbad
  have hhead10' : cN (EndN f 0) n H≤10 := hhead10
  have hSbound : h+m+s≤j+10 := by
    change h+m+s=cN (EndN f 0) n H+cN P n H at hph
    omega
  have hthird:=third_actual_five f n h M m L s U w hw hpre hs (by omega) hS hA hS2 hA2 hS3 hA3
  have hthird' : cN (EndN f 0) (n+I) U≤5 := by simpa only [I,Nat.add_assoc] using hthird
  have hpU:=addition_endable_partition f (n+I) U
  rw [count_A_run f (n+I) U (by simpa only [I,Nat.add_assoc] using hA3)] at hpU
  change U=cN (EndN f 0) (n+I) U+cN P (n+I) U at hpU
  have hpT:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,I,Nat.add_assoc] using hA4)] at hpT
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hpT
  have hlast:=Recaman.ShortTargetLast4.short_counter_last_4 f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hlast' : cN (EndN f 0) (n+H+v) T≤4 := by simpa only [H,I,Nat.add_assoc] using hlast
  have hbalance:=hb.1
  refine ⟨hSbound,?_,?_⟩
  · simp only [Nat.add_assoc] at hf1 hf2 hf3 hpU hpT hlast' hthird' hbad'
    omega
  · intro hdeep
    have h3:=Recaman.ShortTargetLast3.short_counter_last_3 f n t h M m L s U v T j C w hw hpre ht
      hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hdeep
    have h3' : cN (EndN f 0) (n+H+v) T≤3 := by simpa only [H,I,Nat.add_assoc] using h3
    simp only [Nat.add_assoc] at hf1 hf2 hf3 hpU hpT h3' hthird' hbad'
    omega

end Recaman.ShortCounterJointCounts
