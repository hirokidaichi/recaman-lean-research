import Recaman.FinalBandSupplyClock
import Recaman.FourRunSourceBase

namespace Recaman.SmallPrefixSupplyThirteen

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.ThreeRunSupplyBudget Recaman.SeparatorSupplyReset Recaman.FinalBandSupplyClock
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Small first-two-run A count excludes all but clock2 in the final
band. The original actual count is bounded by first-three10 + last3. -/
theorem four_run_small_prefix_supply_le_thirteen (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (ht : t<n) (hj : 2≤j) (hshort : T≤j+2) (hML : M+L<j+1)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (hM : 1≤M) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+U+v+T)≤13 := by
  let B := h+M+m+L+s+U
  let D := B+v
  let rs : List (Bool × Nat) :=
    [(false,h),(true,M),(false,m),(true,L),(false,s),(true,U),(false,v)]
  have hh : 1≤h := by
    by_cases hh0 : h=0
    · have hAt : f n=true := by simpa only [hh0,Nat.add_zero] using hA 0 hM
      have hSz : cN (fun x=>f x=false) n 1=0 := by simp [cN,hAt]
      have hp:=hpos 1 (by omega) (by omega)
      rw [hSz] at hp
      omega
    · omega
  have h3 := Recaman.InitialSTargetBounds.three_run_count_of_manyS
    f n h M m L s U w hw hpre hs (by omega)
    hS hA hS2 hA2 hS3 hA3 (fun k hk hkB => hpos k hk (by omega))
  let B0 := h+M+m+L+s
  have hA3' : ∀ k, k<U → f (n+B0+k)=true := by simpa only [B0,Nat.add_assoc] using hA3
  have hword0 : seg f n B0=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false := by
    have hh0:=three_run_word f n h M m L s 0 hS hA hS2 hA2 hS3
      (by intro k hk; omega)
    simpa only [B0,Nat.add_zero,List.replicate_zero,List.append_nil] using hh0
  have hsmall : cN (fun x=>f x=true) n B0<j+1 := by
    have hc:=ones_seg_eq_count f n B0
    rw [hword0] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hshape : seg f (n+B0) (U+v)=List.replicate U true++List.replicate v false := by
    rw [seg_add]
    have hUword : seg f (n+B0) U=List.replicate U true := by
      apply seg_A
      intro x hx hxu
      have hb:=hA3' (x-(n+B0)) (by omega)
      rw [show n+B0+(x-(n+B0))=x by omega] at hb
      exact hb
    rw [hUword,show n+B0+U=n+h+M+m+L+s+U by dsimp [B0]; omega,
      seg_false f (n+h+M+m+L+s+U) v hS4]
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have h4:=last_ray_count_le_three f n t B0 U v T j hw' ht hv hj hshort hsmall hshape
    (by simpa only [B0,Nat.add_assoc] using hA4)
    (by simpa only [B0,Nat.add_assoc] using hgap)
    (by simpa only [B0,Nat.add_assoc] using htarget)
  have h4' : cN (EndN f 0) (n+D) T≤3 := by
    simpa only [D,B,B0,Nat.add_assoc] using h4
  have hSzero : cN (EndN f 0) (n+B) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have hf := hS4 x (by omega) (by omega)
    have ht := he.1
    rw [hf] at ht
    contradiction
  have hc1 := cN_add (EndN f 0) n B v
  have hc2 := cN_add (EndN f 0) n D T
  change cN (EndN f 0) n (D+T)≤13
  change cN (EndN f 0) n B≤10 at h3
  dsimp only [D] at hc2 h4' ⊢
  omega


open Recaman.FourRunSupplySeventeen
theorem small_prefix_counterexample_band_nine (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hML : M+L<j+1) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+U+v+T+j))
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤9 ∧
    cN (fun x => f x=true) n (h+M+m+L+s+U+v+T)≤22 ∧ j≤9 := by
  have hword:=four_run_word f n h M m L s U v T hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hnew:=Recaman.FourRunTargetArea.actual_final_S_source_A_budget
    f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hq hqv hi hband hword hS4 hA4 hgap htarget hlocal
  have hold:=Recaman.FourRunSupplyBudget.four_run_free_gap_residual f n h M m L s U v T j
    w hw hpre hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap he hbad
  have hE:=four_run_small_prefix_supply_le_thirteen f n t h M m L s U v T j
    w hw hpre ht (by omega) (by omega) hML htarget hgap
    hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  have hp:=addition_endable_partition f n (h+M+m+L+s+U+v+T)
  omega

theorem small_prefix_band_from_zero (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hML : M+L<j+1) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hzero : cN (EndN f 0) 0 n=cN (fun x => f x=false) 0 n)
    (hpos : ∀ k, n<k → k≤n+h+M+m+L+s+U+v+T+j →
      cN (EndN f 0) 0 k+1≤cN (fun x => f x=false) 0 k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+U+v+T+j))
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤9 ∧
    cN (fun x => f x=true) n (h+M+m+L+s+U+v+T)≤22 ∧ j≤9 := by
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k := by
    intro k hk hkB
    have hp:=hpos (n+k) (by omega) (by omega)
    have hE:=cN_add (EndN f 0) 0 n k
    have hS:=cN_add (fun x=>f x=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  exact small_prefix_counterexample_band_nine f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hML hq hqv hi hband hS hA hS2 hA2 hS3 hA3 hS4 hA4
    hrel hgap he htarget hlocal hbad

end Recaman.SmallPrefixSupplyThirteen
