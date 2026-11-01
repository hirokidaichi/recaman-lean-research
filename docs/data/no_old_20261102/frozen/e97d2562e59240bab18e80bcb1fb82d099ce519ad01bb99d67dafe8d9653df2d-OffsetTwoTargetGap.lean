import Recaman.OffsetHeadBound
import Recaman.OffsetTargetCounter
import Recaman.FourthActualSeven
import Recaman.EarlyOldFourFree

namespace Recaman.OffsetTwoTargetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Mass-three target/S5 full gap. The same target orders every old
supplier, and its actual early seed pays the extra old clock. -/
theorem offset_two_target_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=C+2) (hC4 : 4≤C)
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
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  classical
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hb:=Recaman.OffsetTargetCounter.offset_two_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hkey : runKey (w.drop t)≤ -runKey z-12*((h : Int)+(m : Int)+(s : Int))-10-2*((j : Int)+1)^2 := hb.2.2
  have hS10:=Recaman.OffsetHeadBound.offset_head_ten (w.drop t) z hu (j+1) hb.2.1
    (by rw [hSz]; simpa only [Int.natCast_add,Int.natCast_one] using hkey)
  rw [hSz] at hS10
  have hAh:=ones_seg_eq_count f n H
  change ones (seg f n (h+M+m+L+s+U))=_ at hAh
  rw [hhead] at hAh
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at hAh
  have hfhead : 4≤cN P n H := by
    by_cases hf : cN P n H≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hc:=positive_r3_additions_free_bound f n 0 H hw hpre0
        (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hf
      change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hc
      omega
    · omega
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have hT:=hb.1
  by_cases hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+H+v+k-r)
  · have heq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4) hno
    have hl:=Recaman.FourthLocalSix.fourth_local_six h M m L s U v T (by omega)
    have hlast : cN (EndN f 0) (n+H+v) T≤6 := by
      rw [heq]
      simpa only [z,H,hhead,List.append_assoc] using hl
    change j+1≤cN P n (H+v+T)
    simp only [Nat.add_assoc] at hc1 hc2 hp hlast ⊢
    omega
  ·
    obtain ⟨k,hkno⟩:=Classical.not_forall.mp hno
    have hk : k<T := by
      by_cases hh : k<T
      · exact hh
      · exact False.elim (hkno (fun hh'=>False.elim (hh hh')))
    have hrno : ¬∀ r, r<n → ¬Win f r (n+H+v+k-r) := by
      intro hr
      exact hkno (fun _=>hr)
    obtain ⟨r,hrno⟩:=Classical.not_forall.mp hrno
    have hr : r<n := by
      by_cases hh : r<n
      · exact hh
      · exact False.elim (hrno (fun hh'=>False.elim (hh hh')))
    have hwin : Win f r (n+H+v+k-r) := by
      apply Classical.byContradiction
      intro hn
      exact hrno (fun _=>hn)
    have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
    have horder:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (H+v) k T j hw' hr ht
      (by omega) (by have hR:=hb.2.1; omega)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      (by simpa only [Nat.add_assoc] using hwin)
      (by simpa only [H,Nat.add_assoc] using htarget)
    have hk2 : k≤2 := by omega
    have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v k 0 w z hpre hr rfl
      (by simpa only [H,Nat.add_assoc] using hS4)
      (fun l hl=>by simpa only [H,Nat.add_assoc] using hA4 l (by omega))
      (by intros; omega) (by simpa only [Nat.add_zero] using hwin)
    have hD : 4≤mass (w.drop r) := by
      have hm:=hprof.1
      simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hm
      omega
    have hf5:=Recaman.EarlyOldFourFree.early_old_mass_four_free f n h M m L s U v T r k w hw hpre
      hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hr hk
      (by simpa only [H,Nat.add_assoc] using hwin) hk2 hD
      (fun l hl hlH=>hpos l hl (by omega))
    have hlast:=Recaman.FourthActualSeven.fourth_actual_seven f n h M m L s U v T w hw hpre
      hh hm hs (by omega) hS hA hS2 hA2 hS3 hA3 hS4 hA4
    change j+1≤cN P n (H+v+T)
    have hfive : 5≤cN P n H := by simpa only [H] using hf5.2
    simp only [H,Nat.add_assoc] at hc1 hc2 hp hlast hfive ⊢
    omega

end Recaman.OffsetTwoTargetGap
