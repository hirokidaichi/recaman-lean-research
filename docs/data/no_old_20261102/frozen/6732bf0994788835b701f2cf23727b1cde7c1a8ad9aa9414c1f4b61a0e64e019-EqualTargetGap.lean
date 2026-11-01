import Recaman.EqualTargetNoOldGap
import Recaman.OldZeroInitialSource
import Recaman.FourthActualSeven
import Recaman.EarlyOldSixFree

import Recaman.EqualTargetCounter

namespace Recaman.EqualTargetGap

open Recaman.ASourceReuse

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- All old/no-old cases for a mass-three target after a positive
zero-mass three-run head and S3. No old-clock or local-band premise. -/
theorem equal_target_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=C) (hC4 : 4≤C)
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
  by_cases hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)
  · exact Recaman.EqualTargetNoOldGap.equal_target_no_old_gap f n t h M m L s U v T j C w hw hpre ht
      hh hM hm hL hs hU hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hno hpos
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hb:=Recaman.EqualTargetCounter.equal_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  obtain ⟨k,hkno⟩:=Classical.not_forall.mp hno
  have hk : k<T := by
    by_cases hh : k<T
    · exact hh
    · exact False.elim (hkno (fun hh'=>False.elim (hh hh')))
  have hrno : ¬∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r) := by
    intro hr
    exact hkno (fun _=>hr)
  obtain ⟨r,hrno⟩:=Classical.not_forall.mp hrno
  have hr : r<n := by
    by_cases hh : r<n
    · exact hh
    · exact False.elim (hrno (fun hh'=>False.elim (hh hh')))
  have hwin : Win f r (n+h+M+m+L+s+U+v+k-r) := by
    apply Classical.byContradiction
    intro hn
    exact hrno (fun _=>hn)
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have horder:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t
    (h+M+m+L+s+U+v) k T j hw' hr ht (by omega) (by have hR:=hb.2.1; omega)
    (by simpa only [Nat.add_assoc] using hA4)
    (by simpa only [Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using hwin)
    (by simpa only [Nat.add_assoc] using htarget)
  have hk1 : k=0 := by have hT:=hb.1; omega
  subst k
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v 0 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun l hl=>by simpa only [H,Nat.add_assoc] using hA4 l (by omega))
    (by intros; omega) (by simpa only [H,Nat.add_assoc,Nat.add_zero] using hwin)
  have hD : 5≤mass (w.drop r) := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hm
    omega
  have hf6:=Recaman.EarlyOldSixFree.early_old_mass_five_six_free f n h M m L s U v T r 0 w hw hpre
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hr hk
    (by simpa only [H,Nat.add_assoc] using hwin) (by omega) hD
    (fun l hl hlH=>hpos l hl (by omega))
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  let a:=z++List.replicate v false
  have hseed : tailOldRay w a 0 := by
    refine ⟨r,?_,?_,?_⟩
    · have hn : w.length=n := by rw [←hpre,seg_length]
      omega
    · have hm:=hprof.1
      simpa only [a,List.replicate_zero,List.append_nil,mass_append,mass_replicate_A,List.append_assoc,Int.natCast_zero,Int.add_zero] using hm
    · have hk:=source_key_before_gap (w.drop r++a) 0 0
        (by simpa only [a,List.append_assoc] using hprof.1)
        (by simpa only [a,List.append_assoc] using hprof.2)
      rw [←runKey_append]
      simpa using hk
  have hshape : seg f 0 (n+H+v)=w++a := by
    rw [show n+H+v=n+(H+v) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
  have he:=endable_A_run_count f (n+H+v) T (w++a) hshape
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hraw:=Recaman.OldZeroInitialSource.old_zero_fourth_ray_count_six w hw h M m L s U v T (by omega)
    (by rw [←hhead]; exact hmz)
    (by rw [←hhead]; change 1≤cntF z; rw [hSz]; omega)
    (by simpa only [a,z,H,hhead,List.append_assoc] using hseed)
  have hlast : cN (EndN f 0) (n+H+v) T≤6 := by
    rw [he]
    simpa only [a,z,H,hhead,List.append_assoc] using hraw
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have hfive : 6≤cN P n H := by simpa only [H] using hf6.2
  have hT:=hb.1
  change j+1≤cN P n (H+v+T)
  simp only [H,Nat.add_assoc] at hc1 hc2 hp hlast hfive ⊢
  omega

end Recaman.EqualTargetGap
