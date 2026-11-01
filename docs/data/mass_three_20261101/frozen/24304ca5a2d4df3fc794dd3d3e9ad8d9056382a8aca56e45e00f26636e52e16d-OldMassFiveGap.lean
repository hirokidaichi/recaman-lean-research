import Recaman.EarlyOldSixFree
import Recaman.OldZeroInitialSource
import Recaman.MomentTargetProfile
import Recaman.FourRunSupplySeventeen

namespace Recaman.OldMassFiveGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunSupplySeventeen Recaman.FourRunTargetArea Recaman.MomentTargetProfile
open Recaman.MomentActualTarget Recaman.OldSourceKeyOrder
open Recaman.ASourceReuse Recaman.EarlyOldSixFree Recaman.OldZeroInitialSource

/-- Any actual old supplier of mass at least five pays the final-band
free gap by original actual counts. No head, gap or old-mass cutoff is input. -/
theorem mass_five_supplier_gap (f : Nat → Bool) (n t h M m L s U v T j q i sOld kOld : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hsOld : sOld<n) (hkOld : kOld<T)
    (hseedWin : Win f sOld (n+h+M+m+L+s+U+v+kOld-sOld))
    (hD : 5≤mass (w.drop sOld))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  let H:=h+M+m+L+s+U
  let S:=h+m+s
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hword:=four_run_word f n h M m L s U v T hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=S := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H,S] at *
    omega
  have hsrc:=actual_final_S_source_A_budget f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hq hqv hi hband hword hS4 hA4 hgap htarget hlocal
  have hF4 : 4≤cN P n (H+v+T) := by
    by_cases hf : cN P n (H+v+T)≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 (H+v+T) hw hpre0
        (by simpa only [H,Nat.add_assoc] using hpos) hf
      have hAbound : 2*(j+1)+2≤cN (fun x=>f x=true) n (H+v+T) := by
        simpa only [H,Nat.add_assoc] using hsrc.2.2
      change cN (fun x=>f x=true) n (H+v+T)≤2*cN P n (H+v+T)+1 at hb
      change cN P n (H+v+T)<j+1 at hcounter
      omega
    · omega
  have hj : 2≤j := by change cN P n (H+v+T)<j+1 at hcounter; omega
  have hprof:=actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hmass:=hprof.1
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hmass
  have hprior:=actual_old_target_prior_clock f n sOld t (H+v) kOld T j
    (by rw [hpre]; exact hw) hsOld ht (by omega) hj
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using hseedWin)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hprofOld:=actual_target_word_profile f n sOld H v kOld 0 w z hpre hsOld rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by intro k hk; simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intro x hx hx0; omega)
    (by simpa only [H,Nat.add_assoc,Nat.add_zero] using hseedWin)
  let a:=z++List.replicate v false
  have hseed : tailOldRay w a kOld := by
    refine ⟨sOld,?_,?_,?_⟩
    · have hn : w.length=n := by rw [←hpre,seg_length]
      omega
    · have hm:=hprofOld.1
      simp only [a,List.replicate_zero,List.append_nil,mass_append,mass_replicate_A] at hm ⊢
      omega
    · have hk:=source_key_before_gap (w.drop sOld++a) kOld 0
        (by simpa only [a,List.append_assoc] using hprofOld.1)
        (by simpa only [a,List.append_assoc] using hprofOld.2)
      rw [←runKey_append]
      simpa using hk
  have hkOne : kOld≤1 := by
    have hi2:=hsrc.2.1
    omega
  have hmassOld:=hprofOld.1
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,List.replicate_zero,List.append_nil] at hmassOld
  have hfree:=early_old_mass_five_six_free f n h M m L s U v T sOld kOld w hw hpre
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hsOld hkOld hseedWin
    (by omega) hD (fun k hk hkH=>hpos k hk (by omega))
  have hlastword : seg f 0 (n+H+v)=w++(z++List.replicate v false) := by
    rw [show n+H+v=n+(H+v) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
  have he:=endable_A_run_count f (n+H+v) T (w++(z++List.replicate v false)) hlastword
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hlast : cN (EndN f 0) (n+H+v) T≤T-(j+1)+6 := by
    by_cases hk0 : kOld=0
    · have hraw:=old_zero_fourth_ray_count_six w hw h M m L s U v T hv
        (by rw [←hhead]; exact hmz)
        (by rw [←hhead]; change 1≤cntF z; rw [hSz]; dsimp [S]; omega)
        (by simpa only [a,z,H,hhead,List.append_assoc,hk0] using hseed)
      have hb : cN (EndN f 0) (n+H+v) T≤6 := by
        rw [he]
        simpa only [z,H,hhead,List.append_assoc] using hraw
      omega
    · have hk1 : kOld=1 := by omega
      have hT : T=j+2 := by have hi2:=hsrc.2.1; omega
      have hcnt : 3≤cntF (z++List.replicate v false) := by
        rw [cntF_append,cntF_replicate_S,hSz]
        dsimp [S]
        omega
      have ho:=block_rayCount_append hw (z++List.replicate v false) hcnt T
      have hl:=Recaman.AdjacentRunSupply.fourth_ray_local_le_six h M m L s U v T hv
      have hl' : rayCount (z++List.replicate v false) T≤6 := by
        simpa only [z,H,hhead,List.append_assoc] using hl
      omega
  have hAc:=count_A_run f (n+H+v) T
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hp:=addition_endable_partition f (n+H+v) T
  rw [hAc] at hp
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hfh : 6≤cN P n H := hfree.2
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  change cN P n (H+v+T)<j+1 at hcounter
  simp only [Nat.add_assoc] at hc1 hc2 hlast hp hfh hcounter
  omega

end Recaman.OldMassFiveGap
