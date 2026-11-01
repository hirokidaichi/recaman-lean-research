import Recaman.OldZeroInitialSource
import Recaman.EarlyOldHeadFree
import Recaman.MomentTargetProfile

namespace Recaman.OldZeroTargetGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.EarlyOldHeadFree Recaman.OldZeroInitialSource
open Recaman.ASourceReuse

private theorem free_gap_charge (f : Nat → Bool) (n H v T j : Nat)
    (hhead : 5≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H)
    (hlast : cN (EndN f 0) (n+H+v) T≤6) (hT : T=j+2)
    (hS : ∀ x, n+H≤x → x<n+H+v → f x=false)
    (hA : ∀ k, k<T → f (n+H+v+k)=true) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (H+v+T) := by
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hsep0 : cN P (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv hp
    have hf:=hS x hx hxv
    change f x=true ∧ ¬EndN f 0 x at hp
    rw [hf] at hp
    simp at hp
  have h1:=cN_add P n H v
  have h2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T hA] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  change j+1≤cN P n (H+v+T)
  omega

/-- The old0 source and the same target internally supply the head and
last-ray budgets; the result covers every v>=4 and target mass v-1. -/
theorem old_zero_short_target_free_gap (f : Nat → Bool) (n t h M m L s U v T j sOld : Nat)
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
    (hv : 4≤v)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hsOld : sOld<n)
    (hseedWin : Win f sOld (n+h+M+m+L+s+U+v-sOld))
    (hC : mass (w.drop t)=(v : Int)-1)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H]
    omega
  have hprof:=actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hTj : T=j+2 := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  have hprofOld:=actual_target_word_profile f n sOld H v 0 0 w z hpre hsOld rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by intro k hk; omega)
    (by intro x hx hx0; omega)
    (by simpa only [H,Nat.add_assoc,Nat.add_zero] using hseedWin)
  have hD : 5≤mass (w.drop sOld) := by
    have hm:=hprofOld.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,List.replicate_zero,List.append_nil] at hm
    omega
  have hfree:=early_old_mass_five_head_free f n h M m L s U v T sOld 0 w hw hpre
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hsOld (by omega)
    (by simpa only [Nat.add_zero] using hseedWin) (by decide) hD
    (fun k hk hkH=>hpos k hk (by omega))
  have hseed : tailOldRay w (z++List.replicate v false) 0 := by
    refine ⟨sOld,?_,?_,?_⟩
    · have hn : w.length=n := by rw [←hpre,seg_length]
      omega
    · have hm:=hprofOld.1
      simp only [List.replicate_zero,List.append_nil,mass_append,mass_replicate_A] at hm ⊢
      omega
    · have hk:=source_key_before_gap (w.drop sOld++z++List.replicate v false) 0 0 hprofOld.1 hprofOld.2
      rw [←runKey_append]
      simpa only [List.append_assoc] using (show runKey (w.drop sOld++z++List.replicate v false)= -2 by simpa using hk)
  have hlastword : seg f 0 (n+H+v)=w++(z++List.replicate v false) := by
    rw [show n+H+v=n+(H+v) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
  have hraw:=old_zero_fourth_ray_count_six w hw h M m L s U v T (by omega)
    (by rw [←hhead]; exact hmz)
    (by rw [←hhead]; change 1≤cntF z; rw [hSz]; omega)
    (by simpa only [z,H,hhead,List.append_assoc] using hseed)
  have he:=endable_A_run_count f (n+H+v) T (w++(z++List.replicate v false)) hlastword
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hlast : cN (EndN f 0) (n+H+v) T≤6 := by
    rw [he]
    simpa only [z,H,hhead,List.append_assoc] using hraw
  exact free_gap_charge f n H v T j hfree.2 hlast hTj
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)

end Recaman.OldZeroTargetGap
