import Recaman.OldOneLastSix
import Recaman.EarlyOldFourFree
import Recaman.MomentTargetProfile

namespace Recaman.MassThreeOldOneGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.EarlyOldFourFree Recaman.OldOneLastSix
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
  change 5≤cN P n H at hhead
  simp only [Nat.add_assoc] at h1 h2 hp hsep0 hhead hlast ⊢
  omega

/-- The same mass-three target and final separator S4 supply T=j+2.
An actual oldclock1 supplies headfree5 and the internal source comparison
supplies last-count6, without a final-S local-band premise. -/
theorem mass_three_old_one_gap (f : Nat → Bool) (n t h M m L s U T j sOld : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+4 → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+4+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+4+T≤x → x<n+h+M+m+L+s+U+4+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+4+T+j-t))
    (hsOld : sOld<n)
    (hseedWin : Win f sOld (n+h+M+m+L+s+U+4+1-sOld))
    (hC : mass (w.drop t)=3)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+4+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T)
  · exact hgood
  have hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T)<j+1 := by omega
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
    dsimp [H] at hc
    omega
  have hprof:=actual_target_word_profile f n t H 4 T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hTj : T=j+2 := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  have hprofOld:=actual_target_word_profile f n sOld H 4 1 0 w z hpre hsOld rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by intro k hk; simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intro x hx hx0; omega)
    (by simpa only [H,Nat.add_assoc,Nat.add_zero] using hseedWin)
  have hD : 4≤mass (w.drop sOld) := by
    have hm:=hprofOld.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,List.replicate_zero,List.append_nil] at hm
    omega
  have hfree:=early_old_mass_four_free f n h M m L s U 4 T sOld 1 w hw hpre
    hh hM hm hL hs hU hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hsOld (by omega)
    (by simpa only [Nat.add_zero] using hseedWin) (by decide) hD
    (fun k hk hkH=>hpos k hk (by omega))
  have hseed : tailOldRay w (z++List.replicate 4 false) 1 := by
    refine ⟨sOld,?_,?_,?_⟩
    · have hn : w.length=n := by rw [←hpre,seg_length]
      omega
    · have hm:=hprofOld.1
      simp only [List.replicate_zero,List.append_nil,mass_append,mass_replicate_A] at hm ⊢
      omega
    · have hk:=source_key_before_gap (w.drop sOld++z++List.replicate 4 false) 1 0 hprofOld.1 hprofOld.2
      rw [←runKey_append]
      simpa only [List.append_assoc] using (show runKey (w.drop sOld++z++List.replicate 4 false)= -2 by simpa using hk)
  have hlastword : seg f 0 (n+H+4)=w++(z++List.replicate 4 false) := by
    rw [show n+H+4=n+(H+4) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) 4 (by simpa only [H,Nat.add_assoc] using hS4)]
  let B : Int:= -areaW z
  have hB : runKey z= -2*B := by
    unfold runKey
    rw [hmz]
    dsimp [B]
    grind only
  have hkt:=actual_zero_mass_target_key f n t H 4 T j w z hpre ht rfl hmz B
    (by dsimp [B]; omega)
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  rw [hC,hSz] at hkt
  have hkeyTarget : runKey (w.drop t)=2*B-12*((h : Int)+(m : Int)+(s : Int))-16-2*((j : Int)+1)^2 := by
    grind only
  have hbudget : M≤j+1+1 := by
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    have hpreA : seg f 0 (n+h)=w++List.replicate h false := by
      rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
    have hE:=endable_A_run_count f (n+h) M (w++List.replicate h false) hpreA hA
    have hE2:=block_rayCount_after_S hw h M
    have hpart:=addition_endable_partition f (n+h) M
    rw [count_A_run f (n+h) M hA] at hpart
    change M=cN (EndN f 0) (n+h) M+cN P (n+h) M at hpart
    have h1:=cN_add P n h M
    have h2:=cN_add P n (h+M) (m+L+s+U+4+T)
    change cN P n (h+M+m+L+s+U+4+T)<j+1 at hcounter
    simp only [Nat.add_assoc] at h1 h2 hE hpart hcounter
    omega
  have huTarget : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hraw:=old_one_target_last_six w hw h M m L s U T (j+1) (w.drop t) huTarget hC hbudget B
    (by rw [←hhead]; exact hB)
    (by simpa using hkeyTarget) hzeroMass
    (by rw [←hhead]; exact hmz)
    (by rw [←hhead]; change 11≤cntF z; rw [hSz]; exact hfree.1)
    (by simpa only [z,H,hhead,List.append_assoc] using hseed)
  have he:=endable_A_run_count f (n+H+4) T (w++(z++List.replicate 4 false)) hlastword
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hlast : cN (EndN f 0) (n+H+4) T≤6 := by
    rw [he]
    simpa only [z,H,hhead,List.append_assoc] using hraw
  exact free_gap_charge f n H 4 T j hfree.2 hlast hTj
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)

end Recaman.MassThreeOldOneGap
