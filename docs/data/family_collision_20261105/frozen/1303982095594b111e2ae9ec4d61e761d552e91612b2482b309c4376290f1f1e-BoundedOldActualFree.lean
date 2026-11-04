import Recaman.BoundedOldSourceFloor
import Recaman.MomentTargetProfile
import Recaman.SourceFamilyFreeCount

namespace Recaman.BoundedOldActualFree


open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem bounded_old_head_free_four (f : Nat → Bool) (n h M m L s U v T : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hh : 1≤h) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hzero : M+L+U=h+m+s) (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r))
    (hregion : (3≤mass (w.drop r) ∧ v≤5) ∨ (4≤mass (w.drop r) ∧ v≤6))
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    4≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U) := by
  by_cases hgood : 4≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)≤3 := by omega
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by simp only [z,H,hword,mass_append,mass_rep_false,mass_replicate_A]; omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl : z.length=H := seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hc:=ones_seg_eq_count f n H
    rw [show z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true from hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hb:=positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre) hpos hbad
  have hS7 : cntF z≤7 := by rw [hSz]; rw [hAc] at hb; omega
  have hK : 3≤K := by
    have hp:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have hq:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
    dsimp [K]
    grind only
  have hkz : runKey z=4*K-2*(cntF z : Int)^2 := by
    rw [hSz,show z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true from hword]
    rw [runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    simp only [Int.natCast_add]
    dsimp [K]
    grind only
  have hu:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intros; omega) (by simpa only [H,Nat.add_zero,Nat.add_assoc] using hseed)
  have hmass : mass (w.drop r)-(v : Int)+(i : Int)=1 := by
    have hh:=hp.1
    simp only [mass_append,hmz,mass_rep_false,mass_replicate_A] at hh
    omega
  have hk:=Recaman.ASourceReuse.source_key_before_gap (w.drop r++z++List.replicate v false) i 0
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hp.1)
    (by simpa only [List.replicate_zero,List.append_nil,List.append_assoc] using hp.2)
  exact False.elim (Recaman.BoundedOldSourceFloor.small_head_seed_excluded (w.drop r) z hu hmz
    (by rw [hSz]; omega) hS7 K hK hkz v i hregion hmass (by simpa using hk))

end Recaman.BoundedOldActualFree
