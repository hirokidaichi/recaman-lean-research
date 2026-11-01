import Recaman.OldSeedInversionKey
import Recaman.SmallInversionBudget
import Recaman.MomentSmallHeadPruning
import Recaman.MomentTargetProfile
import Recaman.FourRunSupplySeventeen

namespace Recaman.LargeOldSeedGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunSupplySeventeen Recaman.FourRunTargetArea Recaman.MomentTargetProfile
open Recaman.MomentActualTarget Recaman.OldSourceKeyOrder Recaman.OldSeedInversionKey Recaman.SmallInversionBudget
open Recaman.ASourceReuse

/-- Old supplier mass at least six is excluded in the old-seeded final-band
branch by original actual counts. No head, gap or old-mass cutoff is input. -/
theorem large_old_seed_free_gap (f : Nat → Bool) (n t h M m L s U v T j q i sOld kOld : Nat)
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
    (hD : 6≤mass (w.drop sOld))
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
  have hCv : mass (w.drop t)≤(v : Int) := by omega
  have hE:=four_run_supply_le_seventeen f n h M m L s U v T w hw hpre hM hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  have hAc : cN (fun x=>f x=true) n (H+v+T)=S+T := by
    have hc:=ones_seg_eq_count f n (H+v+T)
    change ones (seg f n (h+M+m+L+s+U+v+T))=_ at hc
    rw [hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    dsimp [S]
    omega
  have hpart:=addition_endable_partition f n (H+v+T)
  rw [hAc] at hpart
  change S+T=cN (EndN f 0) n (H+v+T)+cN P n (H+v+T) at hpart
  change cN (EndN f 0) n (H+v+T)≤17 at hE
  change cN P n (H+v+T)<j+1 at hcounter
  have hS16 : S≤16 := by omega
  have hprofOld:=actual_target_word_profile f n sOld H v kOld 0 w z hpre hsOld rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by intro k hk; simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intro x hx hx0; omega)
    (by simpa only [H,Nat.add_assoc,Nat.add_zero] using hseedWin)
  let a:=z++List.replicate v false

  let I : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hmeasure : runKey z=4*I-2*(cntF z : Int)^2 := by
    change runKey (seg f n (h+M+m+L+s+U))=_
    rw [hhead,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs,hSz]
    dsimp [I,S]
    grind only
  have hu : BlockWord (w.drop sOld) :=
    block_suffix hw (w.take sOld) (w.drop sOld) (List.take_append_drop sOld w)
  have hmseed : mass (w.drop sOld)-(v : Int)+(kOld : Int)=1 := by
    have hm:=hprofOld.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,List.replicate_zero,List.append_nil] at hm
    omega
  have hkseed : runKey (w.drop sOld++z++List.replicate v false)= -2 := by
    have hk:=Recaman.ASourceReuse.source_key_before_gap (w.drop sOld++a) kOld 0
      (by simpa only [a,List.append_assoc] using hprofOld.1)
      (by simpa only [a,List.append_assoc] using hprofOld.2)
    simpa only [a,List.append_assoc] using hk
  have hkOld1 : kOld≤1 := by
    have horder:=hprior.1
    have hd:=seg_drop f 0 n sOld (by omega)
    have ht0:=seg_drop f 0 n t (by omega)
    simp only [Nat.zero_add,hpre] at hd ht0
    rw [←hd,←ht0] at horder
    omega
  have hkey:=old_seed_inversion_inequality (w.drop sOld) z hu hmz v kOld hkOld1 I hmeasure hmseed hkseed
  have hcap:=inversion_cap (cntF z : Int) (mass (w.drop sOld)) I 16 6
    (by omega) (by rw [hSz]; omega) (by decide) hD (by decide) hkey
  have hI16 : I≤16 := by omega
  have hhead8:=small_inversion_three_run_count_eight f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 hM hm hL hI16
    (fun k hk hkH=>hpos k hk (by omega))
  have hprelast : seg f 0 (n+H+v)=w++(z++List.replicate v false) := by
    rw [show n+H+v=n+(H+v) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [show seg f n H=z by rfl,seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
    simp only [List.append_assoc]
  have helast:=endable_A_run_count f (n+H+v) T (w++(z++List.replicate v false)) hprelast
    (by simpa only [H,Nat.add_assoc] using hA4)
  have holast:=block_rayCount_append hw (z++List.replicate v false)
    (by rw [cntF_append,cntF_replicate_S,hSz]; dsimp [S]; omega) T
  have hllast:=Recaman.AdjacentRunSupply.fourth_ray_local_le_six h M m L s U v T hv
  have hlast7 : cN (EndN f 0) (n+H+v) T≤7 := by
    rw [helast]
    have hl : rayCount (z++List.replicate v false) T≤6 := by
      simpa only [z,H,hhead,List.append_assoc] using hllast
    omega
  have hsep0 : cN (EndN f 0) (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have hf:=hS4 x (by dsimp [H] at *; omega) (by dsimp [H] at *; omega)
    have ht:=he.1
    rw [hf] at ht
    contradiction
  have hE1:=cN_add (EndN f 0) n H v
  have hE2:=cN_add (EndN f 0) n (H+v) T
  have hE15 : cN (EndN f 0) n (H+v+T)≤15 := by
    change cN (EndN f 0) n H≤8 at hhead8
    simp only [Nat.add_assoc] at *
    omega
  have hS14 : S≤14 := by omega
  have hcap14:=inversion_cap (cntF z : Int) (mass (w.drop sOld)) I 14 6
    (by omega) (by rw [hSz]; omega) (by decide) hD (by decide) hkey
  have hI0 : 0≤I := by
    have hp:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have hq:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int) by omega)
    dsimp [I]
    omega
  omega

end Recaman.LargeOldSeedGap
