import Recaman.OldSeedInversionKey
import Recaman.MomentTargetProfile
import Recaman.MomentSmallHeadPruning

namespace Recaman.EarlyOldHeadFree

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.MomentSmallHeadPruning Recaman.OldSeedInversionKey
open Recaman.ASourceReuse

/-- A large old supplier at clock0,1 or2 forces five actual free A signs
in the head, without any target or hypothetical-counter premise. -/
theorem early_old_head_free_five (f : Nat → Bool) (n h M m L s U v T sOld kOld : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
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
    (hsOld : sOld<n) (hkOld : kOld<T)
    (hseedWin : Win f sOld (n+h+M+m+L+s+U+v+kOld-sOld))
    (hkTwo : kOld≤2) (hD : 6≤mass (w.drop sOld))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    15≤h+m+s ∧ 5≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U) := by
  let H:=h+M+m+L+s+U
  let S:=h+m+s
  let z:=seg f n H
  let I : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
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
  have hmeasure : runKey z=4*I-2*(cntF z : Int)^2 := by
    change runKey (seg f n (h+M+m+L+s+U))=_
    rw [hhead,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs,hSz]
    dsimp [I,S]
    grind only
  have hprof:=actual_target_word_profile f n sOld H v kOld 0 w z hpre hsOld rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by intro k hk; simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intro x hx hx0; omega)
    (by simpa only [H,Nat.add_assoc,Nat.add_zero] using hseedWin)
  have hu : BlockWord (w.drop sOld) :=
    block_suffix hw (w.take sOld) (w.drop sOld) (List.take_append_drop sOld w)
  have hmseed : mass (w.drop sOld)-(v : Int)+(kOld : Int)=1 := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,List.replicate_zero,List.append_nil] at hm
    omega
  have hkseed : runKey (w.drop sOld++z++List.replicate v false)= -2 := by
    have hk:=source_key_before_gap (w.drop sOld++z++List.replicate v false) kOld 0 hprof.1 hprof.2
    simpa using hk
  have hkey:=old_seed_clock_inversion (w.drop sOld) z hu hmz v kOld I hmeasure hmseed hkseed
  have hI0 : 0≤I := by
    have hp:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have hq:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int) by omega)
    dsimp [I]
    omega
  have hkSq : ((kOld : Int)-1)^2≤1 := by
    have hk : kOld=0 ∨ kOld=1 ∨ kOld=2 := by omega
    rcases hk with rfl|rfl|rfl <;> decide
  have hkey0 : 2*0+2*mass (w.drop sOld)*(cntF z : Int)+(mass (w.drop sOld))^2-1≤(cntF z : Int)^2 := by
    omega
  have hS15 : 15≤S := by
    by_cases hh : 15≤S
    · exact hh
    · have hc:=inversion_cap (cntF z : Int) (mass (w.drop sOld)) 0 14 6
        (by omega) (by rw [hSz]; omega) (by decide) hD (by decide) hkey0
      omega
  have hE10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by dsimp [S] at hS15; omega) hS hA hS2 hA2 hS3 hA3 hpos
  have hAc : cN (fun x=>f x=true) n H=S := by
    have hc:=ones_seg_eq_count f n H
    change ones (seg f n (h+M+m+L+s+U))=_ at hc
    rw [hhead] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    dsimp [S]
    omega
  have hp:=addition_endable_partition f n H
  rw [hAc] at hp
  change cN (EndN f 0) n H≤10 at hE10
  constructor
  · exact hS15
  · change 5≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H
    omega

end Recaman.EarlyOldHeadFree
