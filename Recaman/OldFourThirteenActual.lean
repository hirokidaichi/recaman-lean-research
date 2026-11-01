import Recaman.OldFourThirteenKey
import Recaman.EarlyOldHeadFree

namespace Recaman.OldFourThirteenActual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentTargetProfile Recaman.MomentSmallHeadPruning Recaman.OldSeedInversionKey
open Recaman.ASourceReuse

theorem actual_old_four_thirteen (f : Nat → Bool) (n h M m L s U v T sOld kOld : Nat)
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
    (hkTwo : kOld≤2) (hD : mass (w.drop sOld)=4) (hThirteen : h+m+s=13)
 :
    23≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int) ∧
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤25 := by
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
  exact Recaman.OldFourThirteenKey.same_old_four_thirteen (w.drop sOld) z hu hD hmz
    (by rw [hSz]; exact hThirteen) v kOld hkTwo I hmeasure hmseed hkseed

end Recaman.OldFourThirteenActual
