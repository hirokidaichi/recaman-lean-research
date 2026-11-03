import Recaman.MassTwoEqualCounter
import Recaman.MassTwoThreeKeys
import Recaman.NonsquareActualSupply

namespace Recaman.MassTwoEqualOldResidual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_equal_old_residual (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=2) (hC2 : C=2)
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

    (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    j=5 ∧ h+m+s=15 ∧ (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=63 := by
  have hb:=Recaman.MassTwoEqualCounter.mass_two_equal_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hw' : BlockWord (seg f 0 n) := by rw [hpre]; exact hw
  have ho:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (h+M+m+L+s+U+v) i T j
    hw' hr ht (by omega) (by have hx:=hb.2.1; omega)
    (by simpa only [Nat.add_assoc] using hA4)
    (by simpa only [Nat.add_assoc] using hgap)
    (by simpa only [Nat.add_assoc] using hseed)
    (by simpa only [Nat.add_assoc] using htarget)
  have hT : T=j+1 := by have ht:=hb.1; omega
  have hi0 : i=0 := by omega
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    dsimp [z,H]
    rw [hword]
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hl:=seg_length f n H
    rw [hmz,hl] at hc
    dsimp [H] at hc
    omega
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v 0 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by intros; omega) (by intros; omega)
    (by simpa only [hi0,H,Nat.add_zero,Nat.add_assoc] using hseed)
  have hD : mass (w.drop r)=3 := by
    have hm:=hp.1
    simp only [List.replicate_zero,List.append_nil,mass_append,mass_rep_false,hmz] at hm
    rw [hv] at hm
    omega
  have hseedkey : runKey (w.drop r++z++List.replicate v false)= -2 := by
    have he : runKey (w.drop r++z++List.replicate v false++List.replicate 0 true++List.replicate 0 false)= -2 := by
      unfold runKey
      rw [hp.1,hp.2]
      decide
    simpa only [List.replicate_zero,List.append_nil] using he
  rw [runKey_append_S,runKey_append,mass_append,hmz,hD,hSz,hv] at hseedkey
  simp only [Int.natCast_add] at hseedkey
  have htargetkey:=hb.2.2.2
  rw [hv,hC2] at htargetkey
  change runKey (w.drop t)= -runKey z-4*2*((h : Int)+(m : Int)+(s : Int)+2)+2*2^2-2*((j : Int)+1)^2 at htargetkey
  have hheadkey : runKey z=4*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))-
      2*((h : Int)+(m : Int)+(s : Int))^2 := by
    dsimp [z,H]
    rw [hword,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    grind only
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega))
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hx:=ones_seg_eq_count f n H
    dsimp [H] at hx ⊢
    rw [hword] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    omega
  have hpart:=addition_endable_partition f n H
  rw [hAc] at hpart
  change h+m+s=cN (EndN f 0) n H+cN P n H at hpart
  have hf:=cN_add P n H (v+T)
  have hSbound : h+m+s≤j+10 := by
    simp only [H,Nat.add_assoc] at hpart hf hhead10 hbad
    omega
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hur:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hCtwo : mass (w.drop t)=2 := by omega
  have hku:=Recaman.MassTwoThreeKeys.mass_two_keys (w.drop t) hu hCtwo
  have hkr:=Recaman.MassTwoThreeKeys.mass_three_keys (w.drop r) hur hD
  have hn : w.length=n := by rw [←hpre,seg_length]
  have hno : ¬(runKey (w.drop t)= -2 ∧ runKey (w.drop r)= -2) := by
    rintro ⟨h1,h2⟩
    exact Recaman.MassTwoThreeKeys.joint_minus_two_excluded w hw t r (by omega) (by omega) hCtwo hD h1 h2
  have hdiff : runKey (w.drop t)-runKey (w.drop r)=4*((h : Int)+(m : Int)+(s : Int))+10-2*((j : Int)+1)^2 := by omega
  have hkey : runKey (w.drop t)=2*((h : Int)+(m : Int)+(s : Int))^2-
      4*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))-
      8*((h : Int)+(m : Int)+(s : Int))-8-2*((j : Int)+1)^2 := by rw [hheadkey] at htargetkey; grind only
  have hc:=Recaman.MassTwoThreeKeys.old_pair_parameters ((j : Int)+1) ((h : Int)+(m : Int)+(s : Int))
    ((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) (runKey (w.drop t)) (runKey (w.drop r))
    (by have hx:=hb.2.1; omega) (by omega) hku hkr hno hdiff hkey
  exact ⟨by have hx:=hc.1; omega,by have hx:=hc.2.1; omega,hc.2.2⟩

end Recaman.MassTwoEqualOldResidual
