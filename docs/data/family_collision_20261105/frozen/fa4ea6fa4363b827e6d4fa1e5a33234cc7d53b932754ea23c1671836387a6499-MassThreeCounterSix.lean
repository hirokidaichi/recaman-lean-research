import Recaman.LowOldActualSix
import Recaman.MixedZeroActualCircle
import Recaman.MassOneTargetCounter
import Recaman.SourceFamilyFreeCount

namespace Recaman.MassThreeCounterSix


open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem old_three_counter_six (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : 1≤v)
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
    (hC : mass (w.drop t)=1)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (r i : Nat) (hr : r<n) (hi : i<T)
    (hseed : Win f r (n+h+M+m+L+s+U+v+i-r))
    (hD : mass (w.drop r)=3)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    j=7 ∧ h+m+s+v=16 ∧ 2≤v ∧ v≤5 ∧
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=((v : Int)-8)^2+16 := by
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j 1 w hw hpre ht
    hh hM hm hL hs hU (by omega) rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let free:=cN P n H
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
  have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T=v+j := by
    have hm:=hprof.1
    simp only [mass_append,mass_rep_false,mass_replicate_A,hmz,hC] at hm
    omega
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hp:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hp
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hp
  have hlast:=Recaman.LowOldActualSix.low_old_actual_six f n h M m L s U v T w hw hpre
    hh hm hs (by omega) hS hA hS2 hA2 hS3 hA3 hS4 hA4 hzeroMass r i hr hi hseed (Or.inr hD)
  simp only [H,P,Nat.add_assoc] at hc1 hc2 hp hlast hbad
  have hcost : free+v≤6 := by
    dsimp [free,H,P]
    simp only [Nat.add_assoc]
    omega
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hc:=ones_seg_eq_count f n H
    dsimp [H] at hc ⊢
    rw [hhead] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hpart:=addition_endable_partition f n H
  rw [hAc] at hpart
  have hE : h+m+s+v≤16 := by
    dsimp [free,H,P] at hcost
    simp only [H,Nat.add_assoc] at hhead10 hpart hcost
    omega
  have hwalk:=(cN_walk f n H).2
  have hrel:=hpos H (by dsimp [H]; omega) (by dsimp [H]; omega)
  have hr1 : 1≤free := by
    dsimp [free,P]
    dsimp [H] at hwalk hrel hpart
    rw [hAc] at hwalk
    omega
  have hc:=Recaman.MixedZeroActualCircle.actual_mixed_old_three_circle f n H t r v T j i w z hw hpre
    rfl hmz ht hr hi hC hD
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using hseed)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hR5 : (5 : Int)≤(j : Int)+1 := by have hh:=hb.2.1; omega
  have hR8 : (j : Int)+1≤8 := by
    by_cases hx : (j : Int)+1≤8
    · exact hx
    have hp:=Int.mul_nonneg (show 0≤(j : Int)+1-9 by omega) (show 0≤(j : Int)+1+9 by omega)
    have hs:=hc.2.1
    rw [hSz] at hs
    simp only [Int.natCast_add] at hs
    grind only
  have hj : j=7 := by
    have heven:=hc.1
    have hsquare:=hc.2.1
    have hEeven:=hc.2.2.2
    rcases (show j=5 ∨ j=7 by omega) with h5|h7
    · rw [h5] at hsquare
      have hx : (cntF z : Int)+(v : Int)=9 := by omega
      rw [hx] at hEeven
      omega
    · exact h7
  have hE16 : h+m+s+v=16 := by
    have he:=hc.2.1
    rw [hj,hSz] at he
    simp only [Int.natCast_add] at he
    omega
  have hseedProfile:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
    (by intros; omega) (by simpa only [H,Nat.add_zero,Nat.add_assoc] using hseed)
  have hv2 : 2≤v := by
    have he:=hseedProfile.1
    simp only [mass_append,hmz,hD,mass_rep_false,mass_replicate_A] at he
    omega
  have hv5 : v≤5 := by omega
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hkz : runKey z=4*K-2*((h : Int)+(m : Int)+(s : Int))^2 := by
    rw [show z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true from hhead]
    rw [runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    dsimp [K]
    grind only
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hk0 : runKey [true]=0 := by decide
  have htkey:=hb.2.2.2
  rw [hu1,hk0,hkz,hj] at htkey
  have hsum : (h : Int)+(m : Int)+(s : Int)=16-(v : Int) := by omega
  rw [hsum] at htkey
  have hK : K=((v : Int)-8)^2+16 := by grind only
  exact ⟨hj,hE16,hv2,hv5,hK⟩

end Recaman.MassThreeCounterSix
