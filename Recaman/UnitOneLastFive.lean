import Recaman.FourthActualSeven
import Recaman.UnitTargetNoOldFour
import Recaman.UnitOneInitialSource
import Recaman.MomentNoOld
import Recaman.KFiveHeadActual
import Recaman.UnitTargetSmallHeadKey
import Recaman.MassOneTargetCounter
import Recaman.MomentTargetProfile

namespace Recaman.UnitOneLastFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_one_counter_last_five (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1)
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T=5 ∧
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)=j := by
  have hfree4:=Recaman.UnitTargetNoOldFour.unit_no_old_head_four f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hnoOld
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j 1 w hw hpre ht
    hh hM hm hL hs hU (by omega) rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let P:=fun a=>f a=true ∧ ¬EndN f 0 a
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hz : z=List.replicate h false++x := by simpa only [z,H,x,List.append_assoc] using hword
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  rw [hu1,hz,hv] at hp
  have hnone : ∀ i, ¬Recaman.FourthSourceFamilies.sourceAt false h (x++List.replicate v false) i := by
    intro i
    rw [hv]
    exact Recaman.UnitOneInitialSource.unit_one_initial_excluded x h i T j (by have hj:=hb.2.1; omega) hmz hp.1 hp.2
  have hl5:=Recaman.UnitOneInitialSource.fourth_local_five h M m L s U v T (by omega)
    (by simpa only [x,List.append_assoc] using hnone)
  have heq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hnoOld)
  have hlast5 : cN (EndN f 0) (n+H+v) T≤5 := by
    rw [heq,hz]
    simpa only [x,List.append_assoc] using hl5
  have hzP : cN P (n+H) v=0 := by
    apply cN_zero_of
    intro a ha haB he
    have hf:=hS4 a (by dsimp [H] at ha; omega) (by dsimp [H] at haB; omega)
    have heA:=he.1
    rw [hf] at heA
    contradiction
  have hc1:=cN_add P n H v
  have hc2:=cN_add P n (H+v) T
  have hpart:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hpart
  have hbal:=hb.1
  simp only [H,P,Nat.add_assoc] at hfree4 hlast5 hzP hc1 hc2 hpart hbad ⊢
  omega

end Recaman.UnitOneLastFive
