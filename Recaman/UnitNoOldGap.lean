import Recaman.UnitOneNoOldGap
import Recaman.UnitTwoLocalFive

namespace Recaman.UnitNoOldGap


open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_two_no_old_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=2)
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
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hfree4:=Recaman.UnitTargetNoOldFour.unit_no_old_head_four f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hnoOld
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j 1 w hw hpre ht
    hh hM hm hL hs hU (by omega) rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T=j+2 := by have hbal:=hb.1; omega
  have hzeq : z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true := hword
  rw [hu1,hzeq,hv,hT] at hp
  have hl5:=Recaman.UnitTwoLocalFive.fourth_two_local_five h M m L s U T j
    (by have hx:=hb.2.1; omega) hM hb.2.2.1 hmz
    (by simpa only [List.append_assoc] using hp.1)
    (by simpa only [List.append_assoc] using hp.2)
  have heq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hnoOld)
  have hlast5 : cN (EndN f 0) (n+H+v) T≤5 := by
    rw [heq,hzeq,hv]
    exact hl5
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
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
  simp only [H,P,Nat.add_assoc] at hfree4 hlast5 hzP hc1 hc2 hpart hbad
  omega

/-- All separator lengths, with counter bounds supplied internally. -/
theorem unit_no_old_gap (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hfour:=Recaman.UnitTargetNoOldFour.unit_no_old_head_four f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hnoOld
  have hr:=Recaman.UnitTargetNoOldCounter.unit_no_old_counter f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hnoOld
  have hv2 : v≤2 := by have hh:=hr.2.1; omega
  rcases (show v=1 ∨ v=2 by omega) with hv1|hv2
  · exact Recaman.UnitOneNoOldGap.unit_one_no_old_gap f n t h M m L s U v T j w hw hpre ht
      hh hM hm hL hs hU hv1 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hnoOld
  · exact unit_two_no_old_gap f n t h M m L s U v T j w hw hpre ht
      hh hM hm hL hs hU hv2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hnoOld

end Recaman.UnitNoOldGap
