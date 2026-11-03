import Recaman.MassTwoEqualOldResidual

namespace Recaman.MassTwoEqualOldGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_equal_old_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  apply Classical.byContradiction
  intro hnot
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hc:=Recaman.MassTwoEqualOldResidual.mass_two_equal_old_residual f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC2 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos r i hr hi hseed hbad
  have hpref:=Recaman.ThreeRunSupplyBudget.two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
    (fun hp=>hpos (h+M+m+L) hp (by omega))
  have hthird:=Recaman.NonsquareActualSupply.third_actual_four_between f n h M m L s U 11 w hw hpre hs (by omega)
    hS hA hS2 hA2 hS3 hA3 (by have hx:=hc.2.2; omega) (by have hx:=hc.2.2; omega)
  have hz : cN (EndN f 0) (n+h+M+m+L) s=0 := by
    apply cN_zero_of
    intro x hx hxB he
    have ha:=he.1
    rw [hS3 x hx hxB] at ha
    contradiction
  let H:=h+M+m+L+s+U
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hc1:=cN_add (EndN f 0) n (h+M+m+L) s
  have hc2:=cN_add (EndN f 0) n (h+M+m+L+s) U
  have hhead9 : cN (EndN f 0) n H≤9 := by
    dsimp [H]
    simp only [Nat.add_assoc] at hpref hthird hz hc1 hc2 ⊢
    omega
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hx:=ones_seg_eq_count f n H
    dsimp [H] at hx ⊢
    rw [hword] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    omega
  have hp:=addition_endable_partition f n H
  rw [hAc] at hp
  change h+m+s=cN (EndN f 0) n H+cN P n H at hp
  have hf:=cN_add P n H (v+T)
  change cN P n (H+v+T)<j+1 at hbad
  simp only [H,Nat.add_assoc] at hp hf hhead9 hbad
  have hj:=hc.1
  have hS15:=hc.2.1
  omega

end Recaman.MassTwoEqualOldGap
