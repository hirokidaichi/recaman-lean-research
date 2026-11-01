import Recaman.EqualTargetCounter
import Recaman.FourRunSupplySeventeen

namespace Recaman.EqualTargetNoOldBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The v=C, C>=4 no-old counter supplies R5, headS15 and the first-A budget. Every old history is retained before exclusion is proved. -/
theorem equal_target_no_old_bounds (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=C) (hC4 : 4≤C)
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
    (hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    T=j+1 ∧ 5≤j+1 ∧ h+m+s≤15 ∧ M≤j+2 := by
  have hb:=Recaman.EqualTargetCounter.equal_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
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
  have hAc : cN (fun x=>f x=true) n (H+v+T)=h+m+s+T := by
    have hword:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T hS hA hS2 hA2 hS3 hA3 hS4 hA4
    have hc:=ones_seg_eq_count f n (h+M+m+L+s+U+v+T)
    rw [hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    dsimp [H]
    omega
  have hT : T=j+1 := by have ht:=hb.1; omega
  have hlastEq:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hno)
  have hlocal6:=Recaman.AdjacentRunSupply.fourth_ray_local_le_six h M m L s U v T (by omega)
  have hlast : cN (EndN f 0) (n+H+v) T≤6 := by
    rw [hlastEq]
    simpa only [z,H,hhead,List.append_assoc] using hlocal6
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hsep : cN (EndN f 0) (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxe he
    have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxe; omega)
    have ht:=he.1
    rw [hf] at ht
    contradiction
  have he1:=cN_add (EndN f 0) n H v
  have he2:=cN_add (EndN f 0) n (H+v) T
  have hpart:=addition_endable_partition f n (H+v+T)
  rw [hAc] at hpart
  change h+m+s+T=cN (EndN f 0) n (H+v+T)+cN P n (H+v+T) at hpart
  have hS15 : h+m+s≤15 := by
    change cN (EndN f 0) n H≤10 at hhead10
    change cN P n (H+v+T)<j+1 at hbad
    simp only [Nat.add_assoc] at he1 he2 hlast hpart hbad
    omega
  exact ⟨hT,hb.2.1,hS15,hb.2.2.1⟩

end Recaman.EqualTargetNoOldBounds
