import Recaman.MassThreeTargetCounter

namespace Recaman.NoOldFourSTargetBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The S4 same-target key forces headS>=10 when R>=5. -/
theorem target_head_ten_S4 (u z : List Bool) (hu : BlockWord u) (R : Nat) (hR : 5≤R)
    (hkey : runKey u= -runKey z-12*(cntF z : Int)-16-2*(R : Int)^2) :
    10≤cntF z := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hlowz:=runKey_count_lower z
  by_cases hh : 10≤cntF z
  · exact hh
  · have hp:=Int.mul_nonneg (show 0≤9-(cntF z : Int) by omega)
      (show 0≤(cntF z : Int)+3 by omega)
    have hRR:=Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
      (show 0≤(R : Int)+5 by omega)
    grind only

/-- All S4 no-old bounds are supplied by the unchanged actual counter.
The full old prefix remains quantified; no arbitrary high-mass cut is used. -/
theorem no_old_four_S_counter_bounds (f : Nat → Bool) (n t h M m L s U T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+4 → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+4+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+4+T≤x → x<n+h+M+m+L+s+U+4+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+4+T+j-t))
    (hC : mass (w.drop t)=3)
    (hno : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+4+k-r))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+4+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+4+T)<j+1) :
    T=j+2 ∧ 5≤j+1 ∧ h+m+s≤14 ∧ M≤j+2 ∧
      runKey (w.drop t)= -runKey (seg f n (h+M+m+L+s+U))-
        12*((h : Int)+(m : Int)+(s : Int))-16-2*((j : Int)+1)^2 := by
  have hb:=Recaman.MassThreeTargetCounter.mass_three_counter_parameters f n t h M m L s U 4 T j w hw hpre ht
    hh hM hm hL hs hU (Or.inr rfl) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
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
  have hAc : cN (fun x=>f x=true) n (H+4+T)=h+m+s+T := by
    have hword:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U 4 T hS hA hS2 hA2 hS3 hA3 hS4 hA4
    have hc:=ones_seg_eq_count f n (h+M+m+L+s+U+4+T)
    rw [hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    dsimp [H]
    omega
  have hT : T=j+2 := by have ht:=hb.1; omega
  have hlastEq:=Recaman.MomentNoOld.last_count_eq_local f n H 4 T z rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hno)
  have hlocal6:=Recaman.AdjacentRunSupply.fourth_ray_local_le_six h M m L s U 4 T (by decide)
  have hlast : cN (EndN f 0) (n+H+4) T≤6 := by
    rw [hlastEq]
    simpa only [z,H,hhead,List.append_assoc] using hlocal6
  have hhead10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
    (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
  have hsep : cN (EndN f 0) (n+H) 4=0 := by
    apply cN_zero_of
    intro x hx hxe he
    have hf:=hS4 x (by dsimp [H] at hx; omega) (by dsimp [H] at hxe; omega)
    have ht:=he.1
    rw [hf] at ht
    contradiction
  have he1:=cN_add (EndN f 0) n H 4
  have he2:=cN_add (EndN f 0) n (H+4) T
  have hpart:=addition_endable_partition f n (H+4+T)
  rw [hAc] at hpart
  change h+m+s+T=cN (EndN f 0) n (H+4+T)+cN P n (H+4+T) at hpart
  have hS14 : h+m+s≤14 := by
    change cN (EndN f 0) n H≤10 at hhead10
    change cN P n (H+4+T)<j+1 at hbad
    simp only [Nat.add_assoc] at he1 he2 hlast hpart hbad
    omega
  refine ⟨hT,hb.2.1,hS14,hb.2.2.1,?_⟩
  have hk:=hb.2.2.2
  change runKey (w.drop t)= -runKey z-12*((h : Int)+(m : Int)+(s : Int)+(4 : Int))+2*(4 : Int)^2-2*((j : Int)+1)^2 at hk
  change runKey (w.drop t)= -runKey z-12*((h : Int)+(m : Int)+(s : Int))-16-2*((j : Int)+1)^2
  grind only

end Recaman.NoOldFourSTargetBounds
