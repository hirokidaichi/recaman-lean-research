import Recaman.FourthActualSeven
import Recaman.UnitTargetNoOldCounter
import Recaman.UnitTargetSmallHeadKey
import Recaman.MomentNoOld
import Recaman.MassOneTargetCounter
import Recaman.MomentTargetProfile

namespace Recaman.UnitTargetNoOldResidual

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem unit_no_old_residual (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1)
    (hnoOld : ∀ k, k<T → ∀ r, r<n → ¬Win f r (n+h+M+m+L+s+U+v+k-r)) :
    cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)=4 ∨
    (cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)=3 ∧ h+m+s=7 ∧ v=2 ∧ j=4 ∧
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5) := by
  have hc:=Recaman.UnitTargetNoOldCounter.unit_no_old_counter f n t h M m L s U v T j w hw hpre ht
    hh hM hm hL hs hU hv hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad hnoOld
  by_cases hr4 : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)=4
  · exact Or.inl hr4
  have hr3 : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U)≤3 := by omega
  have hb:=Recaman.MassOneTargetCounter.mass_one_target_counter f n t h M m L s U v T j 1 w hw hpre ht
    hh hM hm hL hs hU hv rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let r:=cN P n H
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hx:=ones_seg_eq_count f n H
    dsimp [H] at hx ⊢
    rw [hhead] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    omega
  have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  have hsml:=positive_r3_additions_free_bound f n 0 H hw hpre0
    (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hr3
  rw [hAc] at hsml
  have hK3 : 3≤K := by
    have hp:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have hq:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
    dsimp [K]
    grind only
  have hkz : runKey z=4*K-2*((h : Int)+(m : Int)+(s : Int))^2 := by
    dsimp [z,H]
    rw [hhead,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    dsimp [K]
    grind only
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hku : runKey (w.drop t)=0 := by rw [block_mass_one hu hC]; decide
  have hkey:=hb.2.2.2
  change runKey (w.drop t)= -runKey z-4*(1 : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 at hkey
  rw [hku,hkz] at hkey
  have hcircle : ((j : Int)+1)^2=((h : Int)+(m : Int)+(s : Int))^2+(v : Int)^2-
      2*((h : Int)+(m : Int)+(s : Int)+(v : Int))-2*K := by grind only
  have hout:=Recaman.UnitTargetSmallHeadKey.small_head_residual ((h : Int)+(m : Int)+(s : Int))
    (v : Int) ((j : Int)+1) K (r : Int) (by omega) (by omega) (by have hx:=hb.2.1; omega) hK3
    (by omega) (by dsimp [r,H,P]; omega) (by dsimp [r,H,P]; have hx:=hc.2.1; omega)
    (by dsimp [r,H,P]; omega) hcircle
  exact Or.inr ⟨by dsimp [r,H,P] at hout; omega,by omega,by omega,by omega,by dsimp [K] at hout; omega⟩

end Recaman.UnitTargetNoOldResidual
