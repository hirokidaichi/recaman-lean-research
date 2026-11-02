import Recaman.ShortCounterJointCounts
import Recaman.JointShiftedCircle
import Recaman.ShortCounterParameterCuts

namespace Recaman.ShortCounterJointQuadratic

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SourceFamilyFreeCount

theorem short_counter_cross_circle (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v<C) (hvpos : 1≤v) (hC4 : 4≤C)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    ((j : Int)+1)^2+(C : Int)^2+2*(C : Int)*(v : Int)-(v : Int)^2-1+
      2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))≤
      (((h : Int)+(m : Int)+(s : Int))-(C : Int))^2 := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let z:=seg f n (h+M+m+L+s+U)
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hz : runKey z=4*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))-
      2*((h : Int)+(m : Int)+(s : Int))^2 := by
    dsimp [z]
    rw [hword,runKey_append_A,runKey_five_runs]
    grind only
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hlo : -2≤runKey (w.drop t) := by
    have hx:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hk:=hb.2.2.2
  change runKey (w.drop t)= -runKey z-4*(C : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
    2*(v : Int)^2-2*((j : Int)+1)^2 at hk
  rw [hz] at hk
  grind only

/-- The actual third/last free budget bounds the genuine head cross.
The same target then supplies shifted quadratic and linear inequalities. -/
theorem short_counter_joint_quadratic (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v<C) (hvpos : 1≤v) (hC4 : 4≤C)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    (C=v+1 → ((j : Int)+1)^2+(C : Int)^2+28*(C : Int)≤186) ∧
    (v+2≤C → ((j : Int)+1)^2+((C : Int)-(v : Int))^2+
      4*((C : Int)-(v : Int))*(v : Int)+(v : Int)^2+24*(v : Int)≤133) ∧
    (v+2≤C → 16*(C : Int)+2*(C : Int)*(v : Int)-(v : Int)^2+2*(v : Int)-76≤
      2*((j : Int)+1)*(8-(C : Int))) := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hc:=Recaman.ShortCounterHeadCounts.short_counter_head_counts f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hj:=Recaman.ShortCounterJointCounts.short_counter_joint_counts f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hcuts:=Recaman.ShortCounterParameterCuts.short_counter_parameter_cuts f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let z:=seg f n (h+M+m+L+s+U)
  let K: Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hK : (M : Int)+(L : Int)+1≤K := by
    have h1:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
    have h2:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
    have he : K-(2*(M : Int)+(L : Int))=
        (M : Int)*((m : Int)+(s : Int)-2)+(L : Int)*((s : Int)-1) := by dsimp [K]; grind only
    omega
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hz : runKey z=4*K-2*((h : Int)+(m : Int)+(s : Int))^2 := by
    dsimp [z]
    rw [hword,runKey_append_A,runKey_five_runs]
    dsimp [K]
    grind only
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hlo : -2≤runKey (w.drop t) := by
    have hx:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hkey:=hb.2.2.2
  have hcircle : ((j : Int)+1)^2+(C : Int)^2+2*(C : Int)*(v : Int)-(v : Int)^2-1+2*K≤
      (((h : Int)+(m : Int)+(s : Int))-(C : Int))^2 := by
    change runKey (w.drop t)= -runKey z-4*(C : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
      2*(v : Int)^2-2*((j : Int)+1)^2 at hkey
    rw [hz] at hkey
    grind only
  have hbounds:=Recaman.JointShiftedCircle.shifted_bounds
    ((h : Int)+(m : Int)+(s : Int)) (C : Int) (v : Int) ((j : Int)+1) K
    (by omega) (by have hx:=hcuts.1; omega)
    (by have hx:=hj.1; omega) (by have hx:=hc.1; omega)
    (by intro hd; have hx:=hc.2 (by omega); omega)
    (by have hx:=hj.2.1; omega)
    (by intro hd; have hx:=hj.2.2 (by omega); omega) hcircle
  exact ⟨fun hd=>hbounds.1 (by omega),fun hd=>hbounds.2.1 (by omega),fun hd=>hbounds.2.2 (by omega)⟩

end Recaman.ShortCounterJointQuadratic
