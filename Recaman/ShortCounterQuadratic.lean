import Recaman.ShortCounterParameterCuts
import Recaman.ShortCounterFactorBounds

namespace Recaman.ShortCounterQuadratic

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Actual short-target counters supply factored quadratic bounds.
Count budgets and the positive square domain are derived internally. -/
theorem short_counter_quadratic (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (C=v+1 → ((j : Int)+1)^2+(C : Int)^2+28*(C : Int)≤198) ∧
    (v+2≤C → ((j : Int)+1)^2+((C : Int)-(v : Int))^2+
      4*((C : Int)-(v : Int))*(v : Int)+(v : Int)^2+24*(v : Int)≤145) := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hc:=Recaman.ShortCounterHeadCounts.short_counter_head_counts f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let z:=seg f n (h+M+m+L+s+U)
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hmz : mass z=0 := by
    simp only [z,hword,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=h+m+s := by
    have hx:=mass_cntF z
    have hl : z.length=h+M+m+L+s+U := seg_length f n _
    rw [hmz,hl] at hx
    omega
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hlo : -2≤runKey (w.drop t) := by
    have hx:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hlz:=runKey_count_lower z
  rw [hSz] at hlz
  have hkey:=hb.2.2.2
  have hcircle : ((j : Int)+1)^2+(C : Int)^2+2*(C : Int)*(v : Int)-(v : Int)^2-1≤
      (((h : Int)+(m : Int)+(s : Int))-(C : Int))^2 := by
    change runKey (w.drop t)= -runKey z-4*(C : Int)*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
      2*(v : Int)^2-2*((j : Int)+1)^2 at hkey
    simp only [Int.natCast_add] at hlz
    grind only
  have hcuts:=Recaman.ShortCounterParameterCuts.short_counter_parameter_cuts f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  refine ⟨?_,?_⟩
  · intro hclose
    exact Recaman.ShortCounterFactorBounds.close_quadratic
      ((h : Int)+(m : Int)+(s : Int)) (C : Int) (v : Int) ((j : Int)+1)
      (by have hx:=hcuts.1; omega) (by omega) (by omega)
      (by have hx:=hc.1; omega) hcircle
  · intro hdeep
    exact Recaman.ShortCounterFactorBounds.deep_quadratic
      ((h : Int)+(m : Int)+(s : Int)) (C : Int) (v : Int) ((j : Int)+1)
      (by have hx:=hcuts.1; omega) (by omega)
      (by have hx:=hc.2 hdeep; omega) hcircle

end Recaman.ShortCounterQuadratic
