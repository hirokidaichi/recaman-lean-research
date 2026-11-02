import Recaman.ShortCounterQuadratic
import Recaman.ShortCounterBoxes

namespace Recaman.ShortCounterBands

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Complete five-box containment of the stated actual counter.
All old histories remain unbounded; no counter absence is asserted. -/
theorem short_counter_five_bands (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    ((v=3 ∧ C=4 ∧ 5≤j+1 ∧ j+1≤8) ∨ (v=4 ∧ C=5 ∧ j+1=5) ∨
      (v=1 ∧ 4≤C ∧ C≤8 ∧ 5≤j+1 ∧ j+1≤9) ∨
      (v=2 ∧ 4≤C ∧ C≤7 ∧ 5≤j+1 ∧ j+1≤8) ∨
      (v=3 ∧ C=5 ∧ 5≤j+1 ∧ j+1≤6)) ∧
    C≤8 ∧ v≤4 ∧ j+1≤9 ∧ h+m+s≤19 ∧ M+L+U+T≤21 ∧
    (v+2≤C → ((j : Int)+1)^2+((C : Int)-(v : Int))^2+
      4*((C : Int)-(v : Int))*(v : Int)+(v : Int)^2+24*(v : Int)≤145) := by
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hc:=Recaman.ShortCounterHeadCounts.short_counter_head_counts f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hcuts:=Recaman.ShortCounterParameterCuts.short_counter_parameter_cuts f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hq:=Recaman.ShortCounterQuadratic.short_counter_quadratic f n t h M m L s U v T j C w hw hpre ht
    hh hM hm hL hs hU hv hvpos hC4 hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hf:=Recaman.ShortCounterBoxes.five_boxes (C : Int) (v : Int) ((j : Int)+1)
    (by omega) (by omega) (by omega) (by have hr:=hb.2.1; omega)
    (by intro hh; have hx:=hcuts.2.1 (by omega); omega)
    (by intro hh; have hx:=hcuts.2.2 (by omega); omega)
    (by intro hh; exact hq.1 (by omega))
    (by intro hh; exact hq.2 (by omega))
  have hnat : (v=3 ∧ C=4 ∧ 5≤j+1 ∧ j+1≤8) ∨ (v=4 ∧ C=5 ∧ j+1=5) ∨
      (v=1 ∧ 4≤C ∧ C≤8 ∧ 5≤j+1 ∧ j+1≤9) ∨
      (v=2 ∧ 4≤C ∧ C≤7 ∧ 5≤j+1 ∧ j+1≤8) ∨
      (v=3 ∧ C=5 ∧ 5≤j+1 ∧ j+1≤6) := by
    rcases hf with h1|h2|h3|h4|h5
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
  have hcaps : C≤8 ∧ v≤4 ∧ j+1≤9 := by
    rcases hnat with h1|h2|h3|h4|h5 <;> omega
  have hbalance:=hb.1
  have hS19 : h+m+s≤19 := by
    by_cases hclose : C=v+1
    · have hx:=hc.1; omega
    · have hx:=hc.2 (by omega); omega
  have hA21 : M+L+U+T≤21 := by
    rcases hnat with h1|h2|h3|h4|h5
    all_goals try have hdeep : v+2≤C := by omega
    all_goals try have hx:=hc.2 hdeep
    all_goals omega
  exact ⟨hnat,hcaps.1,hcaps.2.1,hcaps.2.2,hS19,hA21,hq.2⟩

end Recaman.ShortCounterBands
