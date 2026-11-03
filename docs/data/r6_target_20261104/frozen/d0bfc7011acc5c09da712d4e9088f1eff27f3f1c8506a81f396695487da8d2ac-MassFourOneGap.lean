import Recaman.MassFourOneR6
import Recaman.NonsquareActualSupply

namespace Recaman.MassFourOneGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem long_initial (M h m s L : Int) (hM4 : 4≤M) (hM7 : M≤7)
    (hS : h+m+s=14) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hI : M*(m+s)+L*s≤21) : 2*M≤h+3 := by
  by_cases hl : 2*M≤h+3
  · exact hl
  exfalso
  have hp:=Int.mul_nonneg (show 0≤M-4 by omega) (show 0≤7-M by omega)
  have he : (M-4)*(7-M)=11*M-M^2-28 := by grind only
  have hq : 18-2*M≤m+s := by omega
  have hpq:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-(18-2*M) by omega)
  have heq : M*(m+s-(18-2*M))=M*(m+s)-18*M+2*M^2 := by grind only
  have hLp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hLe : (L-1)*s=L*s-s := by grind only
  omega

/-- The last three mass4/separator1 counter bands are excluded by nonsquare initial sources. -/
theorem mass_four_one_gap (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hv : v=1) (hC4 : C=4)
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
 :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_contra hnot
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  subst C
  subst v
  have hres:=Recaman.MassFourOneR6.mass_four_one_R6 f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU rfl rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hKlo : 18≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int) := by rcases hres.2.2 with h19|h20|h21 <;> omega
  have hKhi : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤21 := by rcases hres.2.2 with h19|h20|h21 <;> omega
  have hM7 : M≤7 := by have hx:=hb.2.2.1; omega
  have hlong (hM4 : 4≤M) : 2*M≤h+3 := by
    have hl:=long_initial (M : Int) (h : Int) (m : Int) (s : Int) (L : Int)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hKhi
    omega
  have hfirst : M≤3 ∨ 2*M≤h+3 := by
    by_cases hsmall : M≤3
    · exact Or.inl hsmall
    · exact Or.inr (hlong (by omega))
  have hpref:=Recaman.FirstTwoActualBounds.prefix_first_one f n h M m L w hw hpre hM hm hL hS hA hS2 hA2
    (hpos (h+M+m+L) (by omega) (by omega)) hfirst
  have hthird:=Recaman.NonsquareActualSupply.third_actual_four f n h M m L s U w hw hpre hs (by omega)
    hS hA hS2 hA2 hS3 hA3 hKlo (by omega)
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
  have hhead8 : cN (EndN f 0) n H≤8 := by
    simp only [Nat.add_assoc] at hpref hthird hz hc1 hc2 ⊢
    dsimp [H]
    omega
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hAc : cN (fun x=>f x=true) n H=h+m+s := by
    have hx:=ones_seg_eq_count f n (h+M+m+L+s+U)
    rw [hword] at hx
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hx
    dsimp [H]
    omega
  have hp:=addition_endable_partition f n H
  rw [hAc] at hp
  change h+m+s=cN (EndN f 0) n H+cN P n H at hp
  have hf:=cN_add P n H (1+T)
  change cN P n (h+M+m+L+s+U+1+T)<j+1 at hbad
  simp only [H,Nat.add_assoc] at hp hf hhead8 hbad
  omega

end Recaman.MassFourOneGap
