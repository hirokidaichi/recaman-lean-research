import Recaman.ShortCounterWeightedCounts
import Recaman.ShortCounterJointQuadratic
import Recaman.MassFourOneArithmetic
import Recaman.MassFourOneBands
import Recaman.MassFourOneFourteen
import Recaman.MassFourTargetKeys
import Recaman.MassFourTargetCounter
import Recaman.SeventeenSecondSource
import Recaman.FirstTwoActualBounds
import Recaman.MassFourOneBounds
import Recaman.SmallInversionActual
import Recaman.S15SecondExclusion
import Recaman.SecondRaySmallShapes
import Recaman.ShortCounterSourceCounts
import Recaman.ShortCounterJointCuts

namespace Recaman.MassFourOneR6

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Actual small-inversion head charging reduces the remaining counter to three strict parameter bands. -/
theorem mass_four_one_R6 (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    h+m+s=14 ∧ j=5 ∧ ((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=19 ∨
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=20 ∨
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=21) := by
  subst C
  subst v
  have hres:=Recaman.MassFourTargetCounter.mass_four_target_counter f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU rfl rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  by_cases hj4 : j=4
  · have hK26 : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤26 := by
      rcases hres.2 with h5 | h6 <;> omega
    have hM6 : M≤6 := by have hx:=hb.2.2.1; omega
    have hlong (hM4 : 4≤M) : 2*M≤h+3 := by
      by_cases hl : 2*M≤h+3
      · exact hl
      have hp:=Int.mul_nonneg (show 0≤(M : Int)-4 by omega) (show 0≤6-(M : Int) by omega)
      have he : ((M : Int)-4)*(6-(M : Int))=10*(M : Int)-(M : Int)^2-24 := by grind only
      have hq : 18-2*(M : Int)≤(m : Int)+(s : Int) := by omega
      have hpq:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-(18-2*(M : Int)) by omega)
      have heq : (M : Int)*((m : Int)+(s : Int)-(18-2*(M : Int)))=
        (M : Int)*((m : Int)+(s : Int))-18*(M : Int)+2*(M : Int)^2 := by grind only
      have hLp:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
      have hLe : ((L : Int)-1)*(s : Int)=(L : Int)*(s : Int)-(s : Int) := by grind only
      omega
    have hhead9 : cN (EndN f 0) n (h+M+m+L+s+U)≤9 := by
      by_cases hM3 : M≤3
      · exact Recaman.OldTargetFirstRun.three_run_count_small_first f n h M m L s U w hw hpre hM3 hs
          (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega))
      · exact Recaman.HeadRunCountBounds.head_long_first_nine f n h M m L s U w hw hpre hM hm hL hs hU
          (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkB=>hpos k hk (by omega)) (hlong (by omega))
    let H:=h+M+m+L+s+U
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
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
    change cN (EndN f 0) n H≤9 at hhead9
    change cN P n (h+M+m+L+s+U+1+T)<j+1 at hbad
    simp only [H,Nat.add_assoc] at hp hf hhead9 hbad
    omega
  · rcases hres.2 with h5 | h6
    · omega
    · exact ⟨hres.1,h6.1,h6.2⟩
end Recaman.MassFourOneR6
