import Recaman.ShortCounterWeightedCounts
import Recaman.ShortCounterJointQuadratic
import Recaman.MassFourOneArithmetic
import Recaman.MassFourOneBands
import Recaman.MassFourOneFourteen
import Recaman.MassFourTargetKeys
import Recaman.SeventeenSecondSource
import Recaman.FirstTwoActualBounds
import Recaman.MassFourOneBounds
import Recaman.SmallInversionActual
import Recaman.S15SecondExclusion
import Recaman.SecondRaySmallShapes
import Recaman.ShortCounterSourceCounts
import Recaman.ShortCounterJointCuts

namespace Recaman.MassFourTargetCounter

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Actual small-inversion head charging reduces the remaining counter to three strict parameter bands. -/
theorem mass_four_target_counter (f : Nat → Bool) (n t h M m L s U v T j C : Nat)
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
    h+m+s=14 ∧
    ((j=4 ∧ ((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=25 ∨
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=26)) ∨
    (j=5 ∧ ((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=19 ∨
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=20 ∨
      (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=21))) := by
  subst C
  subst v
  have hfourteen:=Recaman.MassFourOneFourteen.mass_four_one_fourteen f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU rfl rfl hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hb:=Recaman.ShortTargetCounter.short_target_counter f n t h M m L s U 1 T j 4 w hw hpre ht
    hh hM hm hL hs hU (by omega) (by omega) (by omega) hzeroMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hheadkey : runKey (seg f n (h+M+m+L+s+U))=4*K-2*((h : Int)+(m : Int)+(s : Int))^2 := by
    rw [hword,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    dsimp [K]
    grind only
  have hSi : (h : Int)+(m : Int)+(s : Int)=14 := by omega
  have hkey:=hb.2.2.2
  change runKey (w.drop t)= -runKey (seg f n (h+M+m+L+s+U))-
    4*4*((h : Int)+(m : Int)+(s : Int)+1)+2*1^2-2*((j : Int)+1)^2 at hkey
  rw [hheadkey,hSi] at hkey
  have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hspec:=Recaman.MassFourTargetKeys.mass_four_keys (w.drop t) hu hC
  refine ⟨hfourteen.1,?_⟩
  rcases hfourteen.2 with h5 | h6
  · have hj4:=h5.1
    rw [hj4] at hkey
    have hK : K=25 ∨ K=26 := by omega
    exact Or.inl ⟨hj4,hK⟩
  · have hj5:=h6.1
    rw [hj5] at hkey
    have hK : K=19 ∨ K=20 ∨ K=21 := by omega
    exact Or.inr ⟨hj5,hK⟩
end Recaman.MassFourTargetCounter
