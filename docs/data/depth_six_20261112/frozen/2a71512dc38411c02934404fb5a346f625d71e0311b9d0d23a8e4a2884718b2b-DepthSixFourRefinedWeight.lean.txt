import Recaman.OldFiveShortHighWindow
import Recaman.GapSourceDebt

namespace Recaman.DepthSixFourRefinedWeight

open Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation Recaman.HighWindowSquareBudget
open Recaman.LevelTriangleArea Recaman.AdditionRankSlack Recaman.GapSourceDebt
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.LowTargetWeightedGap

/-- Every original gap-four counter has the high-free penalty on the
same low-weight budget, whether its chosen final source is old or local. -/
theorem positive_four_eight_high_weight (f : Nat → Bool) (n a b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4) :
    lowAdditionWeights f n (Fw f n-2) (b-n)+
      8*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤36 := by
  obtain ⟨hf,_,_,htarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre
    hnb hfloor hpos hS he hcounter
  have hdown := fw_false_run f b 4 hS
  have hit : ∃ q, n≤q ∧ q≤b ∧ Fw f q=Fw f n-6 := by
    by_cases h : ∃ q, n≤q ∧ q≤b ∧ Fw f q=Fw f n-6
    · exact h
    · have hg := positive_full_depth_five_free_gap f n a b 4 hw hpre hnb (by
        intro i hi hib
        have hh := hfloor i hi hib
        by_cases hEq : Fw f i=Fw f n-6
        · exact (h ⟨i,hi,hib,hEq⟩).elim
        · omega) hpos hS he
      omega
  obtain ⟨q,hqn,hqb,hq⟩ := hit
  obtain ⟨z,hqz,hzb,hzF,hzA⟩ := ivt f b (Fw f n-4) (by omega) (b-q) q (by omega) (by omega)
  have hOne : 1≤cN (fun i => Fw f i=Fw f n-6+1 ∧ f i=true) n (b-n) := by
    by_cases h : 1≤cN (fun i => Fw f i=Fw f n-6+1 ∧ f i=true) n (b-n)
    · exact h
    · exact (not_of_cN_zero (fun i => Fw f i=Fw f n-6+1 ∧ f i=true) n (b-n)
        (by omega) z (by omega) (by omega) ⟨by omega,hzA⟩).elim
  obtain ⟨hW,hE⟩ := low_weights_saving_at_high_free f n a (b-n) (Fw f n-6) (Fw f n-2)
    hw hpre (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have hH : cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n)=
      cN (fun i => Fw f n-6+2≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) := by
    apply cN_congr
    intro i _ _
    rw [show Fw f n-6+2=Fw f n-4 by omega]
  have hHigh := positive_depth_six_counter_high_free f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
  simp only [Nat.reduceEqDiff,if_false] at hHigh
  rw [hH] at hHigh ⊢
  omega

end Recaman.DepthSixFourRefinedWeight
