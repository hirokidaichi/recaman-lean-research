import Recaman.DepthSixClockFourPrefix

namespace Recaman.DepthSixClockFourHighWindow

open Recaman.DepthSixClockFourPrefix Recaman.DepthSixFourRefinedWeight Recaman.DepthSixLocalPreBudget
open Recaman.DepthSixGapResidual Recaman.SFinalWindowLength Recaman.HighWindowSquareBudget
open Recaman.LevelTriangleArea Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Every actual high supplier in the clock-four source branch has a
three-step source. The bound of eleven is internally derived from the
same-prefix area and the spent high free, in both remaining gap sizes. -/
theorem clock_four_high_source_SAA (f : Nat → Bool) (n a b j q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤j)
    (hj : j=4 ∨ j=5) (htb : n+4<b) (hwin : Win f (n+4) (b+j-(n+4)))
    (hnq : n≤q) (hqb : q<b) (hd : 2≤d) (hq : Fw f q=Fw f n-2+d+1) (hqe : EndN f 0 q) :
    ∃ u, n≤u ∧ u+3=q ∧ Fw f u=Fw f n-2+d ∧ Win f u 3 := by
  obtain ⟨_,hFull,hHigh,_⟩ := clock_four_actual_prefix_packet f n a b j hw hpre hnb hfloor hpos hS he hcounter hj htb hwin
  obtain ⟨_,u,k,_,huk,hk,hLev,hAr⟩ := hqe
  rw [huk,hq] at hLev
  have hu : Fw f u=Fw f n-2+d := by omega
  have hnu : n≤u := by
    by_cases h : n≤u
    · exact h
    · have hOld := (block_suffix_positive_walk f 0 n a hw hpre u (by omega) (by omega)).1
      simp only [Nat.zero_add] at hOld
      omega
  have hUWin : Win f u (q-u) := by
    rw [show q-u=k by omega]
    exact ⟨hk,by rw [huk,hq]; exact hLev,hAr⟩
  let r := Fw f n-2
  have hNew := internal_window_area_budget f n u q b r hnu (by omega) (by omega)
    (by dsimp [r]; omega) (by dsimp [r]; omega) (by dsimp [r]; omega)
    (by obtain ⟨_,_,_,hT,_⟩ := positive_depth_six_counter_profile f n a b j hw hpre hnb hfloor hpos hS he hcounter
        have hD := fw_false_run f b j hS
        dsimp [r]; omega) hUWin
  have htri (z : Int) (hz : 0≤z) : aboveTriangle r (r+z)=z*(z+1) := by
    unfold aboveTriangle
    rw [show r+z-r=z by omega,Int.max_eq_right hz]
  rw [show Fw f u=r+d from hu,show Fw f q=r+(d+1) by dsimp [r]; omega,
    htri d (by omega),htri (d+1) (by omega),
    show Fw f n=r+2 by dsimp [r]; omega,htri 2 (by omega),show r+d-r=d by omega] at hNew
  have hpoly (Z : Int) : d*(d+1)+Z-(d+1)*(d+1+1)+2*((q-u : Nat) : Int)*d=
      Z-2+2*(d*(((q-u : Nat) : Int)-1)) := by grind only
  rw [hpoly] at hNew
  have hCost : d*(((q-u : Nat) : Int)-1)≤11 := by
    obtain ⟨_,_,_,hT,_⟩ := positive_depth_six_counter_profile f n a b j hw hpre hnb hfloor hpos hS he hcounter
    rcases hj with rfl | rfl
    · have hW := positive_four_eight_high_weight f n a b hw hpre hnb hfloor hpos hS he hcounter
      rw [hHigh] at hW
      have hD := fw_false_run f b 4 hS
      have hB : Fw f b=r+5 := by dsimp [r]; omega
      have hBT : aboveTriangle r (Fw f b)=30 := by rw [hB,htri 5 (by omega)]; decide
      rw [hBT] at hNew
      have hTailAr : Ar f b 4= -10 := by rw [Ar_areaW,seg_false f b 4 hS]; decide
      have hTail : areaFromLevel f b r 4=10 := by
        unfold areaFromLevel
        rw [hTailAr,show Fw f b-r=5 by omega]
        decide
      have ha := area_from_level_split f n b (b+4) r (by omega) (by omega)
      rw [show b+4-b=4 by omega,hTail] at ha
      change areaFromLevel f n r (b+4-n)≤4 at hFull
      change lowAdditionWeights f n r (b-n)+_≤36 at hW
      omega
    · have hW := positive_five_weight_budget f n a b hw hpre hnb hfloor hpos hS he hcounter
      rw [hHigh] at hW
      have hD := fw_false_run f b 5 hS
      have hB : Fw f b=r+6 := by dsimp [r]; omega
      have hBT : aboveTriangle r (Fw f b)=42 := by rw [hB,htri 6 (by omega)]; decide
      rw [hBT] at hNew
      have hTailAr : Ar f b 5= -15 := by rw [Ar_areaW,seg_false f b 5 hS]; decide
      have hTail : areaFromLevel f b r 5=15 := by
        unfold areaFromLevel
        rw [hTailAr,show Fw f b-r=6 by omega]
        decide
      have ha := area_from_level_split f n b (b+5) r (by omega) (by omega)
      rw [show b+5-b=5 by omega,hTail] at ha
      change areaFromLevel f n r (b+5-n)≤4 at hFull
      change lowAdditionWeights f n r (b-n)+_≤44 at hW
      omega
  have hmul := Int.mul_nonneg (show 0≤d-2 by omega) (show 0≤((q-u : Nat) : Int)-1 by have := hUWin.1; omega)
  have hmEq : (d-2)*(((q-u : Nat) : Int)-1)=d*(((q-u : Nat) : Int)-1)-2*(((q-u : Nat) : Int)-1) := by grind only
  rw [hmEq] at hmul
  have h3 : q-u=3 := by
    rcases window_three_or_at_least_seven f u (q-u) hUWin with h | h
    · exact h
    · omega
  exact ⟨u,hnu,by omega,hu,by rwa [h3] at hUWin⟩

end Recaman.DepthSixClockFourHighWindow
