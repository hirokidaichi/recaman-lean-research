import Recaman.OldFourInitialSS

namespace Recaman.OldFourSecondClockBudget

open Recaman.OldFourInitialSS Recaman.DepthSixOldFour Recaman.DepthSixFourRefinedWeight
open Recaman.DepthSixGapResidual Recaman.HighWindowSquareBudget Recaman.LevelTriangleArea
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The internally supplied initial SS gives a lower common area anchor.
Any high source after that original second clock pays duration plus eight
times actual high free from a budget of nine. No prefix is rebased. -/
theorem old_four_second_clock_source_budget (f : Nat → Bool) (n a b t u q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (htn : t<n) (hwin : Win f t (b+4-t))
    (hnu : n+2≤u) (huq : u<q) (hqb : q≤b) (hd : 0≤d)
    (hu : Fw f u=Fw f n-2+d) (huWin : Win f u (q-u)) :
    d*(((q-u : Nat) : Int)-1)+
      8*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤9 := by
  obtain ⟨hnS,hn1S⟩ := old_four_counter_initial_SS f n a b t hw hpre hnb hfloor hpos hS he hcounter htn hwin
  have hSS : ∀ i, n≤i → i<n+2 → f i=false := by
    intro i hi hj
    by_cases h : i=n
    · rwa [h]
    · rwa [show i=n+1 by omega]
  let r := Fw f n-2
  have hStart := fw_false_run f n 2 hSS
  have hFirstAr : Ar f n 2= -3 := by
    rw [Ar_areaW,seg_false f n 2 hSS]
    decide
  have hFirst : areaFromLevel f n r 2=1 := by
    unfold areaFromLevel
    rw [hFirstAr,show Fw f n-r=2 by dsimp [r]; omega]
    decide
  have hArea := (old_four_counter_area_budget f n a b t hw hpre hnb hfloor hpos hS he hcounter htn hwin).1
  have hW := positive_four_eight_high_weight f n a b hw hpre hnb hfloor hpos hS he hcounter
  have ha := area_from_level_split f n (n+2) b r (by omega) (by omega)
  rw [show n+2-n=2 by omega,hFirst] at ha
  have hwSplit := low_weights_append f n r 2 (b-(n+2))
  rw [show 2+(b-(n+2))=b-n by omega] at hwSplit
  have hPre := low_weights_nonnegative f n r 2
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
  have hDown := fw_false_run f b 4 hS
  have hQ := huWin.2.1
  rw [show u+(q-u)=q by omega] at hQ
  have hNew := internal_window_area_budget f (n+2) u q b r hnu huq hqb
    (by dsimp [r]; omega) (by dsimp [r]; omega) (by dsimp [r]; omega) (by dsimp [r]; omega) huWin
  have htri (z : Int) (hz : 0≤z) : aboveTriangle r (r+z)=z*(z+1) := by
    unfold aboveTriangle
    rw [show r+z-r=z by omega,Int.max_eq_right hz]
  rw [show Fw f u=r+d from hu,show Fw f q=r+(d+1) by dsimp [r]; omega,
    show Fw f b=r+5 by dsimp [r]; omega,htri d hd,htri (d+1) (by omega),htri 5 (by omega),
    show Fw f (n+2)=r+0 by dsimp [r]; omega,htri 0 (by omega),show r+d-r=d by omega] at hNew
  have hpoly : d*(d+1)+5*(5+1)-(d+1)*(d+1+1)+2*((q-u : Nat) : Int)*d=
      28+2*(d*(((q-u : Nat) : Int)-1)) := by grind only
  rw [hpoly] at hNew
  change areaFromLevel f n r (b-n)≤-12 at hArea
  change lowAdditionWeights f n r (b-n)+_≤36 at hW
  omega

end Recaman.OldFourSecondClockBudget
