import Recaman.HighSubtractionTriangleSlack
import Recaman.DepthSixClockTwoFourBudget

namespace Recaman.DepthSixTightSevenWindow

open Recaman.HighSubtractionTriangleSlack Recaman.HighWindowSquareBudget
open Recaman.DepthSixFourRefinedWeight Recaman.DepthSixGapResidual
open Recaman.LevelTriangleArea Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The formerly saturated internal duration-seven branch has no
external high S and ends exactly nine clocks after that internal source.
The old/n-source alternatives are not removed by this conditional cut. -/
theorem clock_two_four_internal_seven_end (f : Nat → Bool) (n a b u q : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (htb : n+2<b) (hwin : Win f (n+2) (b+4-(n+2)))
    (hnu : n+2≤u) (huq : u+7=q) (hqb : q≤b)
    (hU : Fw f u=Fw f n) (hInner : Win f u 7) :
    b=u+9 ∧ ∀ z, (n+2≤z ∧ z<u) ∨ (q≤z ∧ z<b) →
      f z=false → Fw f z≤Fw f n-2 := by
  have hWeight := positive_four_eight_high_weight f n a b hw hpre hnb hfloor hpos hS he hcounter
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre
    hnb hfloor hpos hS he hcounter
  have hLevel := hwin.2.1
  rw [show n+2+(b+4-(n+2))=b+4 by omega] at hLevel
  let r := Fw f n-2
  have hn2r : Fw f (n+2)=r := by dsimp [r]; omega
  have hDown := fw_false_run f b 4 hS
  have hB : Fw f b=r+5 := by dsimp [r]; omega
  have htailAr : Ar f b 4= -10 := by
    rw [Ar_areaW,seg_false f b 4 hS]
    decide
  have htail : areaFromLevel f b r 4=10 := by
    unfold areaFromLevel
    rw [htailAr,hB,show r+5-r=5 by omega]
    decide
  have hFull : areaFromLevel f (n+2) r (b+4-(n+2))=0 := by
    unfold areaFromLevel
    rw [hwin.2.2,hn2r]
    simp
  have hArea := area_from_level_split f (n+2) b (b+4) r (by omega) (by omega)
  rw [hFull,show b+4-b=4 by omega,htail] at hArea
  have hWeights := low_weights_append f n r 2 (b-(n+2))
  rw [show 2+(b-(n+2))=b-n by omega] at hWeights
  have hW0 := low_weights_nonnegative f n r 2
  have hH0 := Nat.zero_le (cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n))
  have hW : lowAdditionWeights f (n+2) r (b-(n+2))≤36 := by
    change lowAdditionWeights f n r (b-n)+_≤36 at hWeight
    omega
  have huF : Fw f u=r+2 := by dsimp [r]; omega
  have hqF : Fw f q=r+3 := by
    have hh := hInner.2.1
    rw [huq] at hh
    omega
  have hWin : Win f u (q-u) := by rwa [show q-u=7 by omega]
  have htri (z : Int) (hz : 0≤z) : aboveTriangle r (r+z)=z*(z+1) := by
    unfold aboveTriangle
    rw [show r+z-r=z by omega,Int.max_eq_right hz]
  have hT0 : aboveTriangle r r=0 := by simp [aboveTriangle]
  have hcap : 2*lowAdditionWeights f (n+2) r (b-(n+2))+
      2*areaFromLevel f (n+2) r (b-(n+2))+aboveTriangle r (Fw f (n+2))≤
      aboveTriangle r (Fw f u)+aboveTriangle r (Fw f b)-aboveTriangle r (Fw f q)+
        2*((q-u : Nat) : Int)*(Fw f u-r) := by
    rw [hn2r,hT0,huF,hqF,hB,htri 2 (by omega),htri 3 (by omega),htri 5 (by omega),
      show q-u=7 by omega,show r+2-r=2 by omega]
    omega
  have hNo := tight_window_no_external_high_S f (n+2) u q b r hnu (by omega) hqb
    (by omega) (by omega) (by omega) (by omega) hWin hcap
  have hDur := no_high_S_duration f q (b-q) r (by omega) (by
    intro z hqz hzb hzS
    exact hNo z (Or.inr ⟨hqz,by omega⟩) hzS)
  rw [show q+(b-q)=b by omega,hB,hqF] at hDur
  exact ⟨by omega,by dsimp [r] at hNo; exact hNo⟩

/-- The tight branch fixes the unchanged source-earlier prefix area.
No earlier prefix is reset to a BlockWord. -/
theorem clock_two_four_internal_seven_prefix_area (f : Nat → Bool) (n a b u q : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (htb : n+2<b) (hwin : Win f (n+2) (b+4-(n+2)))
    (hnu : n+2≤u) (huq : u+7=q) (hqb : q≤b)
    (hU : Fw f u=Fw f n) (hInner : Win f u 7) :
    Fw f u-Fw f (n+2)=2 ∧ Ar f (n+2) (u-(n+2))= -33 := by
  obtain ⟨hEnd,hNo⟩ := clock_two_four_internal_seven_end f n a b u q hw hpre hnb hfloor
    hpos hS he hcounter htb hwin hnu huq hqb hU hInner
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre
    hnb hfloor hpos hS he hcounter
  have hLevel := hwin.2.1
  rw [show n+2+(b+4-(n+2))=b+4 by omega] at hLevel
  let r := Fw f n-2
  have hn2r : Fw f (n+2)=r := by dsimp [r]; omega
  have hqF : Fw f q=r+3 := by
    have hh := hInner.2.1
    rw [huq] at hh
    dsimp [r]
    omega
  have hA0 : f q=true := by
    cases hf : f q with
    | true => rfl
    | false => have hn := hNo q (Or.inr ⟨by omega,by omega⟩) hf; dsimp [r] at hqF; omega
  have hQ1 : Fw f (q+1)=r+4 := by rw [Fw_succ,hA0]; change Fw f q+1=r+4; omega
  have hA1 : f (q+1)=true := by
    cases hf : f (q+1) with
    | true => rfl
    | false => have hn := hNo (q+1) (Or.inr ⟨by omega,by omega⟩) hf; dsimp [r] at hQ1; omega
  have hTwo : areaFromLevel f q r 2=9 := by
    have hQ2 : Fw f (q+2)=r+5 := by
      rw [show q+2=q+1+1 by omega,Fw_succ,hA1]
      change Fw f (q+1)+1=r+5
      omega
    unfold areaFromLevel
    change (Ar f q 0+(Fw f (q+1)-Fw f q))+(Fw f (q+2)-Fw f q)+2*(Fw f q-r)=9
    simp only [Ar,hqF,hQ1,hQ2]
    omega
  have hInnerArea : areaFromLevel f u r (q-u)=14 := by
    unfold areaFromLevel
    rw [show q-u=7 by omega,hInner.2.2,hU]
    dsimp [r]
    omega
  have hSuffix := area_from_level_split f u q b r (by omega) hqb
  rw [show b-q=2 by omega,hTwo,hInnerArea] at hSuffix
  have hTailAr : Ar f b 4= -10 := by rw [Ar_areaW,seg_false f b 4 hS]; decide
  have hDown := fw_false_run f b 4 hS
  have hB : Fw f b=r+5 := by dsimp [r]; omega
  have hTail : areaFromLevel f b r 4=10 := by
    unfold areaFromLevel
    rw [hTailAr,hB,show r+5-r=5 by omega]
    decide
  have hFull : areaFromLevel f (n+2) r (b+4-(n+2))=0 := by
    unfold areaFromLevel
    rw [hwin.2.2,hn2r]
    simp
  have hArea := area_from_level_split f (n+2) b (b+4) r (by omega) (by omega)
  rw [hFull,show b+4-b=4 by omega,hTail] at hArea
  have hPre := area_from_level_split f (n+2) u b r hnu (by omega)
  have hOrig : areaFromLevel f (n+2) r (u-(n+2))=Ar f (n+2) (u-(n+2)) := by
    unfold areaFromLevel
    rw [hn2r]
    simp
  rw [hOrig] at hPre
  exact ⟨by dsimp [r] at hn2r; omega,by omega⟩

end Recaman.DepthSixTightSevenWindow
