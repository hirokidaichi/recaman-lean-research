import Recaman.DepthSixHighWindow
import Recaman.SFinalWindowLength

namespace Recaman.DepthSixNestedWindow

open Recaman.DepthSixHighWindow Recaman.DepthSixSourceArea Recaman.DepthSixGapResidual
open Recaman.DepthSixFreeLocation Recaman.HighWindowSquareBudget Recaman.SFinalWindowLength
open Recaman.LevelTriangleArea Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The internally supplied SAA high window forces an S-ended second
window of length at least seven. Its exact source-area budget excludes
all gap-six positive depth-six actual counters, with every old history
and every other supplier retained. -/
theorem positive_depth_six_gap_six_free_gap (f : Nat → Bool) (n a b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+6 → f i=false) (he : EndN f 0 (b+6)) :
    7≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n) := by
  by_cases hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤6
  · obtain ⟨hf,_,_,htarget,_⟩ := positive_depth_six_counter_profile f n a b 6 hw hpre
      hnb hfloor hpos hS he hcounter
    let r := Fw f n-2
    have hdown := fw_false_run f b 6 hS
    have hb : Fw f b=r+7 := by dsimp [r]; omega
    obtain ⟨hW,hE⟩ := low_weights_saving_at_high_free f n a (b-n) (Fw f n-6) r hw hpre
      (fun i hi hj => hfloor i hi (by omega)) (by dsimp [r]; omega)
    have hBudget : lowAdditionWeights f n r (b-n)≤57 := by omega
    have hspec := gap_six_actual_source_area_spectrum f n a b hw hpre hnb hfloor hpos hS he hcounter
    have hFull : areaFromLevel f n r (b+6-n)≤1 := by dsimp [r]; omega
    have htailAr : Ar f b 6= -21 := by
      rw [Ar_areaW,seg_false f b 6 hS]
      decide
    have htail : areaFromLevel f b r 6=21 := by
      unfold areaFromLevel
      rw [htailAr,hb,show r+7-r=7 by omega]
      decide
    have ha := area_from_level_split f n b (b+6) r (by omega) (by omega)
    rw [show b+6-b=6 by omega,htail] at ha
    obtain ⟨u,hnu,hu3b,huH,hWin3,hInner⟩ := gap_six_high_window_and_first_supply
      f n a b hw hpre hnb hfloor hpos hS he hcounter
    have hSu := (win3 f u hWin3).1
    have hU1 : Fw f (u+1)=r+4 := by
      rcases fw_cases f u with ⟨_,hA⟩ | ⟨hS,_⟩
      · simp [hSu] at hA
      · dsimp [r]; omega
    obtain ⟨_,v,k,_,hvk,hk,hlev,hAr⟩ := hInner
    have hWin : Win f v k := ⟨hk,hlev,hAr⟩
    rw [hvk,hU1] at hlev
    have hvH : Fw f v=r+3 := by omega
    have hnv : n≤v := by
      by_cases h : n≤v
      · exact h
      · have hOld := (block_suffix_positive_walk f 0 n a hw hpre v (by omega) (by omega)).1
        simp only [Nat.zero_add] at hOld
        dsimp [r] at hvH
        omega
    have hSeven := window_ending_S_length f v k hWin (by rwa [show v+k-1=u by omega])
    have hLen : u+1-v=k := by omega
    have hWin' : Win f v (u+1-v) := by rwa [hLen]
    have hNew := internal_window_area_budget f n v (u+1) b r hnv (by omega) (by omega)
      (by dsimp [r]; omega) (by omega) (by omega) (by omega) hWin'
    have htri (d : Int) : aboveTriangle r (r+d)=max 0 d*(max 0 d+1) := by
      unfold aboveTriangle
      rw [show r+d-r=d by omega]
    rw [hvH,hU1,hb,htri 3,htri 4,htri 7,
      show Fw f n=r+2 by dsimp [r]; omega,htri 2,hLen,
      show max (0 : Int) 3*(max 0 3+1)=12 by decide,
      show max (0 : Int) 4*(max 0 4+1)=20 by decide,
      show max (0 : Int) 7*(max 0 7+1)=56 by decide,
      show max (0 : Int) 2*(max 0 2+1)=6 by decide,
      show r+3-r=3 by omega] at hNew
    omega
  · omega

end Recaman.DepthSixNestedWindow
