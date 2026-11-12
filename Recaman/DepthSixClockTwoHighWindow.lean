import Recaman.DepthSixLocalPreBudget

namespace Recaman.DepthSixClockTwoHighWindow

open Recaman.DepthSixLocalPreBudget Recaman.DepthSixGapResidual
open Recaman.HighWindowSquareBudget Recaman.LevelTriangleArea
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The second-clock original source yields its own area anchor and
internally extracts each high supplier's original source. The duration
and the original high-free penalty share the budget of nine. -/
theorem clock_two_five_actual_high_source (f : Nat → Bool) (n a b q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5)
    (htb : n+2<b) (hwin : Win f (n+2) (b+5-(n+2)))
    (hnq : n≤q) (hqb : q<b) (hd : 3≤d)
    (hq : Fw f q=Fw f n-2+d+1) (hqe : EndN f 0 q) :
    ∃ u, n+2≤u ∧ u<q ∧ Fw f u=Fw f n-2+d ∧ Win f u (q-u) ∧
      d*(((q-u : Nat) : Int)-1)+
        5*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤9 := by
  have hWeight := positive_five_weight_budget f n a b hw hpre hnb hfloor hpos hS he hcounter
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 5 hw hpre
    hnb hfloor hpos hS he hcounter
  have hLevel := hwin.2.1
  rw [show n+2+(b+5-(n+2))=b+5 by omega] at hLevel
  have hn2 : Fw f (n+2)=Fw f n-2 := by omega
  have hn1 : Fw f (n+1)=Fw f n-1 := by
    rcases fw_cases f n with ⟨h1,_⟩ | ⟨h1,_⟩
    · rcases fw_cases f (n+1) with ⟨h2,_⟩ | ⟨h2,_⟩ <;>
        rw [show n+1+1=n+2 by omega] at h2 <;> omega
    · exact h1
  obtain ⟨_,u,k,_,huk,hk,hlev,harea⟩ := hqe
  rw [huk,hq] at hlev
  have hu : Fw f u=Fw f n-2+d := by omega
  have hnu : n≤u := by
    by_cases h : n≤u
    · exact h
    · have hOld := (block_suffix_positive_walk f 0 n a hw hpre u (by omega) (by omega)).1
      simp only [Nat.zero_add] at hOld
      omega
  have hnu2 : n+2≤u := by
    by_cases h : n+2≤u
    · exact h
    · have hh : u=n ∨ u=n+1 := by omega
      rcases hh with rfl | rfl <;> omega
  have hWin : Win f u (q-u) := by
    rw [show q-u=k by omega]
    exact ⟨hk,by rw [huk,hq]; exact hlev,harea⟩
  let r := Fw f n-2
  have hn2r : Fw f (n+2)=r := hn2
  have hDown := fw_false_run f b 5 hS
  have hB : Fw f b=r+6 := by dsimp [r]; omega
  have htailAr : Ar f b 5= -15 := by
    rw [Ar_areaW,seg_false f b 5 hS]
    decide
  have htail : areaFromLevel f b r 5=15 := by
    unfold areaFromLevel
    rw [htailAr,hB,show r+6-r=6 by omega]
    decide
  have hFull : areaFromLevel f (n+2) r (b+5-(n+2))=0 := by
    unfold areaFromLevel
    rw [hwin.2.2,hn2r]
    simp
  have hArea := area_from_level_split f (n+2) b (b+5) r (by omega) (by omega)
  rw [hFull,show b+5-b=5 by omega,htail] at hArea
  have hWeights := low_weights_append f n r 2 (b-(n+2))
  rw [show 2+(b-(n+2))=b-n by omega] at hWeights
  have hW0 := low_weights_nonnegative f n r 2
  have hNew := internal_window_area_budget f (n+2) u q b r hnu2 (by omega) (by omega)
    (by omega) (by dsimp [r]; omega) (by dsimp [r]; omega) (by omega) hWin
  have htri (z : Int) (hz : 0≤z) : aboveTriangle r (r+z)=z*(z+1) := by
    unfold aboveTriangle
    rw [show r+z-r=z by omega,Int.max_eq_right hz]
  have hU : Fw f u=r+d := hu
  have hQ : Fw f q=r+(d+1) := by dsimp [r]; omega
  have htri0 : aboveTriangle r r=0 := by simp [aboveTriangle]
  rw [hU,hQ,hB,htri d (by omega),htri (d+1) (by omega),htri 6 (by omega),
    hn2r,htri0,show r+d-r=d by omega] at hNew
  have hpoly : d*(d+1)+6*(6+1)-(d+1)*(d+1+1)+2*((q-u : Nat) : Int)*d=
      40+2*(d*(((q-u : Nat) : Int)-1)) := by grind only
  rw [hpoly] at hNew
  change lowAdditionWeights f n r (b-n)+_≤44 at hWeight
  refine ⟨u,hnu2,by omega,hu,hWin,?_⟩
  omega

/-- The new budget of nine leaves only a three-step high source,
spends all high-free allowance, and bounds its height by four. -/
theorem clock_two_five_high_source_SAA (f : Nat → Bool) (n a b q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5)
    (htb : n+2<b) (hwin : Win f (n+2) (b+5-(n+2)))
    (hnq : n≤q) (hqb : q<b) (hd : 3≤d)
    (hq : Fw f q=Fw f n-2+d+1) (hqe : EndN f 0 q) :
    ∃ u, n+2≤u ∧ u+3=q ∧ Fw f u=Fw f n-2+d ∧ Win f u 3 ∧
      cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n)=0 ∧ d≤4 := by
  obtain ⟨u,hnu,huq,hu,hWin,hCost⟩ := clock_two_five_actual_high_source f n a b q d
    hw hpre hnb hfloor hpos hS he hcounter htb hwin hnq hqb hd hq hqe
  have hk := win_ge3 f u (q-u) hWin
  have hmul := Int.mul_nonneg (show 0≤d-3 by omega) (show 0≤((q-u : Nat) : Int)-1 by omega)
  have hpoly : (d-3)*(((q-u : Nat) : Int)-1)=
      d*(((q-u : Nat) : Int)-1)-3*(((q-u : Nat) : Int)-1) := by grind only
  rw [hpoly] at hmul
  have hlen : q-u=3 := by
    rcases Recaman.SFinalWindowLength.window_three_or_at_least_seven f u (q-u) hWin with h | h
    · exact h
    · omega
  rw [hlen] at hCost
  exact ⟨u,hnu,by omega,hu,by rwa [hlen] at hWin,by omega,by omega⟩

end Recaman.DepthSixClockTwoHighWindow
