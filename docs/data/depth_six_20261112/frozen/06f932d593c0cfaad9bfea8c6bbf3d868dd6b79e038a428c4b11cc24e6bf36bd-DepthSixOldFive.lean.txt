import Recaman.DepthSixNestedWindow

namespace Recaman.DepthSixOldFive

open Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation Recaman.HighWindowSquareBudget
open Recaman.LevelTriangleArea Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction Recaman.LowTargetWeightedGap

/-- In an old-source gap-five actual counter, the precise old area and
the penalty for high free additions hold on the same original interval. -/
theorem old_five_counter_area_budget (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5)
    (htn : t<n) (hwin : Win f t (b+5-t)) :
    areaFromLevel f n (Fw f n-2) (b-n)≤-17 ∧
      lowAdditionWeights f n (Fw f n-2) (b-n)+
      5*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤44 := by
  obtain ⟨hf,_,_,htarget,_⟩ := positive_depth_six_counter_profile f n a b 5 hw hpre
    hnb hfloor hpos hS he hcounter
  have hdown := fw_false_run f b 5 hS
  have htLevel := hwin.2.1
  rw [show t+(b+5-t)=b+5 by omega] at htLevel
  have hmass : Fw f n-Fw f t=2 := by omega
  have hquad := block_prefix_area_quadratic_lower f n a t hw hpre (by omega)
  rw [hmass] at hquad
  have hsplit := area_split_at f t n (b+5) (by omega) (by omega)
  rw [hwin.2.2] at hsplit
  have hFull : areaFromLevel f n (Fw f n-2) (b+5-n)≤-2 := by
    unfold areaFromLevel
    have hR : Fw f t=Fw f n-2 := by omega
    rw [hR] at hsplit
    omega
  have htailAr : Ar f b 5= -15 := by
    rw [Ar_areaW,seg_false f b 5 hS]
    decide
  have htail : areaFromLevel f b (Fw f n-2) 5=15 := by
    unfold areaFromLevel
    rw [htailAr,show Fw f b-(Fw f n-2)=6 by omega]
    decide
  have ha := area_from_level_split f n b (b+5) (Fw f n-2) (by omega) (by omega)
  rw [show b+5-b=5 by omega,htail] at ha
  have hit : ∃ q, n≤q ∧ q≤b ∧ Fw f q=Fw f n-6 := by
    by_cases h : ∃ q, n≤q ∧ q≤b ∧ Fw f q=Fw f n-6
    · exact h
    · have hg := positive_full_depth_five_free_gap f n a b 5 hw hpre hnb (by
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
  rw [hH]
  exact ⟨by omega,by omega⟩

/-- For the same original old-target counter, each local high source
window pays source height times excess duration and the actual high-free
penalty from a single budget of ten. -/
theorem old_five_source_duration_budget (f : Nat → Bool) (n a b t u q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5)
    (htn : t<n) (hwin : Win f t (b+5-t))
    (hnu : n≤u) (huq : u<q) (hqb : q≤b) (hd : 0≤d)
    (hu : Fw f u=Fw f n-2+d) (huWin : Win f u (q-u)) :
    d*(((q-u : Nat) : Int)-1)+
      5*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤10 := by
  obtain ⟨hArea,hWeight⟩ := old_five_counter_area_budget f n a b t hw hpre hnb hfloor
    hpos hS he hcounter htn hwin
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 5 hw hpre
    hnb hfloor hpos hS he hcounter
  have hDown := fw_false_run f b 5 hS
  let r := Fw f n-2
  have hB : Fw f b=r+6 := by dsimp [r]; omega
  have hQ := huWin.2.1
  rw [show u+(q-u)=q by omega,hu] at hQ
  have hNew := internal_window_area_budget f n u q b r hnu huq hqb
    (by dsimp [r]; omega) (by dsimp [r]; omega) (by dsimp [r]; omega) (by omega) huWin
  have htri (z : Int) (hz : 0≤z) : aboveTriangle r (r+z)=z*(z+1) := by
    unfold aboveTriangle
    rw [show r+z-r=z by omega,Int.max_eq_right hz]
  have hU : Fw f u=r+d := hu
  have hQ' : Fw f q=r+(d+1) := by dsimp [r]; omega
  rw [hU,hQ',hB,htri d hd,htri (d+1) (by omega),htri 6 (by omega),
    show Fw f n=r+2 by dsimp [r]; omega,htri 2 (by omega),
    show r+d-r=d by omega] at hNew
  have hpoly : d*(d+1)+6*(6+1)-(d+1)*(d+1+1)+2*((q-u : Nat) : Int)*d=
      40+2*(d*(((q-u : Nat) : Int)-1)) := by grind only
  rw [hpoly] at hNew
  change lowAdditionWeights f n r (b-n)+_≤44 at hWeight
  change areaFromLevel f n r (b-n)≤-17 at hArea
  omega

/-- Above the old boundary, an actual high supplier internally provides
its local source and the coupled source-duration budget. -/
theorem old_five_actual_high_source (f : Nat → Bool) (n a b t q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5)
    (htn : t<n) (hwin : Win f t (b+5-t))
    (hnq : n≤q) (hqb : q<b) (hd : 2≤d)
    (hq : Fw f q=Fw f n-2+d+1) (hqe : EndN f 0 q) :
    ∃ u, n≤u ∧ u<q ∧ Fw f u=Fw f n-2+d ∧ Win f u (q-u) ∧
      d*(((q-u : Nat) : Int)-1)+
        5*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤10 := by
  obtain ⟨_,u,k,_,huk,hk,hlev,harea⟩ := hqe
  rw [huk,hq] at hlev
  have hu : Fw f u=Fw f n-2+d := by omega
  have hnu : n≤u := by
    by_cases h : n≤u
    · exact h
    · have hOld := (block_suffix_positive_walk f 0 n a hw hpre u (by omega) (by omega)).1
      simp only [Nat.zero_add] at hOld
      omega
  have hWin : Win f u (q-u) := by
    rw [show q-u=k by omega]
    exact ⟨hk,by rw [huk,hq]; exact hlev,harea⟩
  exact ⟨u,hnu,by omega,hu,hWin,old_five_source_duration_budget f n a b t u q d hw hpre
    hnb hfloor hpos hS he hcounter htn hwin hnu (by omega) (by omega) (by omega) hu hWin⟩

end Recaman.DepthSixOldFive
