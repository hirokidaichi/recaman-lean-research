import Recaman.DepthSixSourceArea

namespace Recaman.DepthSixOldHead

open Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation Recaman.DepthSixPairResidual
open Recaman.FloorSupplyPairCharge Recaman.GapSourceDebt Recaman.LowTargetWeightedGap
open Recaman.LevelTriangleArea Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction Classical

/-- A depth-six gap-six positive counter with an old source cannot start
with five subtractions and then its first addition. That early free
addition is unavailable to both images of every floor supply. -/
theorem old_gap_six_excludes_head_five (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+6 → f i=false) (he : EndN f 0 (b+6))
    (hcounter : free f n (b-n)≤6) (htn : t<n) (hwin : Win f t (b+6-t))
    (hHead : n+5<b) (hS5 : ∀ i, n≤i → i<n+5 → f i=false) (hA5 : f (n+5)=true) :
    False := by
  obtain ⟨hf,_,_,htarget,_⟩ := positive_depth_six_counter_profile f n a b 6 hw hpre
    hnb hfloor hpos hS he hcounter
  let m := Fw f n-6
  have hFw5 := fw_false_run f n 5 hS5
  have h5 : Fw f (n+5)=m+1 := by dsimp [m]; omega
  have hcut (i : Nat) (hni : n≤i) (hi : i<n+6) : Fw f i≠m := by
    have hwalk := fw_false_run f n (i-n) (fun u hu hui => hS5 u hu (by omega))
    rw [show n+(i-n)=i by omega] at hwalk
    dsimp [m]
    omega
  have h5Free : ¬EndN f 0 (n+5) :=
    block_prefix_low_clock_not_endable f n a (n+5) hw hpre (by omega) m
      (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have hPair := floor_supply_pair_charge_after_cut f n a (b-n) (n+6) m hw hpre
    (fun i hi hj => hfloor i hi (by omega)) hcut
  let P := fun u => f u=true ∧ ¬EndN f 0 u
  have hMono : cN (fun u => n+6≤u ∧ Fw f u≤m+1 ∧ f u=true ∧ ¬EndN f 0 u) n (b-n)≤
      cN (fun u => P u ∧ n+6≤u) n (b-n) := by
    apply cN_mono
    intro u _ _ hu
    exact ⟨hu.2.2,hu.1⟩
  have hOutside : 1≤cN (fun u => P u ∧ ¬n+6≤u) n (b-n) := by
    by_cases h : 1≤cN (fun u => P u ∧ ¬n+6≤u) n (b-n)
    · exact h
    · exact (not_of_cN_zero (fun u => P u ∧ ¬n+6≤u) n (b-n) (by omega)
        (n+5) (by omega) (by omega) ⟨⟨hA5,h5Free⟩,by omega⟩).elim
  have hSplit := cN_split P (fun u => n+6≤u) n (b-n)
  change free f n (b-n)=_ at hSplit
  have hE2 : cN (fun u => Fw f u=m+2 ∧ EndN f 0 u) n (b-n)≤2 := by omega
  have hit : ∃ q, n≤q ∧ q≤b ∧ Fw f q=m := by
    by_cases h : ∃ q, n≤q ∧ q≤b ∧ Fw f q=m
    · exact h
    · have hgap := positive_full_depth_five_free_gap f n a b 6 hw hpre hnb (by
        intro i hi hib
        have hh := hfloor i hi hib
        by_cases hEq : Fw f i=m
        · exact (h ⟨i,hi,hib,hEq⟩).elim
        · dsimp [m] at hEq
          omega) hpos hS he
      omega
  obtain ⟨q,hqn,hqb,hqF⟩ := hit
  have hq5 : n+5<q := by
    by_cases h : n+5<q
    · exact h
    · exact (hcut q hqn (by omega) hqF).elim
  have hdown := fw_false_run f b 6 hS
  have hb : m+2≤Fw f b := by dsimp [m]; omega
  obtain ⟨z,hqz,hzb,hzF,hzA⟩ := ivt f b (m+2) hb (b-q) q (by omega) (by omega)
  have hTwo := two_marks_le_count (fun u => Fw f u=m+1 ∧ f u=true) n (n+5) z (b-n)
    (by omega) (by omega) (by omega) ⟨h5,hA5⟩ ⟨by omega,hzA⟩
  have hW := low_weights_saving_at_second_floor f n a (b-n) m (Fw f (b+6)-1) hw hpre
    (fun i hi hj => hfloor i hi (by omega)) (by dsimp [m]; omega)
  have hBound : lowAdditionWeights f n (Fw f (b+6)-1) (b-n)≤50 := by omega
  have hOld := old_gap_square_with_exact_area f n a t b 6 hw hpre htn hnb hS hwin
  have htLevel := hwin.2.1
  rw [show t+(b+6-t)=b+6 by omega] at htLevel
  have hquad := block_prefix_area_quadratic_lower f n a t hw hpre (by omega)
  rw [show Fw f n-Fw f t=2 by omega] at hquad
  have hDebt : 2≤Ar f t (n-t) := by omega
  change 0<Ar f t (n-t) ∧ (49 : Int)+Ar f t (n-t)≤_ at hOld
  omega

end Recaman.DepthSixOldHead
