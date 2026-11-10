import Recaman.DepthSixFreeLocation

namespace Recaman.GapSourceDebt

open Recaman.GapSquareLowAdditions Recaman.LevelTriangleArea
open Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation
open Recaman.LowTargetWeightedGap Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- An old source pays its exact positive old area in addition to the
gap square, with no bound on its mass or distance before the boundary. -/
theorem old_gap_square_with_exact_area (f : Nat → Bool) (n a t b j : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (htn : t<n) (hnb : n<b) (hS : ∀ i, b≤i → i<b+j → f i=false)
    (hwin : Win f t (b+j-t)) :
    0<Ar f t (n-t) ∧
      ((j : Int)+1)^2+Ar f t (n-t)≤
        lowAdditionWeights f n (Fw f (b+j)-1) (b-n) := by
  have htarg := hwin.2.1
  rw [show t+(b+j-t)=b+j by omega] at htarg
  obtain ⟨hlev,harea⟩ := block_suffix_positive_walk f 0 n a hw hpre t (by omega) (by omega)
  simp only [Nat.zero_add] at hlev harea
  have hs := area_split_at f t n (b+j) (by omega) (by omega)
  rw [hwin.2.2] at hs
  have hDebt : areaFromLevel f n (Fw f (b+j)-1) (b+j-n)≤-Ar f t (n-t) := by
    unfold areaFromLevel
    rw [show Fw f (b+j)-1=Fw f t by omega]
    omega
  refine ⟨harea,?_⟩
  exact gap_square_from_area_debt f n b j (Fw f (b+j)-1) (Ar f t (n-t)) hnb hS
    (by omega) (by omega) (by omega) hDebt

/-- A particular original local source can use only the low-addition
weights between that source and the start of the final gap. -/
theorem local_gap_square_after_source (f : Nat → Bool) (t b j : Nat)
    (htb : t<b) (hS : ∀ i, b≤i → i<b+j → f i=false)
    (hwin : Win f t (b+j-t)) :
    ((j : Int)+1)^2≤lowAdditionWeights f t (Fw f (b+j)-1) (b-t) := by
  have htarg := hwin.2.1
  rw [show t+(b+j-t)=b+j by omega] at htarg
  have hDebt : areaFromLevel f t (Fw f (b+j)-1) (b+j-t)≤0 := by
    unfold areaFromLevel
    rw [hwin.2.2,show Fw f t-(Fw f (b+j)-1)=0 by omega,Int.mul_zero]
    omega
  have h := gap_square_from_area_debt f t b j (Fw f (b+j)-1) 0 htb hS
    (by omega) (by omega) (by omega) hDebt
  omega

private theorem weight_at_position_le (f : Nat → Bool) (n q t : Nat) (r : Int)
    (hnq : n≤q) (hqt : q<t) :
    lowAdditionWeight f r q≤lowAdditionWeights f n r (t-n) := by
  have h0 := low_weights_append f n r (q-n) (t-q)
  rw [show q-n+(t-q)=t-n by omega,show n+(q-n)=q by omega] at h0
  have h1 := low_weights_append f q r 1 (t-q-1)
  rw [show 1+(t-q-1)=t-q by omega] at h1
  have hfirst : lowAdditionWeights f q r 1=lowAdditionWeight f r q := by
    simp [lowAdditionWeights]
  rw [hfirst] at h1
  have hp := low_weights_nonnegative f n r (q-n)
  have hs := low_weights_nonnegative f (q+1) r (t-q-1)
  omega

/-- In a depth-six positive counter of gap six, every local source for
the final target must precede every original addition on the walk floor. -/
theorem depth_six_gap_six_local_source_before_floor_addition
    (f : Nat → Bool) (n a b t q : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+6 → f i=false) (he : EndN f 0 (b+6))
    (hcounter : free f n (b-n)≤6)
    (hnt : n≤t) (htb : t<b) (hwin : Win f t (b+6-t))
    (hnq : n≤q) (hqb : q<b) (hq : Fw f q=Fw f n-6) (hqA : f q=true) :
    t≤q := by
  obtain ⟨hf,_,_,ht,_⟩ := positive_depth_six_counter_profile f n a b 6 hw hpre
    hnb hfloor hpos hS he hcounter
  let m := Fw f n-6
  have hdown := fw_false_run f b 6 hS
  have hb : m+2≤Fw f b := by dsimp [m]; omega
  obtain ⟨z,hqz,hzb,hzF,hzA⟩ := ivt f b (m+2) hb (b-q) q (by omega) (by dsimp [m]; omega)
  have hzCount : 1≤cN (fun u => Fw f u=m+1 ∧ f u=true) n (b-n) := by
    by_cases h : 1≤cN (fun u => Fw f u=m+1 ∧ f u=true) n (b-n)
    · exact h
    · exact (not_of_cN_zero (fun u => Fw f u=m+1 ∧ f u=true) n (b-n)
        (by omega) z (by omega) (by omega) ⟨by omega,hzA⟩).elim
  obtain ⟨hW,hE⟩ := low_weights_saving_at_high_free f n a (b-n) m (Fw f (b+6)-1) hw hpre
    (fun i hi hj => hfloor i hi (by omega)) (by dsimp [m]; omega)
  have hGlobal : lowAdditionWeights f n (Fw f (b+6)-1) (b-n)≤55 := by omega
  by_cases h : t≤q
  · exact h
  · have hqWeight : lowAdditionWeight f (Fw f (b+6)-1) q=7 := by
      rw [lowAdditionWeight,if_pos ⟨hqA,by omega⟩]
      omega
    have hPre := weight_at_position_le f n q t (Fw f (b+6)-1) hnq (by omega)
    rw [hqWeight] at hPre
    have hLocal := local_gap_square_after_source f t b 6 htb hS hwin
    change (49 : Int)≤_ at hLocal
    have hsplit := low_weights_append f n (Fw f (b+6)-1) (t-n) (b-t)
    rw [show t-n+(b-t)=b-n by omega,show n+(t-n)=t by omega] at hsplit
    omega

end Recaman.GapSourceDebt
