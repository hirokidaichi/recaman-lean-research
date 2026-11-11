import Recaman.DepthSixFourRefinedWeight
import Recaman.GapSourceDebt
import Recaman.OldReturnNearFloorCount

namespace Recaman.DepthSixFourLocalSourcePrefix

open Recaman.DepthSixFourRefinedWeight Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation
open Recaman.OldReturnNearFloorCount Recaman.LevelTriangleArea Recaman.GapSourceDebt
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private theorem weight_at_position (f : Nat → Bool) (n q t : Nat) (r : Int)
    (hnq : n≤q) (hqt : q<t) :
    lowAdditionWeight f r q≤lowAdditionWeights f n r (t-n) := by
  have h0 := low_weights_append f n r (q-n) (t-q)
  rw [show q-n+(t-q)=t-n by omega,show n+(q-n)=q by omega] at h0
  have h1 := low_weights_append f q r 1 (t-q-1)
  rw [show 1+(t-q-1)=t-q by omega] at h1
  have hfirst : lowAdditionWeights f q r 1=lowAdditionWeight f r q := by simp [lowAdditionWeights]
  rw [hfirst] at h1
  have hp := low_weights_nonnegative f n r (q-n)
  have hs := low_weights_nonnegative f (q+1) r (t-q-1)
  omega

/-- Any local source of an original gap-four counter has at most two
original free additions before it. Three low free positions cost at
least fifteen, while the same-source prefix budget is eleven. -/
theorem local_four_source_prefix_free (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (hnt : n≤t) (htb : t<b) (hwin : Win f t (b+4-t)) :
    cN (fun i => f i=true ∧ ¬EndN f 0 i) n (t-n)≤2 := by
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre
    hnb hfloor hpos hS he hcounter
  let r := Fw f n-2
  let P := fun i => f i=true ∧ ¬EndN f 0 i
  let Q := fun i => Fw f n-4≤Fw f i ∧ P i
  change cN P n (t-n)≤2
  have hAll := positive_four_eight_high_weight f n a b hw hpre hnb hfloor hpos hS he hcounter
  have hLocal := local_gap_square_after_source f t b 4 htb hS hwin
  rw [show Fw f (b+4)-1=r by dsimp [r]; omega] at hLocal
  change (25 : Int)≤_ at hLocal
  have hsplit := low_weights_append f n r (t-n) (b-t)
  rw [show t-n+(b-t)=b-n by omega,show n+(t-n)=t by omega] at hsplit
  have hPre : lowAdditionWeights f n r (t-n)+8*(cN Q n (b-n) : Int)≤11 := by
    change lowAdditionWeights f n r (b-n)+8*(cN Q n (b-n) : Int)≤36 at hAll
    omega
  have hH := positive_depth_six_counter_high_free f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
  simp only [Nat.reduceEqDiff,if_false] at hH
  change cN Q n (b-n)≤1 at hH
  have hLowWeight (x : Nat) (hx : P x) (hF : ¬Fw f n-4≤Fw f x) : 5≤lowAdditionWeight f r x := by
    rw [lowAdditionWeight,if_pos ⟨hx.1,by dsimp [r]; omega⟩]
    dsimp [r]
    omega
  by_cases hHigh : 1≤cN Q n (b-n)
  · have hMono : cN P n (t-n)≤cN Q n (t-n) := by
      apply cN_mono
      intro x hnx hxt hx
      refine ⟨?_,hx⟩
      by_cases h : Fw f n-4≤Fw f x
      · exact h
      · have h5 := hLowWeight x hx h
        have hw := weight_at_position f n x t r hnx (by omega)
        omega
    have hPrefix := count_prefix_le Q n (t-n) (b-n) (by omega)
    omega
  · have hZero : cN Q n (b-n)=0 := by omega
    have hLow (x : Nat) (hnx : n≤x) (hxt : x<t) (hx : P x) : 5≤lowAdditionWeight f r x := by
      apply hLowWeight x hx
      intro hF
      exact not_of_cN_zero Q n (b-n) hZero x hnx (by omega) ⟨hF,hx⟩
    apply count_le_two_of_no_ordered_triple
    intro p q z hnp hpq hqz hzt hp hq hz
    have hp5 := hLow p hnp (by omega) hp
    have hq5 := hLow q (by omega) (by omega) hq
    have hz5 := hLow z (by omega) (by omega) hz
    have h0 := low_weights_append f n r (q-n) (t-q)
    rw [show q-n+(t-q)=t-n by omega,show n+(q-n)=q by omega] at h0
    have h1 := low_weights_append f q r (z-q) (t-z)
    rw [show z-q+(t-z)=t-q by omega,show q+(z-q)=z by omega] at h1
    have hwp := weight_at_position f n p q r hnp hpq
    have hwq := weight_at_position f q q z r (by omega) hqz
    have hwz := weight_at_position f z z t r (by omega) (by omega)
    omega

/-- The same source has a finite original clock bound after the new
two-free prefix reduction, using the existing r3 count theorem. -/
theorem local_four_source_clock_sixteen (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (hnt : n≤t) (htb : t<b) (hwin : Win f t (b+4-t)) : t≤n+16 := by
  have hOne := local_four_source_prefix_free f n a b t hw hpre hnb hfloor hpos hS he hcounter hnt htb hwin
  have hAdd := three_nonsupplied_additions_le_seven f n a (t-n) hw hpre
    (fun k hk hkt => hpos k hk (by omega)) (by omega)
  have hCount := cN_walk f n (t-n)
  rw [show n+(t-n)=t by omega] at hCount
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre
    hnb hfloor hpos hS he hcounter
  have hLevel := hwin.2.1
  rw [show t+(b+4-t)=b+4 by omega] at hLevel
  omega

end Recaman.DepthSixFourLocalSourcePrefix
