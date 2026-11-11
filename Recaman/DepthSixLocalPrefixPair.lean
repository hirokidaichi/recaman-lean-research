import Recaman.DepthSixFourLocalSourcePrefix
import Recaman.LowCrossSupplyCount

namespace Recaman.DepthSixLocalPrefixPair

open Recaman.DepthSixFourRefinedWeight Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation
open Recaman.LowCrossSupplyCount Recaman.LevelTriangleArea Recaman.GapSourceDebt
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private theorem weight_at_position (f : Nat → Bool) (n q t : Nat) (r : Int)
    (hnq : n≤q) (hqt : q<t) : lowAdditionWeight f r q≤lowAdditionWeights f n r (t-n) := by
  have h0 := low_weights_append f n r (q-n) (t-q)
  rw [show q-n+(t-q)=t-n by omega,show n+(q-n)=q by omega] at h0
  have h1 := low_weights_append f q r 1 (t-q-1)
  rw [show 1+(t-q-1)=t-q by omega] at h1
  have hfirst : lowAdditionWeights f q r 1=lowAdditionWeight f r q := by simp [lowAdditionWeights]
  rw [hfirst] at h1
  have hp := low_weights_nonnegative f n r (q-n)
  have hs := low_weights_nonnegative f (q+1) r (t-q-1)
  omega

private theorem two_weights (f : Nat → Bool) (n p q t : Nat) (r : Int)
    (hnp : n≤p) (hnq : n≤q) (hpt : p<t) (hqt : q<t) (hne : p≠q) :
    lowAdditionWeight f r p+lowAdditionWeight f r q≤lowAdditionWeights f n r (t-n) := by
  have ordered (u v : Nat) (hnu : n≤u) (huv : u<v) (hvt : v<t) :
      lowAdditionWeight f r u+lowAdditionWeight f r v≤lowAdditionWeights f n r (t-n) := by
    have hw := low_weights_append f n r (v-n) (t-v)
    rw [show v-n+(t-v)=t-n by omega,show n+(v-n)=v by omega] at hw
    have h0 := weight_at_position f n u v r hnu huv
    have h1 := weight_at_position f v v t r (by omega) hvt
    omega
  by_cases hpq : p<q
  · exact ordered p q hnp hpq hqt
  · have hh := ordered q p hnq (by omega) hpt
    omega

/-- Two earlier low free additions would raise the original prefix floor
by one, whose recovery then forces a high free. This excludes the last
two-free prefix case, improving the source bound from two to one. -/
theorem local_four_source_prefix_free_one (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (hnt : n≤t) (htb : t<b) (hwin : Win f t (b+4-t)) :
    cN (fun i => f i=true ∧ ¬EndN f 0 i) n (t-n)≤1 := by
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
  let r := Fw f n-2
  let m := Fw f n-6
  let P := fun i => f i=true ∧ ¬EndN f 0 i
  let Q := fun i => Fw f n-4≤Fw f i ∧ P i
  have hLevel := hwin.2.1
  rw [show t+(b+4-t)=b+4 by omega] at hLevel
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
  have hOne (x : Nat) (hnx : n≤x) (hxt : x<t) (hx : Q x) : 1≤cN Q n (b-n) := by
    by_cases h : 1≤cN Q n (b-n)
    · exact h
    · exact (not_of_cN_zero Q n (b-n) (by omega) x hnx (by omega) hx).elim
  have hLow (x : Nat) (hx : P x) (hF : ¬Fw f n-4≤Fw f x) : 5≤lowAdditionWeight f r x := by
    rw [lowAdditionWeight,if_pos ⟨hx.1,by dsimp [r]; omega⟩]
    dsimp [r]
    omega
  have hPair (p q : Nat) (hnp : n≤p) (hpq : p<q) (hqt : q<t) (hp : P p) (hq : P q) : False := by
    have hwp := weight_at_position f n p t r hnp (by omega)
    have hwq := weight_at_position f n q t r (by omega) hqt
    have hTwo := two_weights f n p q t r hnp (by omega) (by omega) hqt (by omega)
    by_cases hFp : Fw f n-4≤Fw f p
    · have h1 := hOne p hnp (by omega) ⟨hFp,hp⟩
      by_cases hFq : Fw f n-4≤Fw f q
      · have hh := two_marks_le_count Q n p q (b-n) hnp hpq (by omega) ⟨hFp,hp⟩ ⟨hFq,hq⟩
        omega
      · have hh := hLow q hq hFq
        omega
    · have hp5 := hLow p hp hFp
      by_cases hFq : Fw f n-4≤Fw f q
      · have h1 := hOne q (by omega) hqt ⟨hFq,hq⟩
        omega
      · have hq5 := hLow q hq hFq
        have hZero : cN Q n (b-n)=0 := by omega
        have hPLevel : Fw f p=m+1 := by
          have hmin := hfloor p hnp (by omega)
          by_cases hEq : Fw f p=m
          · have hp7 : lowAdditionWeight f r p=7 := by
              rw [lowAdditionWeight,if_pos ⟨hp.1,by dsimp [m,r] at *; omega⟩,hEq]
              dsimp [m,r]
              omega
            omega
          · dsimp [m] at hEq ⊢
            omega
        have hNoFloor (z : Nat) (hnz : n≤z) (hzt : z<t) (hzF : Fw f z=m) (hzA : f z=true) : False := by
          have hz7 : lowAdditionWeight f r z=7 := by
            rw [lowAdditionWeight,if_pos ⟨hzA,by dsimp [m,r] at *; omega⟩,hzF]
            dsimp [m,r]
            omega
          have hne : p≠z := by
            intro heq
            rw [heq,hzF] at hPLevel
            omega
          have hh := two_weights f n p z t r hnp hnz (by omega) hzt hne
          omega
        have hRaised := floor_lemma f n t (m+1) (by dsimp [m]; omega) (by
          intro z hnz hzt hzF hzA
          exact hNoFloor z hnz hzt (by omega) hzA)
        obtain ⟨z,hpz,hzt,hzF,hzA⟩ := ivt f t (m+3) (by dsimp [m]; omega)
          (t-p) p (by omega) (by omega)
        have hzNo : ¬EndN f 0 z := block_prefix_low_clock_not_endable f n a z hw hpre (by omega)
          (m+1) (fun i hi hj => hRaised i hi (by omega)) (by omega)
        exact not_of_cN_zero Q n (b-n) hZero z (by omega) (by omega)
          ⟨by dsimp [m] at hzF; omega,hzA,hzNo⟩
  apply interval_unique_count
  intro p q hnp hpt hnq hqt hp hq
  by_cases h : p=q
  · exact h
  · by_cases hpq : p<q
    · exact (hPair p q hnp hpq (by omega) hp hq).elim
    · exact (hPair q p hnq (by omega) (by omega) hq hp).elim

end Recaman.DepthSixLocalPrefixPair
