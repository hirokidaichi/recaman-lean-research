import Recaman.DepthSixOldFive

namespace Recaman.OldFiveShortHighWindow

open Recaman.DepthSixOldFive Recaman.SFinalWindowLength
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Every actual supplier at least three above the selected old target
has the short SAA source, not a longer window. Source length and the
high-free joint budget are both supplied internally. -/
theorem old_five_high_source_is_SAA (f : Nat → Bool) (n a b t q : Nat) (d : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5)
    (htn : t<n) (hwin : Win f t (b+5-t))
    (hnq : n≤q) (hqb : q<b) (hd : 2≤d)
    (hq : Fw f q=Fw f n-2+d+1) (hqe : EndN f 0 q) :
    ∃ u, n≤u ∧ u+3=q ∧ Fw f u=Fw f n-2+d ∧ Win f u 3 ∧ d≤5 ∧
      2*d+5*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n) : Int)≤10 := by
  obtain ⟨u,hnu,huq,hu,hWin,hCost⟩ := old_five_actual_high_source f n a b t q d hw hpre
    hnb hfloor hpos hS he hcounter htn hwin hnq hqb hd hq hqe
  have hk := win_ge3 f u (q-u) hWin
  have hmul := Int.mul_nonneg (show 0≤d-2 by omega) (show 0≤((q-u : Nat) : Int)-1 by omega)
  have hpoly : (d-2)*(((q-u : Nat) : Int)-1)=
      d*(((q-u : Nat) : Int)-1)-2*(((q-u : Nat) : Int)-1) := by grind only
  rw [hpoly] at hmul
  have hlen : q-u=3 := by
    rcases window_three_or_at_least_seven f u (q-u) hWin with h | h
    · exact h
    · omega
  have hSmall : 2*d+5*(cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i)
      n (b-n) : Int)≤10 := by
    rw [hlen] at hCost
    omega
  exact ⟨u,hnu,by omega,hu,by rwa [hlen] at hWin,by omega,hSmall⟩

/-- The short-source classification excludes the full original
old-source gap-five counter: the required inner SAA would end in A at
the outer window's initial S. -/
theorem positive_depth_six_old_five_free_gap (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (htn : t<n) (hwin : Win f t (b+5-t)) :
    6≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n) := by
  by_cases hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5
  · let P := fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i
    have hHigh := Recaman.DepthSixFreeLocation.positive_depth_six_counter_high_free
      f n a b 5 hw hpre hnb hfloor hpos hS he hcounter
    simp only [Nat.reduceEqDiff,if_false] at hHigh
    change cN P n (b-n)≤1 at hHigh
    obtain ⟨_,_,_,hTarget,_⟩ := Recaman.DepthSixGapResidual.positive_depth_six_counter_profile
      f n a b 5 hw hpre hnb hfloor hpos hS he hcounter
    have hDown := fw_false_run f b 5 hS
    obtain ⟨q,hnq,hqb,hq,hqA⟩ := ivt f b (Fw f n+4) (by omega) (b-n) n (by omega) (by omega)
    obtain ⟨z,hnz,hzq,hz,hzA⟩ := ivt f q (Fw f n+3) (by omega) (q-n) n (by omega) (by omega)
    have hqe : EndN f 0 q := by
      by_cases h : EndN f 0 q
      · exact h
      · have hOne : 1≤cN P n (b-n) := by
          by_cases hz : 1≤cN P n (b-n)
          · exact hz
          · exact (not_of_cN_zero P n (b-n) (by omega) q hnq (by omega) ⟨by omega,hqA,h⟩).elim
        have hze : EndN f 0 z := by
          by_cases hE : EndN f 0 z
          · exact hE
          · have hTwo := two_marks_le_count P n z q (b-n) (by omega) hzq (by omega)
              ⟨by omega,hzA,hE⟩ ⟨by omega,hqA,h⟩
            omega
        obtain ⟨u,_,_,_,_,_,hCost⟩ := old_five_high_source_is_SAA f n a b t z 3 hw hpre
          hnb hfloor hpos hS he hcounter htn hwin hnz (by omega) (by omega) (by omega) hze
        change 2*3+5*(cN P n (b-n) : Int)≤10 at hCost
        omega
    obtain ⟨u,hnu,huq,huH,hWin,_,hCost⟩ := old_five_high_source_is_SAA f n a b t q 4 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin hnq hqb (by omega) (by omega) hqe
    have hZero : cN P n (b-n)=0 := by
      change 2*4+5*(cN P n (b-n) : Int)≤10 at hCost
      omega
    obtain ⟨hSu,hA1,_⟩ := win3 f u hWin
    have hU1 : Fw f (u+1)=Fw f n+1 := by
      rcases fw_cases f u with ⟨_,hA⟩ | ⟨hS,_⟩
      · simp [hSu] at hA
      · omega
    have hInner : EndN f 0 (u+1) := by
      by_cases hE : EndN f 0 (u+1)
      · exact hE
      · exact (not_of_cN_zero P n (b-n) hZero (u+1) (by omega) (by omega)
          ⟨by omega,hA1,hE⟩).elim
    obtain ⟨v,_,hvu,_,hInnerWin,_,_⟩ := old_five_high_source_is_SAA f n a b t (u+1) 2 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin (by omega) (by omega) (by omega) (by omega) hInner
    have hA := (win3 f v hInnerWin).2.2
    rw [show v+2=u by omega] at hA
    simp [hSu] at hA
  · omega

end Recaman.OldFiveShortHighWindow
