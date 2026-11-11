import Recaman.OldFourHighWindowSpectrum

namespace Recaman.OldFourFreeHeight

open Recaman.OldFourHighWindowSpectrum Recaman.DepthSixFreeLocation
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- In an old-source gap-four counter, an original free addition cannot
lie more than two above the old boundary. Two earlier actual high
windows would otherwise impose opposite signs at the same clock. -/
theorem old_four_free_height_le_two (f : Nat → Bool) (n a b t x : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (htn : t<n) (hwin : Win f t (b+4-t)) (hnx : n≤x) (hxb : x<b)
    (hxA : f x=true) (hxFree : ¬EndN f 0 x) : Fw f x≤Fw f n+2 := by
  by_cases hFx : Fw f x≤Fw f n+2
  · exact hFx
  · let Q := fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i
    have hH := positive_depth_six_counter_high_free f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
    simp only [Nat.reduceEqDiff,if_false] at hH
    change cN Q n (b-n)≤1 at hH
    have hOne : 1≤cN Q n (b-n) := by
      by_cases h : 1≤cN Q n (b-n)
      · exact h
      · exact (not_of_cN_zero Q n (b-n) (by omega) x hnx (by omega) ⟨by omega,hxA,hxFree⟩).elim
    obtain ⟨q,hnq,hqx,hq,hqA⟩ := ivt f x (Fw f n+3) (by omega) (x-n) n (by omega) (by omega)
    have hActual (z : Nat) (hnz : n≤z) (hzx : z<x) (hzF : Fw f n-4≤Fw f z)
        (hzA : f z=true) : EndN f 0 z := by
      by_cases hz : EndN f 0 z
      · exact hz
      · have hTwo := two_marks_le_count Q n z x (b-n) hnz hzx (by omega)
          ⟨hzF,hzA,hz⟩ ⟨by omega,hxA,hxFree⟩
        omega
    have hqe := hActual q hnq hqx (by omega) hqA
    obtain ⟨u,hnu,huq,huH,hWin,hCases⟩ := old_four_high_source_spectrum f n a b t q 3 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin hnq (by omega) (by omega) (by omega) hqe
    have h3 : q-u=3 := by
      rcases hCases with h | h
      · exact h.1
      · have := h.2.1
        omega
    have hWin3 : Win f u 3 := by rwa [h3] at hWin
    obtain ⟨hSu,_,hA2⟩ := win3 f u hWin3
    have hPrevA : f (q-1)=true := by rwa [show q-1=u+2 by omega]
    have hPrevF : Fw f (q-1)=Fw f n+1 := by
      rcases fw_cases f (q-1) with ⟨h,_⟩ | ⟨_,h⟩
      · rw [show q-1+1=q by omega] at h
        omega
      · simp [hPrevA] at h
    have hPrevE := hActual (q-1) (by omega) (by omega) (by omega) hPrevA
    obtain ⟨v,_,_,_,hInner,hInnerCases⟩ := old_four_high_source_spectrum f n a b t (q-1) 2 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin (by omega) (by omega) (by omega) (by omega) hPrevE
    have hInner3 : q-1-v=3 := by
      rcases hInnerCases with h | h
      · exact h.1
      · have hz := h.2.2
        change cN Q n (b-n)=0 at hz
        omega
    have hInnerWin3 : Win f v 3 := by rwa [hInner3] at hInner
    have hA := (win3 f v hInnerWin3).2.1
    rw [show v+1=u by omega] at hA
    simp [hSu] at hA

/-- The upper excursion bound is internally forced by the actual source
spectrum. It is not assumed as a width restriction on the input tail. -/
theorem old_four_counter_upper_excursion (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (htn : t<n) (hwin : Win f t (b+4-t)) :
    ∀ i, n≤i → i≤b → Fw f i≤Fw f n+4 := by
  have hNoA (x : Nat) (hnx : n≤x) (hxb : x<b) (hxF : Fw f n+4≤Fw f x)
      (hxA : f x=true) : False := by
    have hxe : EndN f 0 x := by
      by_cases h : EndN f 0 x
      · exact h
      · have hBound := old_four_free_height_le_two f n a b t x hw hpre hnb hfloor hpos hS he
          hcounter htn hwin hnx hxb hxA h
        omega
    let d := Fw f x-Fw f n+1
    obtain ⟨u,hnu,huq,huH,hWin,hCases⟩ := old_four_high_source_spectrum f n a b t x d hw hpre
      hnb hfloor hpos hS he hcounter htn hwin hnx hxb (by dsimp [d]; omega) (by dsimp [d]; omega) hxe
    have h3 : x-u=3 := by
      rcases hCases with h | h
      · exact h.1
      · have := h.2.1
        dsimp [d] at this
        omega
    have hWin3 : Win f u 3 := by rwa [h3] at hWin
    obtain ⟨hSu,_,hA2⟩ := win3 f u hWin3
    have hPrevA : f (x-1)=true := by rwa [show x-1=u+2 by omega]
    have hPrevF : Fw f (x-1)=Fw f x-1 := by
      rcases fw_cases f (x-1) with ⟨h,_⟩ | ⟨_,h⟩
      · rw [show x-1+1=x by omega] at h
        omega
      · simp [hPrevA] at h
    have hPrevE : EndN f 0 (x-1) := by
      by_cases h : EndN f 0 (x-1)
      · exact h
      · have hBound := old_four_free_height_le_two f n a b t (x-1) hw hpre hnb hfloor hpos hS he
          hcounter htn hwin (by omega) (by omega) hPrevA h
        omega
    obtain ⟨v,_,_,_,hInner,hInnerCases⟩ := old_four_high_source_spectrum f n a b t (x-1) (d-1) hw hpre
      hnb hfloor hpos hS he hcounter htn hwin (by omega) (by omega) (by dsimp [d]; omega)
      (by dsimp [d]; omega) hPrevE
    have hInner3 : x-1-v=3 := by
      rcases hInnerCases with h | h
      · exact h.1
      · have := h.2.1
        dsimp [d] at this
        omega
    have hInnerWin3 : Win f v 3 := by rwa [hInner3] at hInner
    have hA := (win3 f v hInnerWin3).2.1
    rw [show v+1=u by omega] at hA
    simp [hSu] at hA
  intro i hni hib
  by_cases h : Fw f i≤Fw f n+4
  · exact h
  · obtain ⟨q,hnq,hqi,hq,hqA⟩ := ivt f i (Fw f n+5) (by omega) (i-n) n (by omega) (by omega)
    exact (hNoA q hnq (by omega) (by omega) hqA).elim

end Recaman.OldFourFreeHeight
