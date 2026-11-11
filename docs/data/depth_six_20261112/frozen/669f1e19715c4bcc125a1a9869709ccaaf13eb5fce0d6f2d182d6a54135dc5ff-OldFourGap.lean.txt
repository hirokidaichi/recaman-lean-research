import Recaman.OldFourHighFreeZero
import Recaman.SevenWindowPrefixFive

namespace Recaman.OldFourGap

open Recaman.OldFourHighFreeZero Recaman.OldFourInitialSS Recaman.OldFourSecondClockBudget
open Recaman.OldFourHighWindowSpectrum Recaman.SevenWindowPrefixFive Recaman.DepthSixGapResidual
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Every original positive depth-six tail with an old actual source for
the gap-four target has five free additions. The high-free count and
initial SS are internally supplied before the two-window contradiction. -/
theorem positive_depth_six_old_four_free_gap (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (htn : t<n) (hwin : Win f t (b+4-t)) :
    5≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n) := by
  by_cases hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4
  · have hZero := old_four_counter_high_free_zero f n a b t hw hpre hnb hfloor hpos hS he hcounter htn hwin
    obtain ⟨hnS,hn1S⟩ := old_four_counter_initial_SS f n a b t hw hpre hnb hfloor hpos hS he hcounter htn hwin
    have hn1F : Fw f (n+1)=Fw f n-1 := by
      rcases fw_cases f n with ⟨_,h⟩ | ⟨h,_⟩
      · simp [hnS] at h
      · exact h
    have hActual (x : Nat) (hnx : n≤x) (hxb : x<b) (hxF : Fw f n-4≤Fw f x)
        (hxA : f x=true) : EndN f 0 x := by
      by_cases h : EndN f 0 x
      · exact h
      · exact (not_of_cN_zero
          (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n)
          hZero x hnx (by omega) ⟨hxF,hxA,h⟩).elim
    obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
    have hDown := fw_false_run f b 4 hS
    obtain ⟨q,hnq,hqb,hq,hqA⟩ := ivt f b (Fw f n+3) (by omega) (b-n) n (by omega) (by omega)
    have hqe := hActual q hnq hqb (by omega) hqA
    obtain ⟨u,hnu,huq,huH,hWin,hCases⟩ := old_four_high_source_spectrum f n a b t q 3 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin hnq hqb (by omega) (by omega) hqe
    have h3 : q-u=3 := by
      rcases hCases with h | h
      · exact h.1
      · have := h.2.1
        omega
    have hWin3 : Win f u 3 := by rwa [h3] at hWin
    obtain ⟨hSu,hA1,hA2⟩ := win3 f u hWin3
    have hPrevA : f (q-1)=true := by rwa [show q-1=u+2 by omega]
    have hPrevF : Fw f (q-1)=Fw f n+1 := by
      rcases fw_cases f (q-1) with ⟨h,_⟩ | ⟨_,h⟩
      · rw [show q-1+1=q by omega] at h
        omega
      · simp [hPrevA] at h
    have hPrevE := hActual (q-1) (by omega) (by omega) (by omega) hPrevA
    obtain ⟨v,hnv,hvq,hvH,hInner,hCasesV⟩ := old_four_high_source_spectrum f n a b t (q-1) 2 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin (by omega) (by omega) (by omega) (by omega) hPrevE
    have h7 : q-1-v=7 := by
      rcases hCasesV with h | h
      · have hV3 := h.1
        have hVWin : Win f v 3 := by rwa [hV3] at hInner
        have hVA := (win3 f v hVWin).2.1
        rw [show v+1=u by omega] at hVA
        simp [hSu] at hVA
      · exact h.1
    have hWin7 : Win f v 7 := by rwa [h7] at hInner
    have hnv2 : n+2≤v := by
      by_cases hn0 : v=n
      · have hWord := actual_seven_ending_SA f v hWin7
          (by rwa [show v+5=u by omega]) (by rwa [show v+6=u+1 by omega])
        have hGet := seg_get f v 7 1 (by decide)
        rw [hWord] at hGet
        change some true=some (f (v+1)) at hGet
        rw [hn0,hn1S] at hGet
        cases hGet
      · by_cases hn1 : v=n+1
        · rw [hn1,hn1F] at hvH
          omega
        · omega
    have hCost := old_four_second_clock_source_budget f n a b t v (q-1) 2 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin hnv2 hvq (by omega) (by omega) hvH hInner
    rw [h7] at hCost
    omega
  · omega

end Recaman.OldFourGap
