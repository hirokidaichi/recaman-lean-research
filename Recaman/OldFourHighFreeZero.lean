import Recaman.OldFourSecondClockBudget

namespace Recaman.OldFourHighFreeZero

open Recaman.OldFourInitialSS Recaman.OldFourSecondClockBudget Recaman.OldFourHighWindowSpectrum
open Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The strengthened source budget excludes the one-high-free branch
of every original old-source gap-four counter. -/
theorem old_four_counter_high_free_zero (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+4 → f i=false) (he : EndN f 0 (b+4))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤4)
    (htn : t<n) (hwin : Win f t (b+4-t)) :
    cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n)=0 := by
  let Q := fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i
  by_cases h0 : cN Q n (b-n)=0
  · exact h0
  · have hOne : 1≤cN Q n (b-n) := by omega
    have hH := positive_depth_six_counter_high_free f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
    simp only [Nat.reduceEqDiff,if_false] at hH
    change cN Q n (b-n)≤1 at hH
    obtain ⟨hnS,hn1S⟩ := old_four_counter_initial_SS f n a b t hw hpre hnb hfloor hpos hS he hcounter htn hwin
    have hn1F : Fw f (n+1)=Fw f n-1 := by
      rcases fw_cases f n with ⟨_,h⟩ | ⟨h,_⟩
      · simp [hnS] at h
      · exact h
    obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 4 hw hpre hnb hfloor hpos hS he hcounter
    have hDown := fw_false_run f b 4 hS
    obtain ⟨q,hnq,hqb,hq,hqA⟩ := ivt f b (Fw f n+3) (by omega) (b-n) n (by omega) (by omega)
    have hqNo : ¬EndN f 0 q := by
      intro hqe
      obtain ⟨u,_,_,_,hWin,hCost⟩ := old_four_eight_high_source_budget f n a b t q 3 hw hpre
        hnb hfloor hpos hS he hcounter htn hwin hnq hqb (by omega) (by omega) hqe
      have hk := win_ge3 f u (q-u) hWin
      change 3*(_-1)+8*(cN Q n (b-n) : Int)≤13 at hCost
      omega
    obtain ⟨z,hnz,hzq,hz,hzA⟩ := ivt f q (Fw f n+2) (by omega) (q-n) n (by omega) (by omega)
    have hze : EndN f 0 z := by
      by_cases h : EndN f 0 z
      · exact h
      · have hTwo := two_marks_le_count Q n z q (b-n) hnz hzq (by omega)
          ⟨by omega,hzA,h⟩ ⟨by omega,hqA,hqNo⟩
        omega
    obtain ⟨u,hnu,huz,huH,hWin,hCases⟩ := old_four_high_source_spectrum f n a b t z 2 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin hnz (by omega) (by omega) (by omega) hze
    have h3 : z-u=3 := by
      rcases hCases with h | h
      · exact h.1
      · have hz := h.2.2
        change cN Q n (b-n)=0 at hz
        omega
    have hWin3 : Win f u 3 := by rwa [h3] at hWin
    have hnu2 : n+2≤u := by
      by_cases hn0 : u=n
      · have ha := (win3 f u hWin3).2.1
        rw [hn0,hn1S] at ha
        cases ha
      · by_cases hn1 : u=n+1
        · rw [hn1,hn1F] at huH
          omega
        · omega
    have hCost := old_four_second_clock_source_budget f n a b t u z 2 hw hpre
      hnb hfloor hpos hS he hcounter htn hwin hnu2 huz (by omega) (by omega) huH hWin
    change 2*(_-1)+8*(cN Q n (b-n) : Int)≤9 at hCost
    rw [h3] at hCost
    omega

end Recaman.OldFourHighFreeZero
