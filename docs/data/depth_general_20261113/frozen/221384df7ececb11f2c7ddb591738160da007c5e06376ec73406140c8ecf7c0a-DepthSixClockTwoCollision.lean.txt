import Recaman.DepthSixClockTwoHighWindow

namespace Recaman.DepthSixClockTwoCollision

open Recaman.DepthSixClockTwoHighWindow Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The second-clock gap-five counter is impossible: the two highest
required additions internally supply incompatible original SAA windows. -/
theorem clock_two_five_actual_counter_excluded (f : Nat → Bool) (n a b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5)
    (htb : n+2<b) (hwin : Win f (n+2) (b+5-(n+2))) : False := by
  let P := fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i
  have hHigh := positive_depth_six_counter_high_free f n a b 5 hw hpre hnb hfloor hpos hS he hcounter
  simp only [Nat.reduceEqDiff,if_false] at hHigh
  change cN P n (b-n)≤1 at hHigh
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b 5 hw hpre
    hnb hfloor hpos hS he hcounter
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
      obtain ⟨_,_,_,_,_,hZero,_⟩ := clock_two_five_high_source_SAA f n a b z 3 hw hpre
        hnb hfloor hpos hS he hcounter htb hwin hnz (by omega) (by omega) (by omega) hze
      change cN P n (b-n)=0 at hZero
      omega
  obtain ⟨u,hnu,huq,huH,hWin,hZero,_⟩ := clock_two_five_high_source_SAA f n a b q 4 hw hpre
    hnb hfloor hpos hS he hcounter htb hwin hnq hqb (by omega) (by omega) hqe
  change cN P n (b-n)=0 at hZero
  obtain ⟨hSu,_,hA2⟩ := win3 f u hWin
  have hPrevA : f (q-1)=true := by rwa [show q-1=u+2 by omega]
  have hPrevF : Fw f (q-1)=Fw f n+2 := by
    rcases fw_cases f (q-1) with ⟨h,_⟩ | ⟨_,h⟩
    · rw [show q-1+1=q by omega] at h
      omega
    · simp [hPrevA] at h
  have hPrevE : EndN f 0 (q-1) := by
    by_cases h : EndN f 0 (q-1)
    · exact h
    · exact (not_of_cN_zero P n (b-n) hZero (q-1) (by omega) (by omega)
        ⟨by omega,hPrevA,h⟩).elim
  obtain ⟨v,_,hvq,_,hInner,_,_⟩ := clock_two_five_high_source_SAA f n a b (q-1) 3 hw hpre
    hnb hfloor hpos hS he hcounter htb hwin (by omega) (by omega) (by omega) (by omega) hPrevE
  have hA := (win3 f v hInner).2.1
  rw [show v+1=u by omega] at hA
  simp [hSu] at hA

end Recaman.DepthSixClockTwoCollision
