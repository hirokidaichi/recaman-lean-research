import Recaman.DepthSixLocalSourceClock
import Recaman.FirstSFourPrefix

namespace Recaman.DepthSixClockFourPrefix

open Recaman.FirstSFourPrefix Recaman.FirstSOneFreePrefix Recaman.DepthSixLocalPrefixPair
open Recaman.DepthSixLocalSourcePrefix Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation
open Recaman.HighWindowSquareBudget Recaman.LevelTriangleArea
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- An actual source at original clock four fixes the short prefix,
spends the unique high free there, and bounds the same-target full area.
All later high A clocks are therefore original actual suppliers. -/
theorem clock_four_actual_prefix_packet (f : Nat → Bool) (n a b j : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤j)
    (hj : j=4 ∨ j=5) (htb : n+4<b) (hwin : Win f (n+4) (b+j-(n+4))) :
    (seg f n 4=[false,true,false,false] ∨ seg f n 4=[false,false,true,false] ∨
      seg f n 4=[false,false,false,true]) ∧
    areaFromLevel f n (Fw f n-2) (b+j-n)≤4 ∧
    cN (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i) n (b-n)=1 ∧
    (∀ q, n+4≤q → q<b → Fw f n-4≤Fw f q → f q=true → EndN f 0 q) := by
  have hnS : f n=false := by
    cases h : f n
    · rfl
    · have hp := hpos 1 (by decide) (by omega)
      have hz : cN (fun i => f i=false) n 1=0 := by
        rw [cN_succ_neg _ n 0 (by rw [Nat.add_zero,h]; decide)]
        rfl
      rw [hz] at hp
      omega
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b j hw hpre hnb hfloor hpos hS he hcounter
  have hLevel := hwin.2.1
  rw [show n+4+(b+j-(n+4))=b+j by omega] at hLevel
  have hEnd : Fw f (n+4)=Fw f n-2 := by omega
  have hOne : cN (fun i => f i=true ∧ ¬EndN f 0 i) n 4≤1 := by
    rcases hj with rfl | rfl
    · have hh := local_four_source_prefix_free_one f n a b (n+4) hw hpre hnb hfloor hpos hS he hcounter (by omega) htb hwin
      simpa only [Nat.add_sub_cancel_left] using hh
    · have hh := local_five_source_prefix_free f n a b (n+4) hw hpre hnb hfloor hpos hS he hcounter (by omega) htb hwin
      simpa only [Nat.add_sub_cancel_left] using hh
  have hAF := (first_S_one_free_additions f n a 4 hw hpre hnS hOne).1
  have hCount := cN_walk f n 4
  have hFree1 : cN (fun i => f i=true ∧ ¬EndN f 0 i) n 4=1 := by rw [hEnd] at hCount; omega
  let Q := fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i
  have hQ4 : cN Q n 4=1 := by
    have hc : cN Q n 4=cN (fun i => f i=true ∧ ¬EndN f 0 i) n 4 := by
      apply cN_congr
      intro i hni hin
      constructor
      · intro h; exact h.2
      · intro h
        refine ⟨?_,h⟩
        have hi := cN_walk f n (i-n)
        rw [show n+(i-n)=i by omega] at hi
        omega
    omega
  have hH := positive_depth_six_counter_high_free f n a b j hw hpre hnb hfloor hpos hS he hcounter
  rw [if_neg (by omega)] at hH
  change cN Q n (b-n)≤1 at hH
  have hQmono := count_prefix_le Q n 4 (b-n) (by omega)
  have hQFull : cN Q n (b-n)=1 := by omega
  have hSplit := cN_add Q n 4 (b-(n+4))
  rw [show 4+(b-(n+4))=b-n by omega,hQ4,hQFull] at hSplit
  have hQFuture : cN Q (n+4) (b-(n+4))=0 := by omega
  have hArea := first_S_four_area_le_four f n hnS hEnd
  have ha := area_from_level_split f n (n+4) (b+j) (Fw f n-2) (by omega) (by omega)
  rw [show n+4-n=4 by omega] at ha
  have hTailArea : areaFromLevel f (n+4) (Fw f n-2) (b+j-(n+4))=0 := by
    unfold areaFromLevel
    rw [hwin.2.2,hEnd,Int.sub_self,Int.mul_zero,Int.add_zero]
  rw [hTailArea] at ha
  refine ⟨first_S_four_words f n hnS hEnd,by omega,hQFull,?_⟩
  intro q hnq hqb hq hqA
  by_cases h : EndN f 0 q
  · exact h
  · exact (not_of_cN_zero Q (n+4) (b-(n+4)) hQFuture q hnq (by omega) ⟨hq,hqA,h⟩).elim

end Recaman.DepthSixClockFourPrefix
