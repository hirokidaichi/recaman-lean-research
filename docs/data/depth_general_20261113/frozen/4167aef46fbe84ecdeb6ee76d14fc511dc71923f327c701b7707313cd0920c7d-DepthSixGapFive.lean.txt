import Recaman.DepthSixClockTwoCollision
import Recaman.DepthSixOldSourceGap
import Recaman.DepthSixClockFourCollision
import Recaman.DepthSixLocalSourceClock

namespace Recaman.DepthSixGapFive

open Recaman.DepthSixClockTwoCollision Recaman.DepthSixOldSourceGap
open Recaman.DepthSixClockFourCollision Recaman.DepthSixLocalSourceClock
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Every original positive depth-six target after five subtractions
has six free additions in the same uncut original interval. The final
source is extracted from EndN and all old/local clocks are exhausted. -/
theorem positive_depth_six_gap_five_free_gap (f : Nat → Bool) (n a b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+5 → f i=false) (he : EndN f 0 (b+5)) :
    6≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n) := by
  by_cases hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤5
  · have hSaved := he
    obtain ⟨_,t,k,_,htk,hk,hlev,harea⟩ := he
    rw [htk] at hlev
    have htb : t<b := by
      by_cases h : t<b
      · exact h
      · have hDown := fw_false_run f b 5 hS
        have hToT := fw_false_run f b (t-b) (fun i hi hj => hS i hi (by omega))
        rw [show b+(t-b)=t by omega] at hToT
        omega
    have hWin : Win f t (b+5-t) := by
      rw [show b+5-t=k by omega]
      exact ⟨hk,by rw [htk]; exact hlev,harea⟩
    by_cases htn : t<n
    · exact positive_depth_six_old_source_free_gap f n a b 5 t hw hpre hnb hfloor hpos hS hSaved htn hWin
    · obtain ⟨hClock,_⟩ := local_counter_source_clock_two_or_four f n a b 5 t hw hpre
        hnb hfloor hpos hS hSaved hcounter (Or.inr rfl) (by omega) htb hWin
      rcases hClock with rfl | rfl
      · exact (clock_two_five_actual_counter_excluded f n a b hw hpre hnb hfloor hpos hS hSaved hcounter htb hWin).elim
      · exact (clock_four_actual_counter_excluded f n a b 5 hw hpre hnb hfloor hpos hS hSaved hcounter
          (Or.inr rfl) htb hWin).elim
  · omega

end Recaman.DepthSixGapFive
