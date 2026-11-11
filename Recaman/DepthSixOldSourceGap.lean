import Recaman.OldFourGap

namespace Recaman.DepthSixOldSourceGap

open Recaman.DepthSixGapResidual Recaman.DepthSixPairResidual Recaman.OldFourGap
open Recaman.OldFiveShortHighWindow Recaman.DepthSixNestedWindow
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Coverage composition only: the new old-source four/five cases and
gap-six theorem close every old actual source under the depth-six floor. -/
theorem positive_depth_six_old_source_free_gap (f : Nat → Bool) (n a b j t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j))
    (htn : t<n) (hwin : Win f t (b+j-t)) :
    j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n) := by
  by_cases hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤j
  · obtain ⟨_,hFour,_,_,_⟩ := positive_depth_six_counter_profile f n a b j hw hpre hnb hfloor hpos hS he hcounter
    have hSix := positive_depth_six_counter_gap_le_six f n a b j hw hpre hnb hfloor hpos hS he hcounter
    rcases (show j=4 ∨ j=5 ∨ j=6 by omega) with rfl | rfl | rfl
    · exact positive_depth_six_old_four_free_gap f n a b t hw hpre hnb hfloor hpos hS he htn hwin
    · exact positive_depth_six_old_five_free_gap f n a b t hw hpre hnb hfloor hpos hS he htn hwin
    · exact positive_depth_six_gap_six_free_gap f n a b hw hpre hnb hfloor hpos hS he
  · omega

end Recaman.DepthSixOldSourceGap
