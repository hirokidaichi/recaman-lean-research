import Recaman.DepthSixLocalPrefixPair
import Recaman.DepthSixLocalSourcePrefix
import Recaman.FirstSOneFreePrefix

namespace Recaman.DepthSixLocalSourceClock

open Recaman.DepthSixLocalPrefixPair Recaman.DepthSixLocalSourcePrefix Recaman.FirstSOneFreePrefix
open Recaman.DepthSixGapResidual Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- Both remaining gap sizes have the same two possible original source
clocks after their independently supplied one-free prefix bounds. -/
theorem local_counter_source_clock_two_or_four (f : Nat → Bool) (n a b j t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤j)
    (hj : j=4 ∨ j=5) (hnt : n≤t) (htb : t<b) (hwin : Win f t (b+j-t)) :
    (t=n+2 ∨ t=n+4) ∧ cN (fun i => f i=true) n (t-n)≤1 := by
  have hOne : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (t-n)≤1 := by
    rcases hj with rfl | rfl
    · exact local_four_source_prefix_free_one f n a b t hw hpre hnb hfloor hpos hS he hcounter hnt htb hwin
    · exact local_five_source_prefix_free f n a b t hw hpre hnb hfloor hpos hS he hcounter hnt htb hwin
  have hnS : f n=false := by
    cases h : f n
    · rfl
    · have hp := hpos 1 (by decide) (by omega)
      have hz : cN (fun i => f i=false) n 1=0 := by
        rw [cN_succ_neg _ n 0 (by rw [Nat.add_zero,h]; decide)]
        rfl
      rw [hz] at hp
      omega
  have hA := (first_S_one_free_additions f n a (t-n) hw hpre hnS hOne).2
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b j hw hpre hnb hfloor hpos hS he hcounter
  have hLevel := hwin.2.1
  rw [show t+(b+j-t)=b+j by omega] at hLevel
  have hWalk := cN_walk f n (t-n)
  rw [show n+(t-n)=t by omega] at hWalk
  exact ⟨by omega,hA⟩

end Recaman.DepthSixLocalSourceClock
