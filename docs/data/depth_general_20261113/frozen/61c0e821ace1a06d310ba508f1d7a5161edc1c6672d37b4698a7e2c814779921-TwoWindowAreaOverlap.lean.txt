import Recaman.HighWindowSquareBudget
import Recaman.InitialSPaddingPositive

namespace Recaman.TwoWindowAreaOverlap

open Recaman.LevelTriangleArea Recaman.HighWindowSquareBudget
open Recaman.InitialSPaddingPositive Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The corrected signed-area resource on the original interval. -/
def areaSurplus (f : Nat → Bool) (s : Nat) (r : Int) (K : Nat) : Int :=
  2*areaFromLevel f s r K+belowTriangle r (Fw f (s+K))-
    belowTriangle r (Fw f s)+2*lowAdditionWeights f s r K-
    aboveTriangle r (Fw f (s+K))+aboveTriangle r (Fw f s)

/-- The cost forced by a source window above the chosen baseline. -/
def windowCharge (f : Nat → Bool) (r : Int) (t q : Nat) : Int :=
  2*(Fw f t-r)*(((q-t : Nat) : Int)-1)-2

private def word : List Bool :=
  [false,false,true,true,true,true,false,true]

private def f : Nat → Bool := finiteSign word

private theorem outer : Win f 0 7 := by unfold Win; decide
private theorem inner : Win f 1 3 := by unfold Win; decide

private theorem supplied (t : Nat) (ht : t<7) : EndN f 0 t ↔ t=4 := by
  have hh : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨fun h => (by decide : f 0≠true) h.1 |>.elim,by simp⟩
  · exact ⟨fun h => (by decide : f 1≠true) h.1 |>.elim,by simp⟩
  · refine ⟨fun h => ?_,by simp⟩
    have hl := (localSupply_seg_iff f 0 2 (by decide) (by decide)).mpr h
    have hn : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 (2-0))=false := by decide
    rw [hn] at hl
    cases hl
  · refine ⟨fun h => ?_,by simp⟩
    have hl := (localSupply_seg_iff f 0 3 (by decide) (by decide)).mpr h
    have hn : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 (3-0))=false := by decide
    rw [hn] at hl
    cases hl
  · exact ⟨fun _ => rfl,fun _ => ⟨by decide,1,3,by omega,by omega,inner⟩⟩
  · refine ⟨fun h => ?_,by simp⟩
    have hl := (localSupply_seg_iff f 0 5 (by decide) (by decide)).mpr h
    have hn : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 (5-0))=false := by decide
    rw [hn] at hl
    cases hl
  · exact ⟨fun h => (by decide : f 6≠true) h.1 |>.elim,by simp⟩

/-- Different actual targets may spend the same area resource twice:
SSAAAAS has a length-seven window and an internal SAA window. Even
with the original empty block prefix and strict positive deficit,
their costs are 22 and 2 while the original resource is only 22. -/
theorem two_actual_windows_exceed_one_resource :
    BlockWord (seg f 0 0) ∧
    (∀ i, i≤7 → -2≤Fw f i) ∧
    (∀ k, 0<k → k≤7 → cN (EndN f 0) 0 k+1≤cN (fun i => f i=false) 0 k) ∧
    EndN f 0 7 ∧ EndN f 0 4 ∧ Win f 0 7 ∧ Win f 1 3 ∧
    windowCharge f (-2) 0 7=22 ∧ windowCharge f (-2) 1 4=2 ∧
    areaSurplus f 0 (-2) 7=22 ∧
    areaSurplus f 0 (-2) 7<windowCharge f (-2) 0 7+windowCharge f (-2) 1 4 := by
  have hE : cN (EndN f 0) 0 7=1 := by
    rw [cN_congr (EndN f 0) (fun t => t=4) 0 7 (fun i _ hi => supplied i (by omega))]
    simp [cN]
  refine ⟨BlockWord.nil,?_,?_,⟨by decide,0,7,by omega,by omega,outer⟩,
    ⟨by decide,1,3,by omega,by omega,inner⟩,outer,inner,
    by decide,by decide,by decide,by decide⟩
  · intro i hi
    have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro k hk hk7
    by_cases h2 : 2≤k
    · have he := count_prefix_le (EndN f 0) 0 k 7 hk7
      have hs := count_prefix_le (fun i => f i=false) 0 2 k h2
      have hs2 : cN (fun i => f i=false) 0 2=2 := by simp [cN,f,finiteSign,word]
      omega
    · have he : k=1 := by omega
      rw [he]
      have hz : cN (EndN f 0) 0 1=0 := by
        apply cN_zero_of
        intro i hi hj hh
        have h4 := (supplied i (by omega)).mp hh
        omega
      have hs : cN (fun i => f i=false) 0 1=1 := by simp [cN,f,finiteSign,word]
      omega

end Recaman.TwoWindowAreaOverlap
