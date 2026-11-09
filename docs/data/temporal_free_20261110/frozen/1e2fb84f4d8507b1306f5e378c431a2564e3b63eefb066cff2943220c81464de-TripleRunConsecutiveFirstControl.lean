import Recaman.TripleRunLocalClockCut
import Recaman.InitialSPaddingPositive

namespace Recaman.TripleRunConsecutiveFirstControl

open Recaman.TripleRunClockResidue Recaman.InitialSPaddingPositive
open Recaman.InitialSeparatorTrim Recaman.AdditionRankSlack
open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity Recaman.LeadingRunSupply

private def afterPadding : List Bool :=
  tripleRuns [0,5,2,1,2]++[false]

def controlSign : Nat → Bool :=
  trimSSequence (finiteSign afterPadding) 0 13

/-- The fourth and fifth three-A runs have consecutive local first-A
suppliers. The second source uses more complete blocks than the first. -/
theorem consecutive_first_A_local_control :
    seg controlSign 0 39=tripleRuns [13,5,2,1,2]++[false] ∧
    (∀ k, 0<k → k≤35 → cN (EndN controlSign 0) 0 k+1≤subtractions controlSign 0 k) ∧
    Win controlSign 19 11 ∧ Win controlSign 12 23 ∧
    EndN controlSign 0 30 ∧ EndN controlSign 0 35 := by
  have hA : cN (fun t=>controlSign t=true) 0 35<13 := by
    have h:=ones_seg_eq_count controlSign 0 35
    rw [show ones (seg controlSign 0 35)=12 by decide] at h
    omega
  have hPos:=initial_S_positive controlSign 13 35
    (fun t ht=>by simp [controlSign,trimSSequence,ht]) hA
  have h1 : Win controlSign 19 11 := by unfold Win; decide
  have h2 : Win controlSign 12 23 := by unfold Win; decide
  exact ⟨by decide,hPos,h1,h2,
    ⟨by decide,19,11,by decide,by decide,h1⟩,
    ⟨by decide,12,23,by decide,by decide,h2⟩⟩

end Recaman.TripleRunConsecutiveFirstControl
