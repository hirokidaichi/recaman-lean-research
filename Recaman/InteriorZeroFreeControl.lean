import Recaman.ForwardFreeThreeControl

namespace Recaman.InteriorZeroFreeControl

open Recaman.AdditionRankSlack Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic Recaman.InitialSPaddingPositive Recaman.InitialSeparatorTrim

def history : List Bool :=
  [true,true,false,true,false,false,false,false,false,true,true,true,true]

def interior : List Bool := [false,true,true,true,false,false,false]

def paddedSign : Nat → Bool :=
  trimSSequence (finiteSign (history++interior++[false])) 0 20

private theorem end_at_34 : EndN paddedSign 0 34 :=
  (localSupply_seg_iff paddedSign 0 34 (by decide) (by decide)).mp (by decide)

private theorem end_at_35 : EndN paddedSign 0 35 :=
  (localSupply_seg_iff paddedSign 0 35 (by decide) (by decide)).mp (by decide)

private theorem end_at_36 : EndN paddedSign 0 36 :=
  (localSupply_seg_iff paddedSign 0 36 (by decide) (by decide)).mp (by decide)

/-- Absolute positivity does not pay for a forward clock difference with
the original free additions strictly between two interior source starts. -/
theorem zero_free_forward_control :
    seg paddedSign 33 7=interior ∧
    seg paddedSign 40 1=[false] ∧
    (∀ k, 0<k → k≤44 → cN (EndN paddedSign 0) 0 k+1≤subtractions paddedSign 0 k) ∧
    free paddedSign 33 7=0 ∧
    runKey [false]= -2 ∧ runKey (interior++[false])= -2 ∧
    mass [false]+2=1 ∧ mass (interior++[false])+3=1 ∧
    EndN paddedSign 0 43 ∧ EndN paddedSign 0 44 := by
  have hA : cN (fun i=>paddedSign i=true) 0 44<20 := by
    have h:=ones_seg_eq_count paddedSign 0 44
    rw [show ones (seg paddedSign 0 44)=13 by decide] at h
    omega
  have hp:=initial_S_positive paddedSign 20 44
    (fun i hi=>by simp [paddedSign,trimSSequence,hi]) hA
  have hz : free paddedSign 33 7=0 := by
    unfold free
    apply cN_zero_of
    intro t hnt ht h
    have hc : t=33 ∨ t=34 ∨ t=35 ∨ t=36 ∨ t=37 ∨ t=38 ∨ t=39 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (by decide : paddedSign 33≠true) h.1
    · exact h.2 end_at_34
    · exact h.2 end_at_35
    · exact h.2 end_at_36
    · exact (by decide : paddedSign 37≠true) h.1
    · exact (by decide : paddedSign 38≠true) h.1
    · exact (by decide : paddedSign 39≠true) h.1
  have h43 : EndN paddedSign 0 43 :=
    (localSupply_seg_iff paddedSign 0 43 (by decide) (by decide)).mp (by decide)
  have h44 : EndN paddedSign 0 44 :=
    (localSupply_seg_iff paddedSign 0 44 (by decide) (by decide)).mp (by decide)
  exact ⟨by decide,by decide,hp,hz,by decide,by decide,by decide,by decide,h43,h44⟩

end Recaman.InteriorZeroFreeControl
