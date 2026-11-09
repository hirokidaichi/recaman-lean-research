import Recaman.RankTwoBoundaryRay
import Recaman.InitialSPaddingPositive

namespace Recaman.SameClockBoundaryControl

open Recaman.AdditionRankSlack Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.LineCapacityPeriodic Recaman.InitialSPaddingPositive Recaman.BlockSuffixPositivity

def witnessSign : Nat → Bool := finiteSign [false,true,true,false,false]

/-- A single actual supplied endpoint has distinct starts at 0 and 4.
The four signs between them use exactly two original free additions. -/
theorem same_clock_two_sources_actual :
    seg witnessSign 0 4=[false,true,true,false] ∧
    (∀ k, 0<k → k≤4 → cN (EndN witnessSign 0) 0 k+1≤subtractions witnessSign 0 k) ∧
    free witnessSign 0 4=2 ∧
    Win witnessSign 0 7 ∧ Win witnessSign 4 3 ∧ EndN witnessSign 0 7 := by
  have hNone (t : Nat) (ht : t<4) : ¬EndN witnessSign 0 t := by
    have h : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · intro he; exact (by decide : witnessSign 0≠true) he.1
    · intro he
      have hh:=(localSupply_seg_iff witnessSign 0 1 (by decide) (by decide)).mpr he
      exact (by decide : Recaman.ThreeNonsuppliedData.localSupply (seg witnessSign 0 1)≠true) hh
    · intro he
      have hh:=(localSupply_seg_iff witnessSign 0 2 (by decide) (by decide)).mpr he
      exact (by decide : Recaman.ThreeNonsuppliedData.localSupply (seg witnessSign 0 2)≠true) hh
    · intro he; exact (by decide : witnessSign 3≠true) he.1
  have hCount (k : Nat) (hk : k≤4) : cN (EndN witnessSign 0) 0 k=0 := by
    apply cN_zero_of
    intro t _ ht
    exact hNone t (by omega)
  have hS1 : subtractions witnessSign 0 1=1 :=
    cN_succ_pos _ 0 0 (by decide)
  have hPos (k : Nat) (hk : 0<k) (hk4 : k≤4) :
      cN (EndN witnessSign 0) 0 k+1≤subtractions witnessSign 0 k := by
    have hle : subtractions witnessSign 0 1≤subtractions witnessSign 0 k :=
      count_prefix_le (fun t=>witnessSign t=false) 0 1 k (by omega)
    rw [hCount k hk4]
    omega
  have hA : additions witnessSign 0 4=2 := by
    have ha:=Recaman.BlockSuffixPositivity.ones_seg_eq_count witnessSign 0 4
    rw [show Recaman.LeadingRunSupply.ones (seg witnessSign 0 4)=2 by decide] at ha
    change 2=(additions witnessSign 0 4 : Int) at ha
    omega
  have hSplit:=additions_split witnessSign 0 4
  have he:=hCount 4 (by decide)
  have hW0 : Win witnessSign 0 7 := by unfold Win; decide
  have hW4 : Win witnessSign 4 3 := by unfold Win; decide
  exact ⟨by decide,hPos,by omega,hW0,hW4,
    ⟨by decide,0,7,by decide,by decide,hW0⟩⟩

end Recaman.SameClockBoundaryControl
