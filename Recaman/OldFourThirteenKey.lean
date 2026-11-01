import Recaman.OldSeedInversionKey

namespace Recaman.OldFourThirteenKey

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem block_four_key_bounds (u : List Bool) (hu : BlockWord u) (hm : mass u=4) :
    -2≤runKey u ∧ runKey u≤6 := by
  have ht : (massFourWords.all fun x=>decide (-2≤runKey x ∧ runKey x≤6))=true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp ht u (block_mass_four hu hm))

/-- The real old prefix supplies both sides of the inversion band. The
mass-four extreme areas coexist and neither is silently discarded. -/
theorem same_old_four_thirteen (u z : List Bool) (hu : BlockWord u)
    (hm : mass u=4) (hmz : mass z=0) (hS : cntF z=13) (v i : Nat) (hi : i≤2) (I : Int)
    (hmeasure : runKey z=4*I-2*(cntF z : Int)^2)
    (hmass : mass u-(v : Int)+(i : Int)=1)
    (hkey : runKey (u++z++List.replicate v false)= -2) : 23≤I ∧ I≤25 := by
  have hb:=block_four_key_bounds u hu hm
  have hv : (v : Int)=(i : Int)+3 := by omega
  rw [runKey_append_S,runKey_append,mass_append,hmz,hm,hmeasure,hS] at hkey
  have heq : 4*I+runKey u=96+2*((i : Int)-1)^2 := by
    rw [hv] at hkey
    grind only
  have hiv : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hiv with rfl|rfl|rfl <;> omega

end Recaman.OldFourThirteenKey
