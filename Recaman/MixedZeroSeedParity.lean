import Recaman.UnitTargetPrefixParity
import Recaman.OldThreeKeyParity

namespace Recaman.MixedZeroSeedParity

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ASourceReuse Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The seed-key residue only needs a zero-mass mixed head. No run
number, head shape, area band or old-mass cutoff is required. -/
theorem zero_head_seed_parity (u z : List Bool) (v : Nat) (hmz : mass z=0)
    (hseed : runKey (u++z++List.replicate v false)= -2) :
    ∃ Z : Int, runKey u=2*((cntF z : Int)+(v : Int))-2+4*Z := by
  obtain ⟨Q,hQ⟩:=Recaman.UnitTargetPrefixParity.cross_four z
  obtain ⟨a,ha⟩:=Recaman.OldThreeKeyParity.square_even_delta (cntF z : Int)
  obtain ⟨b,hb⟩:=Recaman.OldThreeKeyParity.square_even_delta (v : Int)
  rw [runKey_append_S,runKey_append,mass_append,hmz] at hseed
  refine ⟨a+b-Q-mass u*((cntF z : Int)+(v : Int)),?_⟩
  grind only

private theorem mass_three_circle (E R k Z : Int)
    (hk : k= -2 ∨ k=0 ∨ k=2) (hZ : k=2*E-2+4*Z)
    (hdiff : -k=8*E+2-2*R^2) : R%2=0 ∧ R^2=4*E ∧ k= -2 ∧ E%2=0 := by
  have heven : R%2=0 := by
    by_cases he : R%2=0
    · exact he
    have ho : R%2=1 := by omega
    obtain ⟨q,hq⟩:=Recaman.OldThreeKeyParity.odd_square_eight R ho
    rw [hq] at hdiff
    rcases hk with hm|hz|hp <;> omega
  let q:=R/2
  have hRq : R=2*q := by dsimp [q]; omega
  have hsquare : R^2=4*q^2 := by rw [hRq]; grind only
  have hminus : k= -2 := by
    rcases hk with hm|hz|hp
    · exact hm
    · rw [hsquare] at hdiff; omega
    · rw [hsquare] at hdiff; omega
  have hcircle : R^2=4*E := by omega
  have hEeven : E%2=0 := by omega
  exact ⟨heven,hcircle,hminus,hEeven⟩

/-- An arbitrary zero-mass mixed head retains the mass3/mass1 coupled
circle and seed key. Primitive suffix spectrum is used literally. -/
theorem mixed_old_three_circle (u z : List Bool) (hu : BlockWord u)
    (hD : mass u=3) (hmz : mass z=0) (v R : Nat)
    (hseed : runKey (u++z++List.replicate v false)= -2)
    (htarget : runKey ([true]++z++List.replicate v false)= -2*(R : Int)^2) :
    (R : Int)%2=0 ∧ (R : Int)^2=4*((cntF z : Int)+(v : Int)) ∧ runKey u= -2 ∧
      ((cntF z : Int)+(v : Int))%2=0 := by
  obtain ⟨Z,hZ⟩:=zero_head_seed_parity u z v hmz hseed
  have hmu : mass [true]=1 := by decide
  have hku : runKey [true]=0 := by decide
  have hs:=hseed
  have ht:=htarget
  rw [runKey_append_S,runKey_append,mass_append,hD,hmz] at hs
  rw [runKey_append_S,runKey_append,mass_append,hmu,hku,hmz] at ht
  have hdiff : -runKey u=8*((cntF z : Int)+(v : Int))+2-2*(R : Int)^2 := by grind only
  exact mass_three_circle _ _ _ Z (Recaman.MassTwoThreeKeys.mass_three_keys u hu hD) hZ hdiff

end Recaman.MixedZeroSeedParity
