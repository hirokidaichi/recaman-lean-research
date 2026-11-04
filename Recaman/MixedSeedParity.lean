import Recaman.MixedZeroSeedParity

namespace Recaman.MixedSeedParity

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ASourceReuse Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The literal seed residue retains the head mass term; no zero-mass
head, run count, area band or source-mass bound is assumed. -/
theorem mixed_seed_parity (u z : List Bool) (v : Nat)
    (hseed : runKey (u++z++List.replicate v false)= -2) :
    ∃ Z : Int, runKey u=2*((cntF z : Int)+(v : Int))-2+4*Z := by
  obtain ⟨Q,hQ⟩:=Recaman.UnitTargetPrefixParity.cross_four z
  obtain ⟨a,ha⟩:=Recaman.OldThreeKeyParity.square_even_delta (cntF z : Int)
  obtain ⟨b,hb⟩:=Recaman.OldThreeKeyParity.square_even_delta (v : Int)
  rw [runKey_append_S,runKey_append,mass_append] at hseed
  refine ⟨a+b-Q-mass u*((cntF z : Int)+(v : Int))-(v : Int)*mass z,?_⟩
  grind only

/-- A mass-two primitive seed and the same mass-one old target force
the even square circle for an arbitrary mixed head. -/
theorem mixed_old_two_circle (u z : List Bool) (hu : BlockWord u)
    (hD : mass u=2) (v R : Nat)
    (hseed : runKey (u++z++List.replicate v false)= -2)
    (htarget : runKey ([true]++z++List.replicate v false)= -2*(R : Int)^2) :
    (R : Int)%2=0 ∧ (R : Int)^2=2*((cntF z : Int)+(v : Int)) ∧ runKey u= -2 := by
  obtain ⟨Z,hZ⟩:=mixed_seed_parity u z v hseed
  have hmu : mass [true]=1 := by decide
  have hku : runKey [true]=0 := by decide
  have hs:=hseed
  have ht:=htarget
  rw [runKey_append_S,runKey_append,mass_append,hD] at hs
  rw [runKey_append_S,runKey_append,mass_append,hmu,hku] at ht
  have hd : -runKey u=4*((cntF z : Int)+(v : Int))+2-2*(R : Int)^2 := by grind only
  have hk:=Recaman.MassTwoThreeKeys.mass_two_keys u hu hD
  have he : (R : Int)%2=0 := by
    by_cases he : (R : Int)%2=0
    · exact he
    have ho : (R : Int)%2=1 := by omega
    obtain ⟨q,hq⟩:=Recaman.OldThreeKeyParity.odd_square_eight (R : Int) ho
    rw [hq] at hd
    rcases hk with hm|hz <;> omega
  have hm : runKey u= -2 := by
    let q:=(R : Int)/2
    have hr : (R : Int)=2*q := by dsimp [q]; omega
    have hr2 : (R : Int)^2=4*q^2 := by rw [hr]; grind only
    rcases hk with hm|hz
    · exact hm
    · rw [hr2] at hd; omega
  exact ⟨he,by omega,hm⟩

end Recaman.MixedSeedParity
