import Recaman.HeadRunCountBounds
namespace Recaman.SecondRaySmallShapes
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.HeadRunSupplyBudgets Recaman.HeadRunCountBounds

private theorem square_holes (x : Int) (hx : 0≤x)
    (he : x^2=3 ∨ x^2=7 ∨ x^2=11 ∨ x^2=13 ∨ x^2=15 ∨ x^2=19) : False := by
  by_cases h1 : x≤1
  · have hs:=Recaman.ShortCounterFactorBounds.square_lower 1 x hx h1; omega
  by_cases h2 : x≤2
  · have hl:=Recaman.ShortCounterFactorBounds.square_lower x 2 (by omega) (by omega)
    have hu:=Recaman.ShortCounterFactorBounds.square_lower 2 x hx h2
    omega
  by_cases h3 : x≤3
  · have hl:=Recaman.ShortCounterFactorBounds.square_lower x 3 (by omega) (by omega)
    have hu:=Recaman.ShortCounterFactorBounds.square_lower 3 x hx h3
    omega
  by_cases h4 : x≤4
  · have hl:=Recaman.ShortCounterFactorBounds.square_lower x 4 (by omega) (by omega)
    have hu:=Recaman.ShortCounterFactorBounds.square_lower 4 x hx h4
    omega
  have hl:=Recaman.ShortCounterFactorBounds.square_lower x 5 (by omega) (by omega)
  omega

/-- Explicit small shapes have no earlier local source; only the separator clock2 remains. -/
theorem small_second_local (h M m K : Nat)
    (hshape : (M=1 ∧ m=1) ∨ (M=3 ∧ 1≤m ∧ m≤3) ∨ (5≤M ∧ M≤7 ∧ m=1)) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false) K≤1 := by
  unfold rayCount
  apply cN_le_one_of_unique
  have only2 (i : Nat) (hi : Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate h false++List.replicate M true++List.replicate m false)++List.replicate i true)=true) : i=2 := by
    have he:=localSupply_two_run_iff h M m i 0
    simp only [List.replicate_zero,List.append_nil,Nat.zero_add,Int.natCast_zero,Int.zero_add,Int.one_pow] at he
    rcases he.mp hi with ⟨q,hq,hqh,hmass,hk⟩|⟨a,ha,haM,hmass,hk⟩|hlast
    · have hsq : ((q : Int)+(m : Int))^2=1+2*(m : Int)*(M : Int) := by omega
      apply False.elim
      apply square_holes ((q : Int)+(m : Int)) (by omega)
      rcases hshape with ⟨rfl,rfl⟩|⟨rfl,hm1,hm3⟩|⟨hM5,hM7,rfl⟩
      · omega
      · rcases (show m=1 ∨ m=2 ∨ m=3 by omega) with hm | hm | hm <;> rw [hm] at hsq <;> omega
      · rcases (show M=5 ∨ M=6 ∨ M=7 by omega) with hM | hM | hM <;> rw [hM] at hsq <;> omega
    · have heq : (1 : Int)=(m : Int)*((m : Int)-2*(a : Int)) := by simpa using hk
      rcases hshape with ⟨rfl,rfl⟩|⟨rfl,hm1,hm3⟩|⟨hM5,hM7,rfl⟩
      · omega
      · rcases (show m=1 ∨ m=2 ∨ m=3 by omega) with hm | hm | hm <;> rw [hm] at heq <;> omega
      · omega
    · omega
  intro i hi j hj hsi hsj
  have h1:=only2 i hsi
  have h2:=only2 j hsj
  omega
end Recaman.SecondRaySmallShapes
