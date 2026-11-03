import Recaman.RunSupplyBudget

namespace Recaman.RayCountFromBase

open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction

private theorem count_translate (P : Nat → Prop) (b : Nat) : ∀ K,
    cN P b K=cN (fun i=>P (b+i)) 0 K
  | 0 => rfl
  | K+1 => by
      classical
      have ih:=count_translate P b K
      by_cases hp : P (b+K) <;> simp [cN,ih,hp]

/-- The exact A-ray count at any fixed original base; no earlier history is erased. -/
theorem count_from_base (f : Nat → Bool) (a b K : Nat) (w : List Bool) (hab : a≤b)
    (hw : seg f a (b-a)=w) (hA : ∀ i, i<K → f (b+i)=true) :
    cN (EndN f a) b K=rayCount w K := by
  rw [count_translate]
  unfold rayCount
  apply cN_congr
  intro i _ hi
  have hword : seg f a (b+i-a)=w++List.replicate i true := by
    have hAi : seg f b i=List.replicate i true := by
      apply seg_A
      intro x hx hxB
      have hh:=hA (x-b) (by omega)
      rw [Nat.add_sub_cancel' hx] at hh
      exact hh
    rw [show b+i-a=(b-a)+i by omega,seg_add,show a+(b-a)=b by omega,hw,hAi]
  have he:=localSupply_seg_iff f a (b+i) (by omega) (hA i (by omega))
  rw [hword] at he
  exact he.symm

/-- Allow one exceptional first clock; all positive clocks use the proved suffix base. -/
theorem count_with_first_clock (f : Nat → Bool) (a b K : Nat)
    (hsource : ∀ i, i<K → 1≤i → EndN f 0 (b+i) → EndN f a (b+i)) :
    cN (EndN f 0) b K≤1+cN (EndN f a) b K := by
  rw [count_translate,count_translate]
  let P:=fun i=>i=0
  let Q:=fun i=>EndN f a (b+i)
  have hm : cN (fun i=>EndN f 0 (b+i)) 0 K≤cN (fun i=>P i ∨ Q i) 0 K := by
    apply cN_mono
    intro i _ hi he
    by_cases hi0 : i=0
    · exact Or.inl hi0
    · exact Or.inr (hsource i (by omega) (by omega) he)
  have ho:=Recaman.RunSupplyBudget.cN_or_le P Q K
  have hp : cN P 0 K≤1 := by
    apply Recaman.RunSupplyBudget.cN_le_one_of_unique
    intros
    dsimp [P] at *
    omega
  change _≤1+cN Q 0 K
  omega

end Recaman.RayCountFromBase
