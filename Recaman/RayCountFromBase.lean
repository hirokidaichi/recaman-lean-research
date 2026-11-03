import Recaman.RunSupplyBudget

namespace Recaman.RayCountFromBase

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
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
  rw [count_translate (EndN f 0) b K,count_translate (EndN f a) b K]
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

private theorem count_length_le (P : Nat → Prop) (b : Nat) : ∀ K, cN P b K≤K
  | 0 => by simp [cN]
  | K+1 => by have h:=count_length_le P b K; have hs:=cN_succ_le P b K; omega

private theorem initial_count_le (d : Nat) : ∀ K, cN (fun i=>i<d) 0 K≤d
  | 0 => by simp [cN]
  | K+1 => by
      by_cases hk : K<d
      · have hl:=count_length_le (fun i=>i<d) 0 K
        have hs:=cN_succ_le (fun i=>i<d) 0 K
        omega
      · rw [cN_succ_neg (fun i=>i<d) 0 K (by simpa using hk)]
        exact initial_count_le d K

/-- A proved source-base comparison outside an initial band costs at most its actual length. -/
theorem count_with_initial_segment (f : Nat → Bool) (a b K d : Nat)
    (hsource : ∀ i, i<K → d≤i → EndN f 0 (b+i) → EndN f a (b+i)) :
    cN (EndN f 0) b K≤d+cN (EndN f a) b K := by
  rw [count_translate (EndN f 0) b K,count_translate (EndN f a) b K]
  let P:=fun i=>i<d
  let Q:=fun i=>EndN f a (b+i)
  have hm : cN (fun i=>EndN f 0 (b+i)) 0 K≤cN (fun i=>P i ∨ Q i) 0 K := by
    apply cN_mono
    intro i _ hi he
    by_cases hd : i<d
    · exact Or.inl hd
    · exact Or.inr (hsource i (by omega) (by omega) he)
  have ho:=Recaman.RunSupplyBudget.cN_or_le P Q K
  have hp : cN P 0 K≤d := initial_count_le d K
  change _≤d+cN Q 0 K
  omega

end Recaman.RayCountFromBase
