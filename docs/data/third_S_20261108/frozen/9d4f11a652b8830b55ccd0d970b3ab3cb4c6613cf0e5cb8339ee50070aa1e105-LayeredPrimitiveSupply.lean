import Recaman.MixedThreeFamilyBudget

namespace Recaman.LayeredPrimitiveSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

def layered : Nat → List Bool
  | 0 => [false,true,true,false,false]
  | k+1 => List.replicate (4*3^k) true++(List.replicate (6*3^k) false++layered k)

private theorem three_power_positive (k : Nat) : 1≤3^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

theorem layered_profile (k : Nat) :
    cntF (layered k)=3*3^k ∧ mass (layered k)= -((3^k : Nat) : Int) ∧
      runKey (layered k)= -2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨hc,hm,hk⟩:=ih
    refine ⟨?_,?_,?_⟩
    · simp only [layered,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,
        Nat.pow_succ]
      rw [hc]
      omega
    · simp only [layered,mass_append,mass_replicate_A,mass_rep_false,hm,Nat.pow_succ,Int.natCast_mul]
      grind only
    · rw [layered,runKey_prepend_A,runKey_prepend_S,hk]
      simp only [cntF_append,cntF_replicate_S,hc,Int.natCast_add,Int.natCast_mul]
      grind only

theorem layered_length (k : Nat) : (layered k).length=5*3^k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [layered,List.length_append,List.length_replicate,ih,Nat.pow_succ]; omega

theorem nested_suffix (N i : Nat) (hi : i≤N) : ∃ u, layered N=u++layered i := by
  induction N with
  | zero =>
    have hi0 : i=0 := by omega
    subst i
    exact ⟨[],rfl⟩
  | succ N ih =>
    by_cases he : i=N+1
    · subst i
      exact ⟨[],rfl⟩
    · obtain ⟨u,hu⟩:=ih (by omega)
      refine ⟨List.replicate (4*3^N) true++List.replicate (6*3^N) false++u,?_⟩
      simp only [layered,hu,List.append_assoc]

/-- Each earlier layer supplies a distinct candidate clock inside the
same unchanged full literal word. No BlockWord realization is assumed. -/
theorem layer_supplies_clock (N i : Nat) (hi : i≤N) :
    Recaman.ThreeNonsuppliedData.localSupply (layered N++List.replicate (3^i+1) true)=true := by
  obtain ⟨u,hu⟩:=nested_suffix N i hi
  have hlen : 0<(layered i).length := by
    rw [layered_length]
    have hp:=three_power_positive i
    omega
  have hlt : u.length<(layered N).length := by rw [hu,List.length_append]; omega
  have hd : (layered N).drop u.length=layered i := by
    rw [hu,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]
  obtain ⟨_,hm,hkey⟩:=layered_profile i
  have he:= (localSupply_A_S_iff (layered N) (3^i+1) 0).mpr
    ⟨u.length,hlt,by rw [hd,hm]; simp only [Int.natCast_add,Int.natCast_one]; omega,
      by rw [hd,hkey]; decide⟩
  simpa only [List.replicate_zero,List.append_nil] using he

private theorem increasing_count_lower (P : Nat → Prop) (f : Nat → Nat)
    (hstep : ∀ k, f k<f (k+1)) : ∀ N,
      (∀ i, i≤N → P (f i)) → N+1≤cN P 0 (f N+1) := by
  intro N
  induction N with
  | zero =>
    intro hP
    have he:=cN_succ_pos P 0 (f 0) (by simpa only [Nat.zero_add] using hP 0 (by omega))
    omega
  | succ N ih =>
    intro hP
    have hp:=ih (fun i hi=>hP i (by omega))
    have hs:=hstep N
    have hc:=cN_add P 0 (f N+1) (f (N+1)-(f N+1))
    rw [show (f N+1)+(f (N+1)-(f N+1))=f (N+1) by omega] at hc
    have hn:=cN_succ_pos P 0 (f (N+1)) (by simpa only [Nat.zero_add] using hP (N+1) (by omega))
    omega

/-- There is no fixed upper bound on final-ray supply for arbitrary
mixed literal histories. This family is not a C1 counterexample. -/
theorem layered_ray_count_unbounded (N : Nat) :
    N+1≤rayCount (layered N) (3^N+2) := by
  let P:=fun i=>Recaman.ThreeNonsuppliedData.localSupply (layered N++List.replicate i true)=true
  have hstep : ∀ k, 3^k+1<3^(k+1)+1 := by
    intro k
    have hp:=three_power_positive k
    rw [Nat.pow_succ]
    omega
  have he:=increasing_count_lower P (fun i=>3^i+1) hstep N
    (fun i hi=>layer_supplies_clock N i hi)
  exact he

/-- A family-specific upper budget grows linearly with the layer count. -/
theorem layered_ray_upper (N K : Nat) : rayCount (layered N) K≤2*N+2 := by
  induction N with
  | zero =>
    have h1:=rayCount_const_append false 1 (List.replicate 2 true++List.replicate 2 false) K
    have h2:=rayCount_A_S_le_one 2 2 K (by decide)
    change rayCount (layered 0) K≤2
    have he : layered 0=List.replicate 1 false++(List.replicate 2 true++List.replicate 2 false) := by decide
    rw [he]
    omega
  | succ N ih =>
    have h1:=rayCount_const_append true (4*3^N) (List.replicate (6*3^N) false++layered N) K
    have h2:=rayCount_const_append false (6*3^N) (layered N) K
    rw [layered]
    omega

end Recaman.LayeredPrimitiveSupply
