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
theorem head_small_second_eight (f : Nat → Bool) (n h M m L s U : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hshape : (M=1 ∧ m=1) ∨ (M=3 ∧ 1≤m ∧ m≤3) ∨ (5≤M ∧ M≤7 ∧ m=1))
    (hlong : 4≤M → 2*M≤h+3) :
    cN (EndN f 0) n (h+M+m+L+s+U)≤8 ∧
    (M=1 → cN (EndN f 0) n (h+M+m+L+s+U)≤7) := by
  have hpref : cN (EndN f 0) n (h+M+m+L)≤3 := by
    by_cases hsum : 3≤h+m
    · have hfirst : cN (EndN f 0) (n+h) M≤1 := by
        by_cases hM3 : M≤3
        · exact Recaman.OldTargetFirstRun.first_run_supply_le_one f n h M w hw hpre hM3 hS hA
        · exact first_long_one f n h M w hw hpre (hlong (by omega)) hS hA
      have hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 :=
        small_second_local h M m L hshape
      have hsecond:=second_actual_bound f n h M m L 1 w hw hpre hsum hS hA hS2 hA2 hlocal
      have heq:=two_prefix_count f n h M m L hS hS2
      omega
    · have hx:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2
        (hpos (h+M+m+L) (by omega) (by omega))
      omega
  constructor
  · exact head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU hSsum
      hS hA hS2 hA2 hS3 hA3 hpos 3 hpref
  · intro hM1
    have hpref2 : cN (EndN f 0) n (h+M+m+L)≤2 := by
      by_cases hsum : 3≤h+m
      · have hfirst:=first_two_zero f n h M w hw hpre (by omega) hS hA
        have hsecond:=second_actual_bound f n h M m L 1 w hw hpre hsum hS hA hS2 hA2 (small_second_local h M m L hshape)
        have heq:=two_prefix_count f n h M m L hS hS2
        omega
      · have hx:=small_S_prefix f n h M m L (by omega) hS hA hS2 hA2
          (hpos (h+M+m+L) (by omega) (by omega))
        omega
    exact head_from_prefix f n h M m L s U w hw hpre hM hm hL hs hU hSsum
      hS hA hS2 hA2 hS3 hA3 hpos 2 hpref2

end Recaman.SecondRaySmallShapes
