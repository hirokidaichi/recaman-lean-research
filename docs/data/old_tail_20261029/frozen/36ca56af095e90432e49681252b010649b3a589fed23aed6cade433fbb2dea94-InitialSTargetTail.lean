import Recaman.InitialSTargetOldPair

namespace Recaman.InitialSTargetTail

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.OldTargetMiddleCharge Recaman.InitialSTargetBounds
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Initial-S target: a final-band first-A source forces q>=j+1,
hence a stronger total-A budget. No bound on the real initial S length. -/
theorem first_A_tail_budget (q M m L s i T j e : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    j+1≤q ∧ 2*(j+1)+(m+s)≤M+L+T := by
  have hp : 0≤(M : Int)-(e : Int)-(q : Int) := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1 hmt
    omega
  have ht := source_key_before_gap
    (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T j hmt hat
  rw [runKey_five_runs] at ht
  have hke := runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append,Int.natCast_zero,Int.zero_add] at hke
  rw [hke] at hk1
  have hprod := Int.mul_nonneg hp (show 0≤(m : Int)+(s : Int) by omega)
  have hquad : ((j : Int)+1)^2-1≤(q : Int)^2 := by grind
  have hq : j+1≤q := by
    by_cases hh : j+1≤q
    · exact hh
    · have hp := Int.mul_nonneg (show 0≤(j : Int)-(q : Int) by omega)
        (show 0≤(j : Int)+(q : Int) by omega)
      grind
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmt
  exact ⟨hq,by omega⟩

private theorem small_S_first_A_clock (m L s i e : Nat)
    (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (he : 1≤e) (hb : m+s≤4)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2) : i=2 := by
  have hK : m+s=2 ∨ m+s=3 ∨ m+s=4 := by omega
  have hkey := runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append] at hkey
  rw [hkey] at hk1
  have hLs := Int.mul_pos (show 0<(L : Int) by omega) (show 0<(s : Int) by omega)
  have heK := Int.mul_nonneg (show 0≤(e : Int)-1 by omega)
    (show 0≤(m : Int)+(s : Int) by omega)
  have heq : 2*(e : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
      ((m : Int)+(s : Int))^2-1 := by grind
  rcases hK with hK|hK|hK
  · have hc : (m : Int)+(s : Int)=2 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    have hn : 2*((2*(e : Int))+((L : Int)*(s : Int)))=3 := by grind
    omega
  · have hc : (m : Int)+(s : Int)=3 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    have hn : 6*(e : Int)+2*((L : Int)*(s : Int))=8 := by grind
    have he1 : e=1 := by omega
    have hLs1 : (L : Int)*(s : Int)=1 := by rw [he1] at hn; simp at hn; omega
    have hL1 : L=1 := by
      have hp := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
      grind
    have hs1 : s=1 := by rw [hL1] at hLs1; simp at hLs1; omega
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1
    omega
  · have hc : (m : Int)+(s : Int)=4 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    have hn : 2*((4*(e : Int))+((L : Int)*(s : Int)))=15 := by grind
    omega

end Recaman.InitialSTargetTail
