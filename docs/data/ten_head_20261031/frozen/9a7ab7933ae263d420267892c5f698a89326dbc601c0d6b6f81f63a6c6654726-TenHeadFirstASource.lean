import Recaman.TenHeadSourcePruning

namespace Recaman.TenHeadFirstASource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunTargetArea Recaman.SourceFamilyFreeCount

/-- In the first target-derived case, a source in the first A run
forces an odd third separator. No head table or cutoff is assumed. -/
theorem first_A_source_odd_separator (h M m L s U e i : Nat)
    (hh : 1≤h) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : h+m+s=10) (hA : M+L+U=10) (he : 1≤e) (heM : e≤M) (hi : i<5)
    (haz : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -46)
    (hbal : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate 1 false)+(i : Int)=1)
    (hkey : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate 1 false)= -2) :
    h=6 ∧ M=6 ∧ (s=1 ∨ s=3) := by
  have hzkey:=runKey_five_runs h M m L s
  have hmass : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hz : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -92 := by
    unfold runKey
    rw [hmass,haz]
    decide
  rw [runKey_append_A,hzkey] at hz
  have hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=27 := by
    have hSc : (h : Int)+(m : Int)+(s : Int)=10 := by omega
    rw [hSc] at hz
    grind only
  have hk:=runKey_seven_runs 0 e m L s U 1
  simp only [List.replicate_zero,List.nil_append,Int.natCast_zero,Int.natCast_one,Int.zero_add] at hk
  rw [hk] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A,Int.natCast_one] at hbal
  have heq : 46-(h : Int)*(h : Int)=2*(2-(i : Int))*(11-(h : Int)) := by
    have hSc : (m : Int)+(s : Int)=10-(h : Int) := by omega
    have hAc : (L : Int)+(U : Int)=10-(M : Int) := by omega
    grind only
  have hh8 : h≤8 := by omega
  have hhcases : h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 ∨ h=7 ∨ h=8 := by omega
  have hhi : h=6 ∧ i=1 := by
    rcases hhcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Int.natCast_ofNat] at heq <;> omega
  have hM6 : 6≤M := by omega
  have hms : (m : Int)+(s : Int)=4 := by omega
  rw [hms] at hI
  have hLspos : 1≤(L : Int)*(s : Int) := by
    have hp:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
    grind only
  have hMeq : M=6 := by omega
  rw [hMeq] at hI
  have hs3 : s≤3 := by omega
  have hscases : s=1 ∨ s=2 ∨ s=3 := by omega
  have hsodd : s=1 ∨ s=3 := by
    rcases hscases with h1|h2|h3
    · exact Or.inl h1
    · rw [h2] at hI
      omega
    · exact Or.inr h3
  exact ⟨hhi.1,hMeq,hsodd⟩

/-- In that odd-separator branch a second-A-run source is impossible;
its key equation would equate a multiple of four with 6 or30. -/
theorem second_A_odd_source_excluded (e s U : Nat) (hs : s=1 ∨ s=3) :
    runKey (List.replicate e true++List.replicate s false++List.replicate U true++
      List.replicate 1 false)≠ -2 := by
  intro hk
  have he:=runKey_five_runs 0 e s U 1
  simp only [List.replicate_zero,List.nil_append] at he
  rw [he] at hk
  rcases hs with rfl|rfl <;> simp only [Int.natCast_zero,Int.natCast_one,Int.natCast_ofNat] at hk <;> omega

end Recaman.TenHeadFirstASource
