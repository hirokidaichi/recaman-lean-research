import Recaman.S14R6LocalCertificate
import Recaman.SeventeenSecondSource
namespace Recaman.S14R6SourceShapes
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem long_initial (M h m s L : Int) (hM4 : 4≤M) (hM7 : M≤7)
    (hS : h+m+s=14) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hI : M*(m+s)+L*s≤21) : 2*M≤h+3 := by
  by_cases hl : 2*M≤h+3
  · exact hl
  exfalso
  have hp:=Int.mul_nonneg (show 0≤M-4 by omega) (show 0≤7-M by omega)
  have he : (M-4)*(7-M)=11*M-M^2-28 := by grind only
  have hq : 18-2*M≤m+s := by omega
  have hpq:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-(18-2*M) by omega)
  have heq : M*(m+s-(18-2*M))=M*(m+s)-18*M+2*M^2 := by grind only
  have hLp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hLe : (L-1)*s=L*s-s := by grind only
  omega

theorem source_numbers (M m L s q i : Int) (hM : 3≤M) (hM7 : M≤7)
    (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hq : 1≤q) (hi : 0≤i) (hiL : i<L) (hi2 : i≠2)
    (hW7 : 7≤M+L) (hW9 : M+L≤9) (hI17 : 17≤M*(m+s)+L*s) (hI21 : M*(m+s)+L*s≤21)
    (hbal : M+i=q+m+1) (hkey : (q+m)^2=2*(M*m)+1) :
    (M=4 ∧ m=1 ∧ s=2 ∧ (L=3 ∨ L=4)) ∨
    (M=3 ∧ m=4 ∧ s=1 ∧ 4≤L ∧ L≤6) ∨
    (M=6 ∧ m=2 ∧ s=1 ∧ 1≤L ∧ L≤3) := by
  have hWp:=Int.mul_nonneg (show 0≤M+L by omega) (show 0≤s-1 by omega)
  have hWe : (M+L)*(s-1)=(M+L)*s-M-L := by grind only
  have heI : M*(m+s)+L*s=M*m+(M+L)*s := by grind only
  have hQ5 : q+m≤5 := by
    by_cases h5 : q+m≤5
    · exact h5
    have hx:=Recaman.ShortCounterFactorBounds.square_lower (q+m) 6 (by omega) (by omega)
    omega
  rcases (show q+m=2 ∨ q+m=3 ∨ q+m=4 ∨ q+m=5 by omega) with h2 | h3 | h4 | h5
  · rw [h2] at hkey; omega
  · rw [h3] at hkey
    have hMm : M*m=4 := by omega
    have hm1 : m=1 := by
      by_cases h1 : m=1
      · exact h1
      have hp:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m-2 by omega)
      have he : M*(m-2)=M*m-2*M := by grind only
      omega
    rw [hm1] at hMm
    have hM4 : M=4 := by omega
    have hs2 : s=2 := by
      have hprod:=Int.mul_nonneg (show 0≤M+L by omega) (show 0≤s-3 by omega)
      have he : (M+L)*(s-3)=(M+L)*s-3*(M+L) := by grind only
      by_cases hs1 : s=1
      · rw [hM4,hm1,hs1] at hI17; omega
      by_cases hs2 : s=2
      · exact hs2
      omega
    rw [hM4,hm1,hs2] at hI17 hI21
    exact Or.inl ⟨hM4,hm1,hs2,by omega⟩
  · rw [h4] at hkey; omega
  · rw [h5] at hkey
    have hMm : M*m=12 := by omega
    have hs1 : s=1 := by
      by_cases h1 : s=1
      · exact h1
      have hp:=Int.mul_nonneg (show 0≤M+L by omega) (show 0≤s-2 by omega)
      have he : (M+L)*(s-2)=(M+L)*s-2*(M+L) := by grind only
      omega
    have hm4 : m≤4 := by
      have hp:=Int.mul_nonneg (show 0≤M-3 by omega) (show 0≤m by omega)
      have he : (M-3)*m=M*m-3*m := by grind only
      omega
    rcases (show m=1 ∨ m=2 ∨ m=3 ∨ m=4 by omega) with hm1 | hm2 | hm3 | hm4
    · rw [hm1] at hMm; omega
    · rw [hm2] at hMm
      exact Or.inr (Or.inr ⟨by omega,hm2,hs1,by omega,by omega⟩)
    · rw [hm3] at hMm; omega
    · rw [hm4] at hMm
      exact Or.inr (Or.inl ⟨by omega,hm4,hs1,by omega,by omega⟩)

/-- The eight explicit local rows are used only after source classification. -/
theorem third_from_shapes (h M m L s U : Nat) (hS : h+m+s=14) (hA : M+L+U=14)
    (hshape : (M=4 ∧ m=1 ∧ s=2 ∧ (L=3 ∨ L=4)) ∨
    (M=3 ∧ m=4 ∧ s=1 ∧ 4≤L ∧ L≤6) ∨
    (M=6 ∧ m=2 ∧ s=1 ∧ 1≤L ∧ L≤3)) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false) U≤3 := by
  rcases hshape with ⟨rfl,rfl,rfl,hL⟩ | ⟨rfl,rfl,rfl,hL4,hL6⟩ | ⟨rfl,rfl,rfl,hL1,hL3⟩
  · rcases hL with rfl | rfl
    · simpa only [show h=11 by omega,show U=7 by omega] using Recaman.S14R6LocalCertificate.third_1
    · simpa only [show h=11 by omega,show U=6 by omega] using Recaman.S14R6LocalCertificate.third_2
  · rcases (show L=4 ∨ L=5 ∨ L=6 by omega) with rfl | rfl | rfl
    · simpa only [show h=9 by omega,show U=7 by omega] using Recaman.S14R6LocalCertificate.third_3
    · simpa only [show h=9 by omega,show U=6 by omega] using Recaman.S14R6LocalCertificate.third_4
    · simpa only [show h=9 by omega,show U=5 by omega] using Recaman.S14R6LocalCertificate.third_5
  · rcases (show L=1 ∨ L=2 ∨ L=3 by omega) with rfl | rfl | rfl
    · simpa only [show h=11 by omega,show U=7 by omega] using Recaman.S14R6LocalCertificate.third_6
    · simpa only [show h=11 by omega,show U=6 by omega] using Recaman.S14R6LocalCertificate.third_7
    · simpa only [show h=11 by omega,show U=5 by omega] using Recaman.S14R6LocalCertificate.third_8
end Recaman.S14R6SourceShapes
