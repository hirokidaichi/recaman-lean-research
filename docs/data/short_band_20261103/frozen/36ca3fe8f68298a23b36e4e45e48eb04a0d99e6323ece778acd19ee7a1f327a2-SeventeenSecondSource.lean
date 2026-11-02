import Recaman.RunClockClassifier
import Recaman.HeadRunCountBounds
namespace Recaman.SeventeenSecondSource
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem initial_source_impossible (M m L s q i : Int)
    (hM : 3≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hq : 1≤q)
    (hi : 0≤i) (hiL : i<L) (hW5 : 5≤M+L) (hW9 : M+L≤9)
    (hI : M*(m+s)+L*s=17) (hbal : M+i=q+m+1)
    (hkey : (q+m)^2=2*(M*m)+1) : False := by
  have hprod:=Int.mul_nonneg (show 0≤M+L by omega) (show 0≤s-1 by omega)
  have heprod : (M+L)*(s-1)=M*s+L*s-M-L := by grind only
  have heI : M*(m+s)+L*s=M*m+(M+L)*s := by grind only
  have hQ5 : q+m≤5 := by
    by_cases h5 : q+m≤5
    · exact h5
    have hsq:=Recaman.ShortCounterFactorBounds.square_lower (q+m) 6 (by omega) (by omega)
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
    rw [hm1] at hI hMm
    have hM4 : M=4 := by omega
    rw [hM4] at hI hW5 hW9
    have he : 4*(1+s)+L*s=4+(4+L)*s := by grind only
    have hps:=Int.mul_nonneg (show 0≤4+L-5 by omega) (show 0≤s by omega)
    have hpe : (4+L-5)*s=(4+L)*s-5*s := by grind only
    have hs2 : s=1 ∨ s=2 := by omega
    rcases hs2 with h1 | h2
    · rw [h1] at hI; omega
    · rw [h2] at hI; omega
  · rw [h4] at hkey; omega
  · rw [h5] at hkey
    have hMm : M*m=12 := by omega
    have hW7 : 7≤M+L := by omega
    omega

/-- All local suppliers of the second ray are clock2 in the internally derived K17/W5..9 region. -/
theorem second_clock_two (h M m L s i : Nat) (hM : 3≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hW5 : 5≤M+L) (hW9 : M+L≤9)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=17)
    (hi : i<L) (he : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate i true)=true) : i=2 := by
  have hc:=Recaman.RunClockClassifier.secondClock_sound h M m i hm he
  simp only [Recaman.RunClockClassifier.secondClock,decide_eq_true_eq] at hc
  rcases hc with h2 | hsource
  · exact h2
  · have hfalse:=initial_source_impossible (M : Int) (m : Int) (L : Int) (s : Int)
      ((i : Int)+(M : Int)-(m : Int)-1) (i : Int)
      (by omega) (by omega) (by omega) (by omega) hsource.1 (by omega) (by omega)
      (by omega) (by omega) hI (by omega) (by grind only)
    exact False.elim hfalse

theorem second_ray_one (h M m L s : Nat) (hM : 3≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hW5 : 5≤M+L) (hW9 : M+L≤9)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=17) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 := by
  unfold rayCount
  apply cN_le_one_of_unique
  intro i hi j hj hei hej
  have h1:=second_clock_two h M m L s i hM hm hL hs hW5 hW9 hI (by omega) (by simpa only [List.append_assoc] using hei)
  have h2:=second_clock_two h M m L s j hM hm hL hs hW5 hW9 hI (by omega) (by simpa only [List.append_assoc] using hej)
  omega

theorem long_initial (M h m s L : Int) (hM4 : 4≤M) (hM6 : M≤6)
    (hh : h+m+s=13) (hm : 1≤m) (hs : 1≤s) (hL : 1≤L)
    (hI : M*(m+s)+L*s=17) : 2*M≤h+3 := by
  by_cases hl : 2*M≤h+3
  · exact hl
  exfalso
  have hp:=Int.mul_nonneg (show 0≤M-4 by omega) (show 0≤6-M by omega)
  have he : (M-4)*(6-M)=10*M-M^2-24 := by grind only
  have hq : 17-2*M≤m+s := by omega
  have hpq:=Int.mul_nonneg (show 0≤M by omega) (show 0≤m+s-(17-2*M) by omega)
  have heq : M*(m+s-(17-2*M))=M*(m+s)-17*M+2*M^2 := by grind only
  have hLp:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hLe : (L-1)*s=L*s-s := by grind only
  omega
end Recaman.SeventeenSecondSource
