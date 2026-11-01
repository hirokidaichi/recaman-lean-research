import Recaman.MomentSmallHeadPruning
import Recaman.FourthSourceFamilies

namespace Recaman.ThreeGapInteriorA

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SourceFamilyFreeCount Recaman.MomentSmallHeadPruning

/-- In the exceptional S13/B79 head, the second-A family after three S
signs can only land at clock0. The competing clock4 would require the
same head moment to be both45 and at least48. -/
theorem special_second_A_clock_zero (h M m L s U e i : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS : h+m+s=13) (hA : M+L+U=13)
    (ha : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -79)
    (he : 1≤e) (heL : e≤L) (hi : i<6)
    (hbal : mass (List.replicate e true++List.replicate s false++List.replicate U true++
      List.replicate 3 false)+(i : Int)=1)
    (hkey : runKey (List.replicate e true++List.replicate s false++List.replicate U true++
      List.replicate 3 false)= -2) : i=0 := by
  have hmom:=three_head_moment h M m L s U (by omega) 79 ha
  have hSc : (h : Int)+(m : Int)+(s : Int)=13 := by omega
  rw [hSc] at hmom
  have hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=45 := by grind only
  have hk:=runKey_five_runs 0 e s U 3
  simp only [List.replicate_zero,List.nil_append] at hk
  rw [hk] at hkey
  simp only [Int.natCast_zero,Int.zero_add] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
  let p : Int:=(s : Int)+3
  let r : Int:=p-2*(e : Int)
  have hp : 4≤p := by dsimp [p]; omega
  have hrel : r+2≤p := by dsimp [r]; omega
  have hpr : p*r=6*(U : Int)+1 := by dsimp [p,r]; grind only
  have hpay : 6*(i : Int)=16-(p-3)*(r-3) := by dsimp [p,r] at *; grind only
  have hr : 1≤r := by
    by_cases he : 1≤r
    · exact he
    · have hz:=Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤p by omega) (show r≤0 by omega)
      omega
  have hr6 : r≤6 := by
    by_cases he : r≤6
    · exact he
    · have hprod:=Int.mul_nonneg (show 0≤p-9 by omega) (show 0≤r-3 by omega)
      grind only
  have hrv : r=1 ∨ r=5 := by
    have hc : r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 := by omega
    rcases hc with h1|h2|h3|h4|h5|h6
    · exact Or.inl h1
    · rw [h2] at hpr; omega
    · rw [h3] at hpr; omega
    · rw [h4] at hpr; omega
    · exact Or.inr h5
    · rw [h6] at hpr; omega
  rcases hrv with hr1|hr5
  · have hpU : p=6*(U : Int)+1 := by rw [hr1] at hpr; omega
    have hiU : (i : Int)=2*(U : Int)+2 := by rw [hr1,hpU] at hpay; grind only
    have hU1 : U=1 := by omega
    have hs4 : s=4 := by dsimp [p] at hpU; omega
    rw [hs4] at hI
    have hAL : (M : Int)+(L : Int)=12 := by omega
    have hprod:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int) by omega)
    grind only
  · have hiLin : 3*(i : Int)=11-p := by rw [hr5] at hpay; grind only
    rw [hr5] at hpr
    omega

end Recaman.ThreeGapInteriorA
