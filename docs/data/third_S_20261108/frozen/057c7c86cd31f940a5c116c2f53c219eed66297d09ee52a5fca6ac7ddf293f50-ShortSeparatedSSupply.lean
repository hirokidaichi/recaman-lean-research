import Recaman.SeparatedSSourceCut

namespace Recaman.ShortSeparatedSSupply

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock
open Recaman.ShortCounterFactorBounds

private theorem gap_certificate : ∀ x∈([0,1,2,3,4] : List Int),
    ∀ y∈([0,1,2,3,4] : List Int),
    (x^2-y^2=3 ∨ x^2-y^2=8) → (x=2 ∧ y=1) ∨ (x=3 ∧ y=1) := by decide

private theorem small_square_gap (x y : Int) (hx : 0≤x) (hy : 0≤y)
    (he : x^2-y^2=3 ∨ x^2-y^2=8) : (x=2 ∧ y=1) ∨ (x=3 ∧ y=1) := by
  have hxy : y<x := by
    by_cases h : y<x
    · exact h
    · have hs:=square_lower y x hx (by omega)
      rcases he with he|he <;> omega
  have hp:=Int.mul_nonneg (show 0≤x-y-1 by omega) (show 0≤x+y-1 by omega)
  have hx4 : x≤4 := by rcases he with he|he <;> grind only
  apply gap_certificate x (by simp only [List.mem_cons]; omega)
    y (by simp only [List.mem_cons]; omega) he

private theorem equal_nonnegative_squares (x y : Int) (hx : 0≤x) (hy : 0≤y)
    (he : x^2=y^2) : x=y := by
  have hp : (x-y)*(x+y)=0 := by grind only
  rcases Int.mul_eq_zero.mp hp with h|h <;> omega

private theorem short_clock_equation (L b z y P : Int)
    (hL : L≤4) (hb : 1≤b) (hbl : b<L) (hz : 2≤z) (hy : 2≤y) (hyz : y≤z)
    (he : (b+z)^2=y^2+2*L*z) (hodd : y^2=1+2*P) : b+z-y=L := by
  rcases (show L=2 ∨ L=3 ∨ L=4 by omega) with h2|h3|h4
  · have hb1 : b=1 := by omega
    have hs : (z-1)^2=y^2 := by rw [h2,hb1] at he; grind only
    have h:=equal_nonnegative_squares (z-1) y (by omega) (by omega) hs
    omega
  · rcases (show b=1 ∨ b=2 by omega) with hb1|hb2
    · have hs : (z-2)^2-y^2=3 := by rw [h3,hb1] at he; grind only
      have h:=small_square_gap (z-2) y (by omega) (by omega) (Or.inl hs)
      rcases h with h|h <;> omega
    · have hs : y^2-(z-1)^2=3 := by rw [h3,hb2] at he; grind only
      have h:=small_square_gap y (z-1) (by omega) (by omega) (Or.inl hs)
      rcases h with h|h
      · rw [h.1] at hodd
        omega
      · rw [h.1,h.2] at hs
        simp at hs
  · rcases (show b=1 ∨ b=2 ∨ b=3 by omega) with hb1|hb2|hb3
    · have hs : (z-3)^2-y^2=8 := by rw [h4,hb1] at he; grind only
      have hz3 : 3≤z := by
        by_cases h : 3≤z
        · exact h
        · have hz2 : z=2 := by omega
          rw [hz2] at hs
          have hy2:=square_lower y 2 (by decide) hy
          grind only
      have h:=small_square_gap (z-3) y (by omega) (by omega) (Or.inr hs)
      rcases h with h|h <;> omega
    · have hs : (z-2)^2=y^2 := by rw [h4,hb2] at he; grind only
      have h:=equal_nonnegative_squares (z-2) y (by omega) (by omega) hs
      omega
    · have hs : y^2-(z-1)^2=8 := by rw [h4,hb3] at he; grind only
      have h:=small_square_gap y (z-1) (by omega) (by omega) (Or.inr hs)
      rcases h with h|h
      · rw [h.1,h.2] at hs
        simp at hs
      · omega

/-- Across an A interval of length at most four, two S sources may
coexist, but their supplied clocks must agree. -/
theorem separated_S_same_clock (m L s U v i j : Nat) (hL : L≤4) (hv : 1≤v)
    (he : sourceAt false m (List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) i)
    (hl : sourceAt false s (List.replicate U true++List.replicate v false) j) : i=j := by
  obtain ⟨b,hb,hbm,hm,hk⟩:=Recaman.SeparatedSSourceCut.earlier_S_depth_cut m L s U v i j he hl
  obtain ⟨k,hk1,hks,hml,hlk⟩:=hl
  have hbl : b<L := by omega
  have hke:=Recaman.SourceFamilyFreeCount.runKey_five_runs b L s U v
  have hk_norm : runKey (List.replicate b false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)= -2 := by
    simpa only [List.append_assoc] using hk
  have hk' : 4*(L : Int)*((s : Int)+(v : Int))+4*(U : Int)*(v : Int)-
      2*((b : Int)+(s : Int)+(v : Int))^2= -2 := by
    simpa only [List.append_assoc] using hke.symm.trans hk_norm
  rw [←List.append_assoc,runKey_S_A_S] at hlk
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hm hml
  have hs:=short_clock_equation (L : Int) (b : Int) ((s : Int)+(v : Int))
    ((k : Int)+(v : Int)) ((U : Int)*(v : Int)) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by grind only) (by grind only)
  omega

/-- Both S families do occur in a unit clock at L2; absence is stronger
than the true one-clock conclusion. -/
theorem length_two_shared_clock_witness :
    sourceAt false 1 (List.replicate 2 true++List.replicate 3 false++
      List.replicate 4 true++List.replicate 1 false) 0 ∧
    sourceAt false 3 (List.replicate 4 true++List.replicate 1 false) 0 := by
  constructor
  · exact ⟨1,by decide,by decide,by decide,by decide⟩
  · exact ⟨2,by decide,by decide,by decide,by decide⟩

/-- Length five admits distinct clocks, so the bound four is sharp
for this unrestricted literal source statement. -/
theorem length_five_distinct_clock_witness :
    sourceAt false 3 (List.replicate 5 true++List.replicate 2 false++
      List.replicate 2 true++List.replicate 2 false) 1 ∧
    sourceAt false 2 (List.replicate 2 true++List.replicate 2 false) 2 := by
  constructor
  · exact ⟨3,by decide,by decide,by decide,by decide⟩
  · exact ⟨1,by decide,by decide,by decide,by decide⟩

end Recaman.ShortSeparatedSSupply
