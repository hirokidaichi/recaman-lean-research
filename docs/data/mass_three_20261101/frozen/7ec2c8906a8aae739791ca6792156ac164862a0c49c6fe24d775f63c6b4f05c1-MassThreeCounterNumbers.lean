import Recaman.MomentFirstASource
import Recaman.LowerMomentOldClock

namespace Recaman.MassThreeCounterNumbers

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentSmallHeadPruning Recaman.ShortGapSourceClocks

theorem mass_three_area_options (u : List Bool) (hu : BlockWord u) (hm : mass u=3) :
    areaW u=5 ∨ areaW u=6 ∨ areaW u=7 := by
  rcases block_mass_three hu hm with rfl|rfl|rfl <;> decide

theorem mass_four_area_options (u : List Bool) (hu : BlockWord u) (hm : mass u=4) :
    areaW u=9 ∨ areaW u=10 ∨ areaW u=11 ∨ areaW u=12 ∨ areaW u=13 := by
  have h:=block_mass_four hu hm
  simp only [massFourWords,List.mem_cons,List.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- Actual count and the genuine three-run moment are supplied separately
by the caller. This small scalar pruning does not classify histories. -/
theorem counter_numbers (S R : Nat) (B a4 a3 I : Int)
    (hS : S≤16) (hR : 5≤R)
    (h4 : a4=9 ∨ a4=10 ∨ a4=11 ∨ a4=12 ∨ a4=13)
    (h3 : a3=5 ∨ a3=6 ∨ a3=7)
    (hB : B=8*(S : Int)+a4+6)
    (hc : (R : Int)^2=2*(S : Int)+3+a4-a3)
    (hm : B=(S : Int)^2-2*I) (hI : 3≤I) (hp : B%2=(S : Int)%2) :
    R=6 ∧ ((S=13 ∧ B=123) ∨ (S=14 ∧ B=128) ∨
      (S=14 ∧ B=130) ∨ (S=15 ∧ B=135)) := by
  have h4lo : 9≤a4 := by omega
  have h4hi : a4≤13 := by omega
  have h3lo : 5≤a3 := by omega
  have h3hi : a3≤7 := by omega
  have hR6 : R≤6 := by
    by_cases h : R≤6
    · exact h
    · have hq:=Int.mul_nonneg (show 0≤(R : Int)-7 by omega)
        (show 0≤(R : Int)+7 by omega)
      grind only
  have hRne : R≠5 := by
    intro he
    rw [he] at hc
    have hS10 : (S : Int)≤10 := by omega
    have hq:=Int.mul_nonpos_of_nonpos_of_nonneg (show (S : Int)-10≤0 by omega)
      (show 0≤(S : Int)+2 by omega)
    grind only
  have hRval : R=6 := by omega
  refine ⟨hRval,?_⟩
  rw [hRval] at hc
  have hs : S=13 ∨ S=14 ∨ S=15 := by omega
  rcases hs with rfl|rfl|rfl <;>
    rcases h4 with rfl|rfl|rfl|rfl|rfl <;>
    rcases h3 with rfl|rfl|rfl <;> omega

private theorem square_gap (x k d : Int) (hk : 0≤k)
    (hlo : k*k<d) (hhi : d<(k+1)*(k+1)) : x*x≠d := by
  by_cases hx : 0≤x
  · exact nonnegative_square_gap x k d hx hk hlo hhi
  · have hn:=nonnegative_square_gap (-x) k d (by omega) hk hlo hhi
    intro he
    apply hn
    grind only

/-- In the four actual-counter parameter cases a first-A supplier merges
with clocks0/2. The M bound is derived from actual first-run free counts. -/
theorem first_A_counter_clock (h M m L s U i : Nat) (B : Int)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzero : M+L+U=h+m+s) (hM7 : M≤7) (hi : i<6)
    (hSB : (h+m+s=13 ∧ B=123) ∨ (h+m+s=14 ∧ B=128) ∨
      (h+m+s=14 ∧ B=130) ∨ (h+m+s=15 ∧ B=135))
    (haz : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B)
    (heq : B-(h : Int)^2+8=2*(4-(i : Int))*
      (((h+m+s : Nat) : Int)-(h : Int)+3)) : i=0 ∨ i=2 := by
  have hmom:=three_head_moment h M m L s U hzero B haz
  have hiv : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases hiv with hi0|rfl|hi2|rfl|rfl|rfl
  · exact Or.inl hi0
  · have hx : ((h : Int)-3)*((h : Int)-3)=B-6*((h+m+s : Nat) : Int)-1 := by grind only
    have hn:=square_gap ((h : Int)-3) 6 (B-6*((h+m+s : Nat) : Int)-1)
      (by decide) (by rcases hSB with h|h|h|h <;> omega)
      (by rcases hSB with h|h|h|h <;> omega)
    exact False.elim (hn hx)
  · exact Or.inr hi2
  · have hx : ((h : Int)-1)*((h : Int)-1)=B-2*((h+m+s : Nat) : Int)+3 := by grind only
    by_cases hB : B=123
    · have hS : h+m+s=13 := by rcases hSB with h|h|h|h <;> omega
      have hx100 : ((h : Int)-1)*((h : Int)-1)=100 := by omega
      have hz : ((h : Int)-11)*((h : Int)+9)=0 := by grind only
      have hh11 : h=11 := by rcases Int.mul_eq_zero.mp hz with h|h <;> omega
      have hm1 : m=1 := by omega
      have hs1 : s=1 := by omega
      rw [hm1,hs1,hh11] at hmom hzero
      simp only [Int.natCast_one] at hmom
      have hLU : (L : Int)+(U : Int)≤13-(M : Int) := by omega
      grind only
    · have hn:=square_gap ((h : Int)-1) 10 (B-2*((h+m+s : Nat) : Int)+3)
        (by decide) (by rcases hSB with h|h|h|h <;> omega)
        (by rcases hSB with h|h|h|h <;> omega)
      exact False.elim (hn hx)
  · have hx : (h : Int)*(h : Int)=B+8 := by grind only
    have hn:=square_gap (h : Int) 11 (B+8) (by decide)
      (by rcases hSB with h|h|h|h <;> omega) (by rcases hSB with h|h|h|h <;> omega)
    exact False.elim (hn hx)
  · have hx : ((h : Int)+1)*((h : Int)+1)=B+2*((h+m+s : Nat) : Int)+15 := by grind only
    by_cases hB : B=123
    · have hS : h+m+s=13 := by rcases hSB with h|h|h|h <;> omega
      have hn:=square_gap ((h : Int)+1) 12 164 (by decide) (by decide) (by decide)
      exact False.elim (hn (by omega))
    · have hn:=square_gap ((h : Int)+1) 13 (B+2*((h+m+s : Nat) : Int)+15)
        (by decide) (by rcases hSB with h|h|h|h <;> omega)
        (by rcases hSB with h|h|h|h <;> omega)
      exact False.elim (hn hx)

end Recaman.MassThreeCounterNumbers
