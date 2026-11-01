import Recaman.MomentSmallHeadPruning

namespace Recaman.MomentFirstASource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunTargetArea Recaman.MomentSmallHeadPruning Recaman.ShortGapSourceClocks

/-- A first-A source retains the moment of the same full head. The
source may have any positive remaining A length and any future clock. -/
theorem first_A_clock_equation (h M m L s U S v e i : Nat) (B : Int)
    (hS : h+m+s=S) (hA : M+L+U=S)
    (ha : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B)
    (hbal : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false)+(i : Int)=1)
    (hkey : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false)= -2) :
    B-(h : Int)^2+(v : Int)^2-1=
      2*((v : Int)+1-(i : Int))*((S : Int)-(h : Int)+(v : Int)) := by
  have hmom:=three_head_moment h M m L s U (by omega) B ha
  have hSc : (h : Int)+(m : Int)+(s : Int)=(S : Int) := by omega
  rw [hSc] at hmom
  have hk:=runKey_seven_runs 0 e m L s U v
  simp only [List.replicate_zero,List.nil_append] at hk
  rw [hk] at hkey
  simp only [Int.natCast_zero,Int.zero_add] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
  have heval : (e : Int)=(M : Int)-(h : Int)+(v : Int)+1-(i : Int) := by omega
  have hUval : (U : Int)=(S : Int)-(M : Int)-(L : Int) := by omega
  have hmval : (m : Int)=(S : Int)-(h : Int)-(s : Int) := by omega
  rw [heval,hUval,hmval] at hkey
  rw [hmval] at hmom
  grind only

/-- In the mass-two v=1 counter parameters, neither odd clock1 nor3
can come from the first A run. -/
theorem first_A_one_gap_low_clock (h S i : Nat) (B : Int) (hh : 1≤h)
    (hS12 : 12≤S) (hS14 : S≤14) (hB : B=4*(S : Int)+27 ∨ B=4*(S : Int)+28)
    (hi : i<4)
    (he : B-(h : Int)^2=2*(2-(i : Int))*((S : Int)-(h : Int)+1)) : i=0 ∨ i=2 := by
  have hiv : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hiv with hi0|rfl|hi2|rfl
  · exact Or.inl hi0
  · have hx : ((h : Int)-1)*((h : Int)-1)=B-2*(S : Int)-1 := by grind only
    have hn:=nonnegative_square_gap ((h : Int)-1) 7 (B-2*(S : Int)-1)
      (by omega) (by decide) (by rcases hB with hB|hB <;> omega) (by rcases hB with hB|hB <;> omega)
    exact False.elim (hn hx)
  · exact Or.inr hi2
  · have hx : ((h : Int)+1)*((h : Int)+1)=B+2*(S : Int)+3 := by grind only
    have hn:=nonnegative_square_gap ((h : Int)+1) 10 (B+2*(S : Int)+3)
      (by omega) (by decide) (by rcases hB with hB|hB <;> omega) (by rcases hB with hB|hB <;> omega)
    exact False.elim (hn hx)

/-- In the v=2 three numerical head cases, the first A family again
merges into0/2. The omitted odd-parity parameter S14/B85 is not admitted. -/
theorem first_A_two_gap_low_clock (h S i : Nat) (B : Int) (hh : 1≤h)
    (hSB : (S=12 ∧ B=76) ∨ (S=13 ∧ B=81) ∨ (S=14 ∧ B=84))
    (hi : i<5)
    (he : B-(h : Int)^2+3=2*(3-(i : Int))*((S : Int)-(h : Int)+2)) : i=0 ∨ i=2 := by
  have hiv : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hiv with hi0|rfl|hi2|rfl|rfl
  · exact Or.inl hi0
  · have hx : ((h : Int)-2)*((h : Int)-2)=B-4*(S : Int)-1 := by grind only
    have hhh : 2≤h := by
      by_cases hh2 : 2≤h
      · exact hh2
      · have hh1 : h=1 := by omega
        rw [hh1] at he
        rcases hSB with hSB|hSB|hSB <;> omega
    have hn:=nonnegative_square_gap ((h : Int)-2) 5 (B-4*(S : Int)-1)
      (by omega) (by decide) (by rcases hSB with hSB|hSB|hSB <;> omega)
      (by rcases hSB with hSB|hSB|hSB <;> omega)
    exact False.elim (hn hx)
  · exact Or.inr hi2
  · have hx : (h : Int)*(h : Int)=B+3 := by grind only
    by_cases h76 : B=76
    · have hn:=nonnegative_square_gap (h : Int) 8 79 (by omega) (by decide) (by decide) (by decide)
      exact False.elim (hn (by omega))
    · have hn:=nonnegative_square_gap (h : Int) 9 (B+3) (by omega) (by decide)
        (by rcases hSB with hSB|hSB|hSB <;> omega) (by rcases hSB with hSB|hSB|hSB <;> omega)
      exact False.elim (hn hx)
  · have hx : ((h : Int)+1)*((h : Int)+1)=B+2*(S : Int)+8 := by grind only
    have hn:=nonnegative_square_gap ((h : Int)+1) 10 (B+2*(S : Int)+8)
      (by omega) (by decide) (by rcases hSB with hSB|hSB|hSB <;> omega)
      (by rcases hSB with hSB|hSB|hSB <;> omega)
    exact False.elim (hn hx)

end Recaman.MomentFirstASource
