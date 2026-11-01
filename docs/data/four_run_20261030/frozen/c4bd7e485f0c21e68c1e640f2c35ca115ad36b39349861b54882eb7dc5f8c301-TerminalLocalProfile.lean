import Recaman.AdjacentRunSupply

namespace Recaman.TerminalLocalProfile

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply

def seed : List Bool := List.replicate 5 false++List.replicate 3 true++
  List.replicate 4 false++List.replicate 4 true++[false]++List.replicate 3 true

private theorem square_gap_nonneg (x k d : Int) (hx : 0≤x) (hk : 0≤k)
    (hlo : k*k<d) (hhi : d<(k+1)*(k+1)) : x*x≠d := by
  intro he
  by_cases hh : x≤k
  · have hp:=Int.mul_nonneg (show 0≤k-x by omega) (show 0≤k+x by omega)
    grind only
  · have hp:=Int.mul_nonneg (show 0≤x-k-1 by omega) (show 0≤x+k+1 by omega)
    grind only

private theorem square_gap (x k d : Int) (hk : 0≤k)
    (hlo : k*k<d) (hhi : d<(k+1)*(k+1)) : x*x≠d := by
  by_cases hx : 0≤x
  · exact square_gap_nonneg x k d hx hk hlo hhi
  · have h:=square_gap_nonneg (-x) k d (by omega) hk hlo hhi
    intro he
    apply h
    grind only

/-- Every source inside the fixed seed is classified by its quadratic
in v. There is no numeric bound on v or on the future A clock i. -/
theorem seed_source_roots (v i t : Nat) (hv : 1≤v) (ht : t<20)
    (hm : mass (seed.drop t)+(i : Int)-(v : Int)=1)
    (hk : runKey (seed.drop t)+4*(v : Int)*mass (seed.drop t)-2*(v : Int)^2= -2) :
    (v=4 ∧ i=3) ∨ (v=8 ∧ i=5) := by
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 ∨ t=17 ∨ t=18 ∨ t=19 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hmval : mass (seed.drop 0)=0 := by decide
    have hkval : runKey (seed.drop 0)=-124 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-0)*((v : Int)-0)=-61 := by grind only
    have hn:=Int.sq_nonneg ((v : Int)-0)
    grind only
  · have hmval : mass (seed.drop 1)=1 := by decide
    have hkval : runKey (seed.drop 1)=-86 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-1)*((v : Int)-1)=-41 := by grind only
    have hn:=Int.sq_nonneg ((v : Int)-1)
    grind only
  · have hmval : mass (seed.drop 2)=2 := by decide
    have hkval : runKey (seed.drop 2)=-52 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-2)*((v : Int)-2)=-21 := by grind only
    have hn:=Int.sq_nonneg ((v : Int)-2)
    grind only
  · have hmval : mass (seed.drop 3)=3 := by decide
    have hkval : runKey (seed.drop 3)=-22 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-3)*((v : Int)-3)=-1 := by grind only
    have hn:=Int.sq_nonneg ((v : Int)-3)
    grind only
  · have hmval : mass (seed.drop 4)=4 := by decide
    have hkval : runKey (seed.drop 4)=4 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-4)*((v : Int)-4)=19 := by grind only
    exact False.elim (square_gap ((v : Int)-4) 4 19 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 5)=5 := by decide
    have hkval : runKey (seed.drop 5)=26 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-5)*((v : Int)-5)=39 := by grind only
    exact False.elim (square_gap ((v : Int)-5) 6 39 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 6)=4 := by decide
    have hkval : runKey (seed.drop 6)=6 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-4)*((v : Int)-4)=20 := by grind only
    exact False.elim (square_gap ((v : Int)-4) 4 20 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 7)=3 := by decide
    have hkval : runKey (seed.drop 7)=-14 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-3)*((v : Int)-3)=3 := by grind only
    exact False.elim (square_gap ((v : Int)-3) 1 3 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 8)=2 := by decide
    have hkval : runKey (seed.drop 8)=-34 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-2)*((v : Int)-2)=-12 := by grind only
    have hn:=Int.sq_nonneg ((v : Int)-2)
    grind only
  · have hmval : mass (seed.drop 9)=3 := by decide
    have hkval : runKey (seed.drop 9)=-16 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-3)*((v : Int)-3)=2 := by grind only
    exact False.elim (square_gap ((v : Int)-3) 1 2 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 10)=4 := by decide
    have hkval : runKey (seed.drop 10)=-2 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-4)*((v : Int)-4)=16 := by grind only
    have hp : ((v : Int)-4-4)*((v : Int)-4+4)=0 := by grind only
    rcases Int.mul_eq_zero.mp hp with h|h <;> omega
  · have hmval : mass (seed.drop 11)=5 := by decide
    have hkval : runKey (seed.drop 11)=8 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-5)*((v : Int)-5)=30 := by grind only
    exact False.elim (square_gap ((v : Int)-5) 5 30 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 12)=6 := by decide
    have hkval : runKey (seed.drop 12)=14 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-6)*((v : Int)-6)=44 := by grind only
    exact False.elim (square_gap ((v : Int)-6) 6 44 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 13)=5 := by decide
    have hkval : runKey (seed.drop 13)=10 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-5)*((v : Int)-5)=31 := by grind only
    exact False.elim (square_gap ((v : Int)-5) 5 31 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 14)=4 := by decide
    have hkval : runKey (seed.drop 14)=6 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-4)*((v : Int)-4)=20 := by grind only
    exact False.elim (square_gap ((v : Int)-4) 4 20 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 15)=3 := by decide
    have hkval : runKey (seed.drop 15)=2 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-3)*((v : Int)-3)=11 := by grind only
    exact False.elim (square_gap ((v : Int)-3) 3 11 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 16)=2 := by decide
    have hkval : runKey (seed.drop 16)=-2 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-2)*((v : Int)-2)=4 := by grind only
    have hp : ((v : Int)-2-2)*((v : Int)-2+2)=0 := by grind only
    rcases Int.mul_eq_zero.mp hp with h|h <;> omega
  · have hmval : mass (seed.drop 17)=3 := by decide
    have hkval : runKey (seed.drop 17)=0 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-3)*((v : Int)-3)=10 := by grind only
    exact False.elim (square_gap ((v : Int)-3) 3 10 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 18)=2 := by decide
    have hkval : runKey (seed.drop 18)=0 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-2)*((v : Int)-2)=5 := by grind only
    exact False.elim (square_gap ((v : Int)-2) 2 5 (by decide) (by decide) (by decide) he)
  · have hmval : mass (seed.drop 19)=1 := by decide
    have hkval : runKey (seed.drop 19)=0 := by decide
    rw [hmval] at hm
    rw [hmval,hkval] at hk
    have he : ((v : Int)-1)*((v : Int)-1)=2 := by grind only
    exact False.elim (square_gap ((v : Int)-1) 1 2 (by decide) (by decide) (by decide) he)

end Recaman.TerminalLocalProfile
