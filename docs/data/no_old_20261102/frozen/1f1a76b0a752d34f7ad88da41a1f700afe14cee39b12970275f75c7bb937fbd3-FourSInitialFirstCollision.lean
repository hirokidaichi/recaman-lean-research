import Recaman.FourSInitialTarget
import Recaman.MomentFirstASource

namespace Recaman.FourSInitialFirstCollision

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

private theorem square_not_between (x k a : Int) (hk : 0≤k)
    (hlo : k^2<a) (hhi : a<(k+1)^2) : x^2≠a := by
  intro he
  by_cases hx : x≤k ∧ -k≤x
  · have hp:=Int.mul_nonneg (show 0≤k-x by omega) (show 0≤k+x by omega)
    grind only
  · by_cases hpos : k<x
    · have hp:=Int.mul_nonneg (show 0≤x-k-1 by omega) (show 0≤x+k+1 by omega)
      grind only
    · have hp:=Int.mul_nonneg (show 0≤-x-k-1 by omega) (show 0≤-x+k+1 by omega)
      grind only

/-- The same S4 target forbids coexistence of initial-S clock0 and
first-A clock1. A three-case arithmetic pruning replaces any head table. -/
theorem initial_zero_first_one_excluded (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U R : Nat) (hzero : M+L+U=h+m+s) (hR : 5≤R) (hS14 : h+m+s≤14)
    (hkeyTarget : runKey u= -runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)-
      12*((h : Int)+(m : Int)+(s : Int))-16-2*(R : Int)^2)
    (hinit : sourceAt false h (List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate 4 false) 0) :
    ¬sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate 4 false) 1 := by
  intro he
  let S:=h+m+s
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let z:=List.replicate h false++x
  have hmz : mass z=0 := by
    simp only [z,x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=S := by
    have hm:=mass_cntF z
    have hl : z.length=h+M+m+L+s+U := by simp only [z,x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hm
    dsimp [S]
    omega
  have hkz:=Recaman.FourSInitialTarget.initial_zero_head_key x h 4 hmz
    (by simpa only [x,List.append_assoc] using hinit)
  change runKey z= -4*((4 : Int)+1)*(cntF z : Int) at hkz
  rw [hSz] at hkz
  have haz : areaW z= -10*(S : Int) := by
    unfold runKey at hkz
    rw [hmz] at hkz
    grind only
  obtain ⟨e,he,heM,hbal,hkey⟩:=he
  have heq:=Recaman.MomentFirstASource.first_A_clock_equation h M m L s U S 4 e 1 (10*(S : Int)) rfl
    (by dsimp [S]; omega)
    (by simpa only [z,x,List.append_assoc] using haz)
    hbal hkey
  have hsq : ((h : Int)-4)^2=2*(S : Int)-1 := by grind only
  have hku : runKey u=8*(S : Int)-16-2*(R : Int)^2 := by
    have ht : runKey u= -runKey z-12*(S : Int)-16-2*(R : Int)^2 := by
      simpa only [z,x,S,List.append_assoc,Int.natCast_add] using hkeyTarget
    rw [hkz] at ht
    grind only
  have hlow : -2≤runKey u := by rcases block_mass_three hu hcu with rfl|rfl|rfl <;> decide
  have hupp : runKey u≤2 := by rcases block_mass_three hu hcu with rfl|rfl|rfl <;> decide
  have hR7 : R≤7 := by
    by_cases hh : R≤7
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤(R : Int)-8 by omega) (show 0≤(R : Int)+8 by omega)
      have hS : (S : Int)≤14 := by dsimp [S]; omega
      grind only
  have hr : R=5 ∨ R=6 ∨ R=7 := by omega
  rcases hr with rfl|rfl|rfl
  · have hS8 : (S : Int)=8 := by omega
    have hn:=square_not_between ((h : Int)-4) 3 15 (by decide) (by decide) (by decide)
    exact hn (by rw [hS8] at hsq; omega)
  · have hS11 : (S : Int)=11 := by omega
    have hn:=square_not_between ((h : Int)-4) 4 21 (by decide) (by decide) (by decide)
    exact hn (by rw [hS11] at hsq; omega)
  · have hS14 : (S : Int)=14 := by omega
    have hn:=square_not_between ((h : Int)-4) 5 27 (by decide) (by decide) (by decide)
    exact hn (by rw [hS14] at hsq; omega)

end Recaman.FourSInitialFirstCollision
