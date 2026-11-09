import Recaman.RankThreeReverseClock
import Recaman.SmallReverseSupplyCount
import Recaman.ForwardSourceActualFreeThree

namespace Recaman.RankTwoDistinctClocks

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.SmallReverseSupplyCount
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

private theorem reverse_cross_band (a s d F Q : Int)
    (ha : a≤5) (hs : 0≤s) (hd : 1≤d) (hf : 1≤F) (ho : F%2=1) (hp : s%2=0)
    (hM : a=s+d) (hQ : Q=2*s^2-4*d*F) (hQ0 : 0≤Q) :
    (s=2 ∧ a=3 ∧ Q=4) ∨ (s=2 ∧ a=4 ∧ Q=0) ∨
      (s=4 ∧ a=5 ∧ 0<Q ∧ Q≤28 ∧ Q%8=4) := by
  have hPos:=Int.mul_pos (show 0<d by omega) (show 0<F by omega)
  have hs0 : s≠0 := by
    intro h
    rw [h] at hQ
    grind only
  have hS : s=2 ∨ s=4 := by omega
  rcases hS with h2|h4
  · rw [h2] at hQ
    have h1:=Int.mul_nonneg (show 0≤d-1 by omega) (show 0≤F by omega)
    have h2':=Int.mul_nonneg (show 0≤F-1 by omega) (show 0≤d by omega)
    have hF : F≤2 := by grind only
    have hF1 : F=1 := by omega
    rw [hF1] at hQ
    omega
  · have hd1 : d=1 := by omega
    rw [h4,hd1] at hQ
    omega

/-- Reverse order also needs at least three original free additions
between the two starts when the original old history is a BlockWord. -/
theorem reverse_pair_needs_three_actual_free (f : Nat → Bool) (n K i j : Nat) (w u : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hji : j<i) (hu : runKey u= -2) (hpu : runKey (seg f n K++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (seg f n K++u)+(j : Int)=1) :
    3≤free f n K := by
  by_cases hFree : free f n K≤2
  · let a:=additions f n K
    let s:=subtractions f n K
    let d:=(i : Int)-(j : Int)
    let F:=cntF u
    let q:=cross (seg f n K)
    have ha:=positive_r3_additions_free_bound f n 0 K hw
      (by simpa only [List.replicate_zero,List.append_nil] using hpre) hpos
      (by change free f n K≤3; omega)
    change a≤2*free f n K+1 at ha
    obtain ⟨hm,hpar,hk⟩:=Recaman.RankThreeReverseClock.reverse_data
      (seg f n K) u i j hu hpu hmu hmpu
    change mass (seg f n K)=d at hm
    change runKey (seg f n K)= -(4*d*(F : Int)) at hk
    rw [cntF_seg] at hpar
    change (s : Int)%2=0 at hpar
    have hM:=seg_mass f n K
    have hwalk:=(cN_walk f n K).1
    change Fw f (n+K)=Fw f n+(a : Int)-(s : Int) at hwalk
    have hAdd : (a : Int)=(s : Int)+d := by omega
    have hQe : q=2*(s : Int)^2-4*d*(F : Int) := by
      unfold q cross
      rw [hk,cntF_seg]
      change -(4*d*(F : Int))+2*(s : Int)^2=_
      omega
    have hQ : 0≤q := cross_nonnegative (seg f n K)
    have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hu
    change (F : Int)%2=1 at hodd
    have hb:=reverse_cross_band (a : Int) (s : Int) d (F : Int) q
      (by omega) (by omega) (by dsimp [d]; omega) (by omega) hodd hpar hAdd hQe hQ
    obtain ⟨h2,h1,h0⟩:=small_reverse_supply_bounds f n K w hw hpre
      (by change a≤5; omega) (by change s≤4; omega) (by change q≤28; omega)
      (by change q≠16; omega) (by change q=0 → s≤2; omega)
    have hspl : a=cN (EndN f 0) n K+free f n K := additions_split f n K
    rcases hb with ⟨hs,ha,hq⟩|⟨hs,ha,hq⟩|⟨hs,ha,hq,_,_⟩
    · have he:=h0 (by change s≤2; omega) (by change a≤3; omega) hq
      omega
    · have he:=h1 (by change s≤2; omega)
      omega
    · omega
  · omega

/-- Both orders of two distinct primitive clocks require three original
free additions in the same positive interval. -/
theorem distinct_pair_needs_three_actual_free (f : Nat → Bool) (n K i j : Nat) (w u : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hne : i≠j) (hu : runKey u= -2) (hpu : runKey (seg f n K++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (seg f n K++u)+(j : Int)=1) :
    3≤free f n K := by
  by_cases h : i<j
  · exact Recaman.ForwardSourceActualFreeThree.forward_pair_needs_three_actual_free
      f n K i j w u hw hpre hpos h hu hpu hmu hmpu
  · exact reverse_pair_needs_three_actual_free f n K i j w u hw hpre hpos
      (by omega) hu hpu hmu hmpu

end Recaman.RankTwoDistinctClocks
