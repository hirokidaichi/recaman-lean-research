import Recaman.AdditionRankSlack

namespace Recaman.ForwardSourceFreeTwoFactor

open Recaman.AdditionRankSlack Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.PrefixMassBarrier Recaman.BlockOldRay Recaman.RunSupplyKeys
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem rank_two_identity (a s q : Int) :
    4*a*s-2*s^2-q-(4*a+2*(a-2)*(a-2+1))=2*a-4-(q+2*(a-s)^2) := by
  grind only

/-- Rank two bounds the key and the squared mass together, with the
original supplied and free counts used for the positivity constraint. -/
theorem key_mass_rank_two (f : Nat → Bool) (n K : Nat)
    (ha : 2≤additions f n K)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n K≤2) :
    runKey (seg f n K)+2*(mass (seg f n K))^2≤2*(additions f n K : Int)-4 := by
  let a:=additions f n K
  let s:=subtractions f n K
  have hA : 2≤a := ha
  have hcast : (((a-2 : Nat) : Int))=(a : Int)-2 := by omega
  have hM:=seg_mass f n K
  have hW:=(cN_walk f n K).1
  change Fw f (n+K)=Fw f n+(a : Int)-(s : Int) at hW
  have hms : mass (seg f n K)=(a : Int)-(s : Int) := by omega
  have h:=rankSlack_mono f n 2 K hp hf 0 K (Nat.zero_le _) (Nat.le_refl _)
  rw [rankSlack_zero] at h
  change 0≤4*(a : Int)*(s : Int)-2*(s : Int)^2-runKey (seg f n K)-rankCost 2 a at h
  unfold rankCost at h
  rw [hcast,rank_two_identity] at h
  rw [hms]
  omega

private theorem unit_factor (a d F : Int) (ha : a≤5) (hd : 1≤d) (hF : 1≤F)
    (h : 4*d*F+2*(-d)^2≤2*a-4) : a=5 ∧ d=1 ∧ F=1 := by
  have hprod:=Int.mul_nonneg (show 0≤d by omega) (show 0≤F-1 by omega)
  have hd1 : d=1 := by
    by_cases he : d=1
    · exact he
    · have hp:=Int.mul_pos (show 0<d-1 by omega) (show 0<d+3 by omega)
      grind only
  rw [hd1] at h
  exact ⟨by omega,hd1,by omega⟩

private theorem primitive_difference (p u : List Bool) (i j : Nat)
    (hu : runKey u= -2) (hpu : runKey (p++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (p++u)+(j : Int)=1) :
    mass p= -((j : Int)-(i : Int)) ∧
      runKey p=4*((j : Int)-(i : Int))*(cntF u : Int) := by
  have hm : mass p= -((j : Int)-(i : Int)) := by
    rw [mass_append] at hmpu
    omega
  rw [runKey_append,hu,hm] at hpu
  simp only [Int.mul_neg,Int.neg_mul] at hpu
  exact ⟨hm,by omega⟩

/-- The quadratic factor at free two forces five additions, one clock
of advance, one future subtraction, and a segment of length eleven. -/
theorem free_two_unit_factor_band (f : Nat → Bool) (n K i j : Nat) (w u : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n K≤2) (hij : i<j)
    (hu : runKey u= -2) (hpu : runKey (seg f n K++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (seg f n K++u)+(j : Int)=1) :
    additions f n K=5 ∧ j=i+1 ∧ cntF u=1 ∧ K=11 ∧ runKey (seg f n K)=4 := by
  have hab:=positive_r3_additions_free_bound f n 0 K hw
    (by simpa only [List.replicate_zero,List.append_nil] using hpre) hp (show free f n K≤3 by omega)
  change additions f n K≤2*free f n K+1 at hab
  have hl:=(Recaman.MixedPrefixClockSquare.mixed_prefix_clock_square (seg f n K) u i j hij hu hpu hmu hmpu).1
  rw [ones_seg_eq_count] at hl
  change ((j-i : Nat) : Int)+2≤(additions f n K : Int) at hl
  have hB:=key_mass_rank_two f n K (by omega) hp hf
  obtain ⟨hm,hk⟩:=primitive_difference (seg f n K) u i j hu hpu hmu hmpu
  rw [hm,hk] at hB
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hu
  obtain ⟨h5,h1,hF⟩:=unit_factor (additions f n K : Int) ((j : Int)-(i : Int)) (cntF u : Int)
    (by omega) (by omega) (by omega) hB
  rw [h1,hF] at hk
  rw [h1] at hm
  have hc := cN_walk f n K
  rw [seg_mass] at hm
  change Fw f (n+K)=Fw f n+(additions f n K : Int)-(subtractions f n K : Int) ∧
    additions f n K+subtractions f n K=K at hc
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

end Recaman.ForwardSourceFreeTwoFactor
