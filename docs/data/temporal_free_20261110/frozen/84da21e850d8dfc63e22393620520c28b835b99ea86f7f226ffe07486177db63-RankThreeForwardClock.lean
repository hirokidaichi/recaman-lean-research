import Recaman.RankThreeEarlyFree

namespace Recaman.RankThreeForwardClock

open Recaman.AdditionRankSlack Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.PrefixMassBarrier Recaman.BlockOldRay Recaman.RunSupplyKeys
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem rank_three_identity (a s q : Int) :
    q+2*(a-s)^2+(4*a*s-2*s^2-q-(4*a+2*(a-3)*(a-3+1)))=6*a-12 := by grind only

/-- The area available to the key and squared mass at free rank three. -/
theorem rank_three_key_mass (f : Nat → Bool) (n K : Nat) (ha : 3≤additions f n K) :
    runKey (seg f n K)+2*(mass (seg f n K))^2+rankSlack f n 3 K=
      6*(additions f n K : Int)-12 := by
  let a:=additions f n K
  let s:=subtractions f n K
  have hA : 3≤a := ha
  have hcast : (((a-3 : Nat) : Int))=(a : Int)-3 := by omega
  have hm:=seg_mass f n K
  have hw:=(cN_walk f n K).1
  change Fw f (n+K)=Fw f n+(a : Int)-(s : Int) at hw
  have hM : mass (seg f n K)=(a : Int)-(s : Int) := by omega
  unfold rankSlack
  change runKey (seg f n K)+2*(mass (seg f n K))^2+
    (4*(a : Int)*(s : Int)-2*(s : Int)^2-runKey (seg f n K)-rankCost 3 a)=6*(a : Int)-12
  unfold rankCost
  rw [hM,hcast]
  exact rank_three_identity (a : Int) (s : Int) (runKey (seg f n K))

private theorem small_band (a d F : Int)
    (ha : 3≤a) (hA : a≤7) (hd : 1≤d) (hF : 1≤F)
    (hpar : (a+d)%2=0) (hodd : F%2=1)
    (hb : 4*d*F+2*d^2≤6*a-16) (hlarge : 5≤a → 4*d*F+2*d^2≤6*a-24) :
    d=1 ∧ (a=5 ∧ F=1 ∨ a=7 ∧ (F=1 ∨ F=3)) := by
  have hFD:=Int.mul_nonneg (show 0≤d by omega) (show 0≤F-1 by omega)
  have he (b : Int) (hb1 : 1≤b) (hbd : b≤d) :
      2*b^2+4*b≤4*d*F+2*d^2 := by
    have hP:=Int.mul_nonneg (show 0≤d-b by omega) (show 0≤d+b+2 by omega)
    grind only
  have h5 : 5≤a := by
    by_cases h : 5≤a
    · exact h
    · by_cases hd1 : d=1
      · have h3 : a=3 := by omega
        have h1:=he 1 (by decide) hd
        rw [h3] at hb
        omega
      · have h2:=he 2 (by decide) (by omega)
        omega
  have hcap:=hlarge h5
  have hd1 : d=1 := by
    by_cases h3 : 3≤d
    · have h:=he 3 (by decide) h3
      omega
    · by_cases h2 : d=2
      · have h6 : a=6 := by omega
        have h:=he 2 (by decide) (by omega)
        rw [h6] at hcap
        omega
      · omega
  refine ⟨hd1,?_⟩
  rw [hd1] at hcap
  omega

private theorem key_difference_data (p u : List Bool) (i j : Nat)
    (hu : runKey u= -2) (hpu : runKey (p++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (p++u)+(j : Int)=1) :
    mass p= -((j : Int)-(i : Int)) ∧
    runKey p=4*((j : Int)-(i : Int))*(cntF u : Int) ∧ (cntF p : Int)%2=0 := by
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hu
  have hodd':=Recaman.MixedASQuarterBudget.source_subtraction_odd (p++u) hpu
  rw [cntF_append,Int.natCast_add] at hodd'
  have hpar : (cntF p : Int)%2=0 := by omega
  have hm : mass p= -((j : Int)-(i : Int)) := by rw [mass_append] at hmpu; omega
  rw [runKey_append,hu,hm] at hpu
  simp only [Int.mul_neg,Int.neg_mul] at hpu
  exact ⟨hm,by omega,hpar⟩

private theorem mass_additions_subtractions (f : Nat → Bool) (n K : Nat) :
    mass (seg f n K)=(additions f n K : Int)-(subtractions f n K : Int) := by
  have h:=seg_mass f n K
  have hs:=(cN_walk f n K).1
  unfold additions subtractions
  omega

/-- Forward primitive clocks at original free rank at most three differ
by one and end by clock three. No bound on the old word is assumed. -/
theorem rank_three_forward_clock_band (f : Nat → Bool) (n K i j : Nat) (w u : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n K≤3) (hij : i<j)
    (hu : runKey u= -2) (hpu : runKey (seg f n K++u)= -2)
    (hmu : mass u+(i : Int)=1) (hmpu : mass (seg f n K++u)+(j : Int)=1) :
    j=i+1 ∧ i≤2 ∧ j≤3 ∧
    (additions f n K=5 ∧ cntF u=1 ∨ additions f n K=7 ∧ (cntF u=1 ∨ cntF u=3)) := by
  let a:=additions f n K
  let d:=(j : Int)-(i : Int)
  have hab:=positive_r3_additions_free_bound f n 0 K hw
    (by simpa only [List.replicate_zero,List.append_nil] using hpre) hp hf
  change a≤2*free f n K+1 at hab
  have hlo:=(Recaman.MixedPrefixClockSquare.mixed_prefix_clock_square
    (seg f n K) u i j hij hu hpu hmu hmpu).1
  rw [ones_seg_eq_count] at hlo
  change ((j-i : Nat) : Int)+2≤(a : Int) at hlo
  have ha3 : 3≤a := by omega
  obtain ⟨hm,hk,hpar⟩:=key_difference_data (seg f n K) u i j hu hpu hmu hmpu
  change mass (seg f n K)= -d at hm
  change runKey (seg f n K)=4*d*(cntF u : Int) at hk
  rw [cntF_seg] at hpar
  change (subtractions f n K : Int)%2=0 at hpar
  have hmas:=mass_additions_subtractions f n K
  have hpar' : ((a : Int)+d)%2=0 := by omega
  have hb:=rank_three_key_mass f n K ha3
  rw [hm,hk] at hb
  have hsq : (-d)^2=d^2 := by grind only
  rw [hsq] at hb
  change 4*d*(cntF u : Int)+2*d^2+rankSlack f n 3 K=6*(a : Int)-12 at hb
  have hbonus:=Recaman.InitialRankBonus.initial_two_subtraction_bonus f n 3 K hp hf
  have hsl : 4≤rankSlack f n 3 K := by
    change 4*((min (a-2) 1 : Nat) : Int)≤rankSlack f n 3 K at hbonus
    rw [Nat.min_eq_right (by omega)] at hbonus
    exact hbonus
  have hbig : 5≤(a : Int) → 4*d*(cntF u : Int)+2*d^2≤6*(a : Int)-24 := by
    intro ha5
    have hs:=Recaman.RankThreeEarlyFree.rank_three_slack_at_five f n K w hw hpre hp hf (by omega)
    omega
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hu
  obtain ⟨hd,hband⟩:=small_band (a : Int) d (cntF u : Int)
    (by omega) (by omega) (by dsimp [d]; omega) (by omega) hpar' hodd (by omega) hbig
  have hi : i≤2 := by
    by_cases hF : cntF u=1
    · have hc:=cntF_int u
      have hmass:=mass_eq u
      have hn:=(ones_bounds u).1
      omega
    · have hF3 : cntF u=3 := by omega
      have hs:=Recaman.PrimitiveClockRadius.primitive_clock_half_S u i (by omega) hu hmu
      omega
  have hj : j=i+1 := by dsimp [d] at hd; omega
  exact ⟨hj,hi,by omega,by omega⟩

end Recaman.RankThreeForwardClock
