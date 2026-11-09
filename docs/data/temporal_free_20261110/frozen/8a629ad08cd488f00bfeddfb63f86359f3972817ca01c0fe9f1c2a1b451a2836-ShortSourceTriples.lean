import Recaman.LowCrossSupplyCount

namespace Recaman.ShortSourceTriples

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.LowCrossSegmentCuts
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem SAA_suffix_signs (f : Nat → Bool) (n t : Nat) (hnt : n≤t) (v : List Bool)
    (hv : seg f n (t-n)=v++[false,true,true]) :
    n+3≤t ∧ f (t-3)=false ∧ f (t-2)=true ∧ f (t-1)=true := by
  have hlen : v.length+3=t-n := by
    have h:=congrArg List.length hv
    rw [seg_length,List.length_append] at h
    simpa using h.symm
  have hcut:=seg_drop f n (t-n) v.length (by omega)
  rw [hv,List.drop_left,show n+v.length=t-3 by omega,show t-n-v.length=3 by omega] at hcut
  have h0:=seg_get f (t-3) 3 0 (by decide)
  have h1:=seg_get f (t-3) 3 1 (by decide)
  have h2:=seg_get f (t-3) 3 2 (by decide)
  rw [← hcut,show t-3+0=t-3 by omega] at h0
  rw [← hcut,show t-3+1=t-2 by omega] at h1
  rw [← hcut,show t-3+2=t-1 by omega] at h2
  exact ⟨by omega,(Option.some.inj h0).symm,(Option.some.inj h1).symm,(Option.some.inj h2).symm⟩

private theorem A_triple_count (f : Nat → Bool) (n t : Nat) (h : n+2≤t)
    (h0 : f t=true) (h1 : f (t-1)=true) (h2 : f (t-2)=true) :
    additions f n (t-n+1)=additions f n (t-2-n)+3 := by
  have hA (i : Nat) (hi : i<3) : f (t-2+i)=true := by
    have hs : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hs with rfl|rfl|rfl
    · simpa only [Nat.add_zero] using h2
    · rwa [show t-2+1=t-1 by omega]
    · rwa [show t-2+2=t by omega]
  have h3:=count_A_run f (t-2) 3 hA
  have hcount:=cN_add (fun t=>f t=true) n (t-2-n) 3
  rw [show t-2-n+3=t-n+1 by omega,show n+(t-2-n)=t-2 by omega,h3] at hcount
  exact hcount

/-- Different SAA suppliers followed by their actual A endpoints
consume disjoint triples of additions. -/
theorem two_short_endpoints_six_additions (f : Nat → Bool) (n K a b : Nat)
    (ha3 : n+3≤a) (hab : a<b) (hb : b<n+K)
    (ha : f a=true) (ha1 : f (a-1)=true) (ha2 : f (a-2)=true)
    (hb0 : f b=true) (hb1 : f (b-1)=true) (hb2 : f (b-2)=true) (hb3 : f (b-3)=false) :
    6≤additions f n K := by
  have hGap : a+1≤b-2 := by
    by_cases h : a+1≤b-2
    · exact h
    · have hs : b-3=a-2 ∨ b-3=a-1 ∨ b-3=a := by omega
      rcases hs with hs|hs|hs
      · rw [hs,ha2] at hb3; cases hb3
      · rw [hs,ha1] at hb3; cases hb3
      · rw [hs,ha] at hb3; cases hb3
  have haC:=A_triple_count f n a (by omega) ha ha1 ha2
  have hbC:=A_triple_count f n b (by omega) hb0 hb1 hb2
  have hmid : additions f n (a-n+1)≤additions f n (b-2-n) :=
    count_prefix_le (fun t=>f t=true) n (a-n+1) (b-2-n) (by omega)
  have htot : additions f n (b-n+1)≤additions f n K :=
    count_prefix_le (fun t=>f t=true) n (b-n+1) K (by omega)
  omega

end Recaman.ShortSourceTriples
