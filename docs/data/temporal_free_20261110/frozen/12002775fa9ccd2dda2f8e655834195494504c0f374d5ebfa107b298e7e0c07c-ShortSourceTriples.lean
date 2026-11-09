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

/-- A supplied addition with the three-sign SAA window wholly in the interval. -/
def shortEndpoint (f : Nat → Bool) (n t : Nat) : Prop :=
  n+3≤t ∧ f (t-3)=false ∧ f (t-2)=true ∧ f (t-1)=true ∧ f t=true

theorem short_endpoint_supplied (f : Nat → Bool) (n t : Nat)
    (h : shortEndpoint f n t) : EndN f 0 t := by
  obtain ⟨ht,hS,h2,h1,hA⟩:=h
  have hF1 : Fw f (t-3+1)=Fw f (t-3)-1 := by
    rw [Fw_succ,hS]
    simp [Recaman.ShortPeriodicSupply.sign] <;> omega
  have hF2 : Fw f (t-3+2)=Fw f (t-3) := by
    rw [show t-3+2=(t-2)+1 by omega,Fw_succ,h2,
      show t-2=t-3+1 by omega,hF1]
    simp [Recaman.ShortPeriodicSupply.sign]
  have hF3 : Fw f (t-3+3)=Fw f (t-3)+1 := by
    rw [show t-3+3=(t-1)+1 by omega,Fw_succ,h1,
      show t-1=t-3+2 by omega,hF2]
    rfl
  refine ⟨hA,t-3,3,by omega,by omega,by decide,hF3,?_⟩
  rw [Ar3]
  omega

/-- Every short endpoint occupies three distinct A positions. This
bound holds for arbitrary original histories and arbitrary run counts. -/
theorem short_endpoints_triple_budget (f : Nat → Bool) (n K : Nat) :
    3*cN (shortEndpoint f n) n K≤additions f n K := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    cases K with
    | zero => simp [cN]
    | succ k =>
      let P:=shortEndpoint f n
      change 3*cN P n (k+1)≤additions f n (k+1)
      by_cases h : P (n+k)
      · have hmark:=h
        obtain ⟨ht,hS,h2,h1,hA⟩:=h
        have hk3 : 3≤k := by omega
        have hn2 : ¬P (n+(k-2)) := by
          intro hh
          have he : f (n+(k-2)-1)=true := hh.2.2.2.1
          rw [show n+(k-2)-1=n+k-3 by omega,hS] at he
          cases he
        have hn1 : ¬P (n+(k-1)) := by
          intro hh
          have he : f (n+(k-1)-2)=true := hh.2.2.1
          rw [show n+(k-1)-2=n+k-3 by omega,hS] at he
          cases he
        have hc2:=cN_succ_neg P n (k-2) hn2
        have hc1:=cN_succ_neg P n (k-1) hn1
        rw [show k-2+1=k-1 by omega] at hc2
        rw [show k-1+1=k by omega] at hc1
        have hA3:=A_triple_count f n (n+k) (by omega) hA h1 h2
        rw [show n+k-n+1=k+1 by omega,show n+k-2-n=k-2 by omega] at hA3
        have hprev:=ih (k-2) (by omega)
        change 3*cN P n (k-2)≤additions f n (k-2) at hprev
        rw [cN_succ_pos P n k hmark,hc1,hc2,hA3]
        omega
      · have hprev:=ih k (by omega)
        have ha : additions f n k≤additions f n (k+1) :=
          count_prefix_le (fun t=>f t=true) n k (k+1) (by omega)
        rw [cN_succ_neg P n k h]
        exact Nat.le_trans hprev ha

end Recaman.ShortSourceTriples
