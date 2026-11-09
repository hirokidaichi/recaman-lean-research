import Recaman.LowCrossOldClocks

namespace Recaman.LowCrossSegmentCuts

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.LeadingRunSupply
open Recaman.BlockSuffixPositivity Recaman.BlockOldRay Recaman.RunSupplyKeys
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem split_at_addition (f : Nat → Bool) (n K t : Nat)
    (hnt : n≤t) (ht : t<n+K) (ha : f t=true) :
    seg f n K=seg f n (t-n)++[true]++seg f (t+1) (n+K-(t+1)) := by
  have h:=seg_add f n (t-n+1) (n+K-(t+1))
  rw [show t-n+1+(n+K-(t+1))=K by omega,seg_succ,
    show n+(t-n)=t by omega,ha,show n+(t-n+1)=t+1 by omega] at h
  exact h

/-- The local clause retains the exact three signs immediately preceding
its endpoint in the original segment. -/
theorem low_cross_local_cut (f : Nat → Bool) (n K t : Nat)
    (hnt : n≤t) (ht : t<n+K) (ha : f t=true)
    (hQ : cross (seg f n K)≤20) (hmod : cross (seg f n K)%8=4)
    (hS : subtractions f n K=6)
    (hl : Recaman.ThreeNonsuppliedData.localSupply (seg f n (t-n))=true) :
    (subtractions f n (t-n)=5 ∨ subtractions f n (t-n)=6) ∧
    n+3≤t ∧ f (t-3)=false ∧ f (t-2)=true ∧ f (t-1)=true := by
  let x:=seg f n (t-n)
  let z:=seg f (t+1) (n+K-(t+1))
  have hs : seg f n K=x++[true]++z := split_at_addition f n K t hnt ht ha
  have hc : cntF (seg f n K)=6 := by rw [cntF_seg]; exact hS
  rw [hs,cntF_append,cntF_append,show cntF [true]=0 by decide,Nat.add_zero] at hc
  rw [hs] at hQ hmod
  obtain ⟨⟨v,hv⟩,hz⟩:=local_source_at_last_two_S x z hQ hmod hl
  have hx : cntF x=subtractions f n (t-n) := cntF_seg f n (t-n)
  have hlen : v.length+3=t-n := by
    have h:=congrArg List.length hv
    rw [show x.length=t-n from seg_length f n (t-n),List.length_append] at h
    simpa using h.symm
  have hcut:=seg_drop f n (t-n) v.length (by omega)
  change x.drop v.length=seg f (n+v.length) (t-n-v.length) at hcut
  rw [hv,List.drop_left,show n+v.length=t-3 by omega,show t-n-v.length=3 by omega] at hcut
  have h0:=seg_get f (t-3) 3 0 (by decide)
  have h1:=seg_get f (t-3) 3 1 (by decide)
  have h2:=seg_get f (t-3) 3 2 (by decide)
  rw [← hcut,show t-3+0=t-3 by omega] at h0
  rw [← hcut,show t-3+1=t-2 by omega] at h1
  rw [← hcut,show t-3+2=t-1 by omega] at h2
  exact ⟨by omega,by omega,(Option.some.inj h0).symm,(Option.some.inj h1).symm,(Option.some.inj h2).symm⟩

/-- The old clause at small cross has all six subtractions before it. -/
theorem low_cross_old_cut (f : Nat → Bool) (n K t : Nat) (w : List Bool)
    (hnt : n≤t) (ht : t<n+K) (ha : f t=true) (hw : BlockWord w)
    (hQ : cross (seg f n K)≤20) (hS : subtractions f n K=6)
    (ho : tailOldRay w (seg f n (t-n)) 0) : subtractions f n (t-n)=6 := by
  let x:=seg f n (t-n)
  let z:=seg f (t+1) (n+K-(t+1))
  have hs : seg f n K=x++[true]++z := split_at_addition f n K t hnt ht ha
  have hc : cntF (seg f n K)=6 := by rw [cntF_seg]; exact hS
  rw [hs,cntF_append,cntF_append,show cntF [true]=0 by decide,Nat.add_zero] at hc
  rw [hs] at hQ
  have hz:=Recaman.LowCrossOldClocks.low_cross_old_after_last_S w x z hw hc hQ ho
  have hx : cntF x=subtractions f n (t-n) := cntF_seg f n (t-n)
  omega

/-- Two different SAA endpoints cannot have the same subtraction rank. -/
theorem SAA_endpoints_rank_strict (f : Nat → Bool) (n a b : Nat) (hab : a<b)
    (ha : n+3≤a) (hb : n+3≤b)
    (ha2 : f (a-2)=true) (ha1 : f (a-1)=true) (hb3 : f (b-3)=false) :
    subtractions f n (a-n)<subtractions f n (b-n) := by
  have hba : a≤b-3 := by
    by_cases h : a≤b-3
    · exact h
    · have he : b-3=a-2 ∨ b-3=a-1 := by omega
      rcases he with he|he
      · rw [he,ha2] at hb3; cases hb3
      · rw [he,ha1] at hb3; cases hb3
  have h1 : subtractions f n (a-n)≤subtractions f n (b-3-n) :=
    count_prefix_le (fun x=>f x=false) n (a-n) (b-3-n) (by omega)
  have h2 : subtractions f n (b-3-n+1)=subtractions f n (b-3-n)+1 :=
    cN_succ_pos _ n (b-3-n) (by rw [show n+(b-3-n)=b-3 by omega]; exact hb3)
  have h3 : subtractions f n (b-3-n+1)≤subtractions f n (b-n) :=
    count_prefix_le (fun x=>f x=false) n (b-3-n+1) (b-n) (by omega)
  omega

end Recaman.LowCrossSegmentCuts
