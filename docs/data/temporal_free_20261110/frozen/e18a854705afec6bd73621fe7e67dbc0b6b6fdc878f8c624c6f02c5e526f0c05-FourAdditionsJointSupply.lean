import Recaman.SmallReverseSupplyCount

namespace Recaman.FourAdditionsJointSupply

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.LowCrossSegmentCuts
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic Recaman.LowCrossSupplyCount

private theorem rank_step (f : Nat → Bool) (n t : Nat) (hnt : n≤t) (hA : f t=true) :
    additions f n (t-n+1)=additions f n (t-n)+1 :=
  cN_succ_pos _ n (t-n) (by rw [show n+(t-n)=t by omega]; exact hA)

private theorem short_before_old_impossible (f : Nat → Bool) (n a b : Nat)
    (hna : n≤a) (hab : a<b) (ha : f a=true)
    (hA : additions f n (b-n)=3) (hQ : cross (seg f n (b-n))=4)
    (v : List Bool) (hShort : seg f n (a-n)=v++[false,true,true]) : False := by
  have hStep:=rank_step f n a hna ha
  have hM : additions f n (a-n+1)≤additions f n (b-n) :=
    count_prefix_le (fun t=>f t=true) n (a-n+1) (b-n) (by omega)
  have hOne : ones (seg f n (a-n))=(additions f n (a-n) : Int) :=
    ones_seg_eq_count f n (a-n)
  have hv0 : ones v=0 := by
    rw [hShort,ones_append,show ones [false,true,true]=2 by decide] at hOne
    have hv:=(ones_bounds v).1
    omega
  have hx : cross (seg f n (a-n))=0 := by
    rw [hShort,cross_append,cross_zero_of_no_A v hv0,hv0,
      show cross [false,true,true]=0 by decide]
    omega
  let z:=seg f (a+1) (b-(a+1))
  have hs : seg f n (b-n)=seg f n (a-n)++[true]++z := by
    have h:=split_at_addition f n (b-n) a hna (by omega) ha
    rw [show n+(b-n)=b by omega] at h
    exact h
  have hOne2 : ones (seg f n (a-n))=2 := by
    rw [hShort,ones_append,hv0]
    decide
  rw [hs,cross_at_addition,hx,hOne2] at hQ
  have hnon:=cross_nonnegative z
  have hz : cntF z=0 := by omega
  rw [cross_zero_of_no_S z hz,hz] at hQ
  omega

/-- With four additions, the original old fourth A and any short local
endpoint cannot occur at different positions. This bounds their union. -/
theorem original_four_additions_supply_one (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hA : additions f n K≤4)
    (hS : subtractions f n K≤4)
    (hQ : cross (seg f n K)=0 → subtractions f n K≤2) :
    cN (EndN f 0) n K≤1 := by
  have hOld (t : Nat) (hnt : n≤t) (ht : t<n+K) (hAt : f t=true)
      (ho : tailOldRay w (seg f n (t-n)) 0) :
      t=n+6 ∧ additions f n (t-n)=3 ∧ cross (seg f n (t-n))=4 := by
    let x:=seg f n (t-n)
    let z:=seg f (t+1) (n+K-(t+1))
    have hsplit : seg f n K=x++[true]++z := split_at_addition f n K t hnt ht hAt
    have hsf : cntF (seg f n K)=subtractions f n K := cntF_seg f n K
    rw [hsplit,cntF_append,cntF_append,show cntF [true]=0 by decide,Nat.add_zero] at hsf
    have hx:=Recaman.LowCrossOldClocks.old_source_small_S w x z hw (by omega)
      (fun hq=>by rw [hsplit] at hQ; have hl:=hQ hq; omega) ho
    obtain ⟨ha,hq⟩:=Recaman.LowCrossOldClocks.old_at_three_S_data w x hw hx ho
    have hlen:=cntF_int x
    have hlen' : x.length=t-n := seg_length f n (t-n)
    have hones : ones x=(additions f n (t-n) : Int) := ones_seg_eq_count f n (t-n)
    exact ⟨by omega,by omega,hq⟩
  have hLocal (t : Nat) (hnt : n≤t) (ht : t<n+K) (hAt : f t=true)
      (hl : Recaman.ThreeNonsuppliedData.localSupply (seg f n (t-n))=true) :
      ∃ v, seg f n (t-n)=v++[false,true,true] := by
    have ha:=rank_step f n t hnt hAt
    have hm : additions f n (t-n+1)≤additions f n K :=
      count_prefix_le (fun t=>f t=true) n (t-n+1) K (by omega)
    have hOne : ones (seg f n (t-n))=(additions f n (t-n) : Int) :=
      ones_seg_eq_count f n (t-n)
    exact local_source_three_prior_A _ (by omega) hl
  have hJoint (a b : Nat) (hna : n≤a) (ha : a<n+K) (hnb : n≤b) (hb : b<n+K)
      (hAa : f a=true) (hAb : f b=true)
      (hO : tailOldRay w (seg f n (a-n)) 0)
      (hL : Recaman.ThreeNonsuppliedData.localSupply (seg f n (b-n))=true) : a=b := by
    obtain ⟨_,hAo,hQo⟩:=hOld a hna ha hAa hO
    obtain ⟨v,hv⟩:=hLocal b hnb hb hAb hL
    by_cases h : b<a
    · exact (short_before_old_impossible f n b a hnb h hAb hAo hQo v hv).elim
    · by_cases h' : a<b
      · have ha' := rank_step f n a hna hAa
        have hb' := rank_step f n b hnb hAb
        have hM : additions f n (a-n+1)≤additions f n (b-n) :=
          count_prefix_le (fun t=>f t=true) n (a-n+1) (b-n) (by omega)
        have ht : additions f n (b-n+1)≤additions f n K :=
          count_prefix_le (fun t=>f t=true) n (b-n+1) K (by omega)
        omega
      · omega
  apply interval_unique_count
  intro a b hna ha hnb hb hea heb
  rcases SmallReverseSupplyCount.original_end_source f n a w hna hpre hea with hoa|hla <;>
    rcases SmallReverseSupplyCount.original_end_source f n b w hnb hpre heb with hob|hlb
  · exact (hOld a hna ha hea.1 hoa).1.trans (hOld b hnb hb heb.1 hob).1.symm
  · exact hJoint a b hna ha hnb hb hea.1 heb.1 hoa hlb
  · exact (hJoint b a hnb hb hna ha heb.1 hea.1 hob hla).symm
  · obtain ⟨v,hv⟩:=hLocal a hna ha hea.1 hla
    obtain ⟨u,hu⟩:=hLocal b hnb hb heb.1 hlb
    obtain ⟨ha3,has,ha2,ha1⟩:=ShortSourceTriples.SAA_suffix_signs f n a hna v hv
    obtain ⟨hb3,hbs,hb2,hb1⟩:=ShortSourceTriples.SAA_suffix_signs f n b hnb u hu
    by_cases h : a<b
    · have h6:=ShortSourceTriples.two_short_endpoints_six_additions f n K a b
        ha3 h hb hea.1 ha1 ha2 heb.1 hb1 hb2 hbs
      omega
    · by_cases h' : b<a
      · have h6:=ShortSourceTriples.two_short_endpoints_six_additions f n K b a
          hb3 h' ha heb.1 hb1 hb2 hea.1 ha1 ha2 has
        omega
      · omega

end Recaman.FourAdditionsJointSupply
