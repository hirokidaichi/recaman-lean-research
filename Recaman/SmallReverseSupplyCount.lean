import Recaman.ShortSourceTriples

namespace Recaman.SmallReverseSupplyCount

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.LowCrossSegmentCuts
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic Recaman.LowCrossSupplyCount

theorem original_end_source (f : Nat → Bool) (n t : Nat) (w : List Bool)
    (hnt : n≤t) (hpre : seg f 0 n=w) (he : EndN f 0 t) :
    tailOldRay w (seg f n (t-n)) 0 ∨
      Recaman.ThreeNonsuppliedData.localSupply (seg f n (t-n))=true := by
  let x:=seg f n (t-n)
  have hwhole : seg f 0 t=w++x := by
    have h:=seg_add f 0 n (t-n)
    rwa [Nat.zero_add,hpre,show n+(t-n)=t by omega] at h
  have h:= (localSupply_seg_iff f 0 t (Nat.zero_le _) he.1).mpr he
  have hh : Recaman.ThreeNonsuppliedData.localSupply ((w++x)++List.replicate 0 true)=true := by
    simpa only [Nat.sub_zero,hwhole,List.replicate_zero,List.append_nil] using h
  simpa only [List.replicate_zero,List.append_nil] using (ray_supply_append_iff w x 0).mp hh

/-- In the low-cross bands with at most five A signs, local SAA sources
cost disjoint triples and every old supplier lies at the same S rank. -/
theorem small_reverse_supply_bounds (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hA : additions f n K≤5) (hS : subtractions f n K≤4)
    (hQ : cross (seg f n K)≤28) (h16 : cross (seg f n K)≠16)
    (hQ0 : cross (seg f n K)=0 → subtractions f n K≤2) :
    cN (EndN f 0) n K≤2 ∧
      (subtractions f n K≤2 → cN (EndN f 0) n K≤1) ∧
      (subtractions f n K≤2 → additions f n K≤3 → cross (seg f n K)=4 →
        cN (EndN f 0) n K=0) := by
  let O := fun t => f t=true ∧ tailOldRay w (seg f n (t-n)) 0
  let L := fun t => f t=true ∧ Recaman.ThreeNonsuppliedData.localSupply (seg f n (t-n))=true
  have hold (t : Nat) (hnt : n≤t) (ht : t<n+K) (ho : O t) :
      subtractions f n (t-n)=3 := by
    let x:=seg f n (t-n)
    let z:=seg f (t+1) (n+K-(t+1))
    have hsplit : seg f n K=x++[true]++z := split_at_addition f n K t hnt ht ho.1
    have hsf : cntF (seg f n K)=subtractions f n K := cntF_seg f n K
    rw [hsplit,cntF_append,cntF_append,show cntF [true]=0 by decide,Nat.add_zero] at hsf
    have h:=Recaman.LowCrossOldClocks.old_source_small_S w x z hw (by omega)
      (fun hq=>by rw [hsplit] at hQ0; have hl:=hQ0 hq; omega) ho.2
    have hx : cntF x=subtractions f n (t-n) := cntF_seg f n (t-n)
    omega
  have hlocal (t : Nat) (hnt : n≤t) (ht : t<n+K) (hl : L t) :
      (n+3≤t ∧ f (t-3)=false ∧ f (t-2)=true ∧ f (t-1)=true) ∧
        (additions f n K≤3 → cross (seg f n K)≠4) := by
    let x:=seg f n (t-n)
    let z:=seg f (t+1) (n+K-(t+1))
    have hsplit : seg f n K=x++[true]++z := split_at_addition f n K t hnt ht hl.1
    have hAc : ones (seg f n K)=(additions f n K : Int) := ones_seg_eq_count f n K
    rw [hsplit] at hAc hQ h16
    obtain ⟨v,hv⟩:=local_source_small_A x z (by omega) hQ h16 hl.2
    refine ⟨ShortSourceTriples.SAA_suffix_signs f n t hnt v hv,?_⟩
    intro h3 h4
    rw [hsplit,hv] at h4
    rw [hv] at hAc
    have h12:=three_A_short_source_cross v z (by omega)
    omega
  have hO : cN O n K≤1 := by
    apply interval_unique_count
    intro a b hna ha hnb hb hoa hob
    have hsa:=hold a hna ha hoa
    have hsb:=hold b hnb hb hob
    by_cases h : a≤b
    · exact old_same_rank_unique f n a b w hw hna h (by omega) (by omega) hoa.2 hob.2
    · exact (old_same_rank_unique f n b a w hw hnb (by omega) (by omega) (by omega) hob.2 hoa.2).symm
  have hO0 (h2 : subtractions f n K≤2) : cN O n K=0 := by
    apply cN_zero_of
    intro t hnt ht he
    have hs:=hold t hnt ht he
    have hm : subtractions f n (t-n)≤subtractions f n K :=
      count_prefix_le (fun t=>f t=false) n (t-n) K (by omega)
    omega
  have hL : cN L n K≤1 := by
    apply interval_unique_count
    intro a b hna ha hnb hb hla hlb
    obtain ⟨⟨ha3,has,ha2,ha1⟩,_⟩:=hlocal a hna ha hla
    obtain ⟨⟨hb3,hbs,hb2,hb1⟩,_⟩:=hlocal b hnb hb hlb
    by_cases h : a<b
    · have hh:=ShortSourceTriples.two_short_endpoints_six_additions f n K a b
        ha3 h hb hla.1 ha1 ha2 hlb.1 hb1 hb2 hbs
      omega
    · by_cases h' : b<a
      · have hh:=ShortSourceTriples.two_short_endpoints_six_additions f n K b a
          hb3 h' ha hlb.1 hb1 hb2 hla.1 ha1 ha2 has
        omega
      · omega
  have hL0 (h3 : additions f n K≤3) (h4 : cross (seg f n K)=4) : cN L n K=0 := by
    apply cN_zero_of
    intro t hnt ht he
    exact (hlocal t hnt ht he).2 h3 h4
  have hCover : cN (EndN f 0) n K≤cN O n K+cN L n K := by
    apply Nat.le_trans _ (interval_or_count O L n K)
    apply cN_mono
    intro t hnt ht he
    rcases original_end_source f n t w hnt hpre he with ho|hl
    · exact Or.inl ⟨he.1,ho⟩
    · exact Or.inr ⟨he.1,hl⟩
  refine ⟨by omega,?_⟩
  refine ⟨fun h=>by have ho:=hO0 h; omega,?_⟩
  intro h2 h3 h4
  have ho:=hO0 h2
  have hl:=hL0 h3 h4
  omega

end Recaman.SmallReverseSupplyCount
