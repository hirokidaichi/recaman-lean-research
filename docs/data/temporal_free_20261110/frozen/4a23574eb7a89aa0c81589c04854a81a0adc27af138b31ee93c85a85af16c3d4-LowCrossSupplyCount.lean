import Recaman.LowCrossSegmentCuts

namespace Recaman.LowCrossSupplyCount

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.LowCrossSegmentCuts
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem shift_count (P : Nat → Prop) (n K : Nat) :
    cN P n K=cN (fun i=>P (n+i)) 0 K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    by_cases h : P (n+K)
    · rw [cN_succ_pos P n K h,cN_succ_pos (fun i=>P (n+i)) 0 K
        (by simpa only [Nat.zero_add] using h),ih]
    · rw [cN_succ_neg P n K h,cN_succ_neg (fun i=>P (n+i)) 0 K
        (by simpa only [Nat.zero_add] using h),ih]

theorem interval_unique_count (P : Nat → Prop) (n K : Nat)
    (h : ∀ a b, n≤a → a<n+K → n≤b → b<n+K → P a → P b → a=b) : cN P n K≤1 := by
  rw [shift_count]
  apply cN_le_one_of_unique
  intro i hi j hj hpi hpj
  have hEq:=h (n+i) (n+j) (by omega) (by omega) (by omega) (by omega) hpi hpj
  omega

theorem interval_or_count (P Q : Nat → Prop) (n K : Nat) :
    cN (fun t=>P t ∨ Q t) n K≤cN P n K+cN Q n K := by
  rw [shift_count (fun t=>P t ∨ Q t) n K,shift_count P n K,shift_count Q n K]
  exact cN_or_le (fun t=>P (n+t)) (fun t=>Q (n+t)) K

/-- If two old endpoints have the same S count, they use the same
mixed prefix and two clocks of its A-ray. -/
theorem old_same_rank_unique (f : Nat → Bool) (n a b : Nat) (w : List Bool)
    (hw : BlockWord w) (hna : n≤a) (hab : a≤b)
    (hS : 3≤subtractions f n (a-n))
    (heq : subtractions f n (a-n)=subtractions f n (b-n))
    (hoA : tailOldRay w (seg f n (a-n)) 0)
    (hoB : tailOldRay w (seg f n (b-n)) 0) : a=b := by
  have hcount:=cN_add (fun x=>f x=false) n (a-n) (b-a)
  rw [show a-n+(b-a)=b-n by omega,show n+(a-n)=a by omega] at hcount
  change subtractions f n (b-n)=subtractions f n (a-n)+cN (fun x=>f x=false) a (b-a) at hcount
  have hz : cN (fun x=>f x=false) a (b-a)=0 := by omega
  have hseg : seg f a (b-a)=List.replicate (b-a) true := by
    apply seg_A
    intro t ha ht
    have hn:=not_of_cN_zero (P := fun x=>f x=false) (s := a) (b-a) hz t ha ht
    cases h : f t with
    | false => exact False.elim (hn h)
    | true => rfl
  have hfull:=seg_add f n (a-n) (b-a)
  rw [show a-n+(b-a)=b-n by omega,show n+(a-n)=a by omega,hseg] at hfull
  obtain ⟨t,ht,hm,hk⟩:=hoB
  rw [hfull,mass_append,mass_replicate_A] at hm
  rw [hfull,runKey_append_A,cntF_append,Recaman.UnitTargetSASProfile.cntF_A,Nat.add_zero] at hk
  have hlater : tailOldRay w (seg f n (a-n)) (b-a) := ⟨t,ht,by omega,hk⟩
  have hf : 3≤cntF (seg f n (a-n)) := by rw [cntF_seg]; exact hS
  have h0:=tailOldRay_clock_unique hw (seg f n (a-n)) hf 0 (b-a) hoA hlater
  omega

private theorem local_same_rank_unique (f : Nat → Bool) (n K a b : Nat)
    (hna : n≤a) (ha : a<n+K) (hnb : n≤b) (hb : b<n+K)
    (hAa : f a=true) (hAb : f b=true)
    (hQ : cross (seg f n K)≤20) (hmod : cross (seg f n K)%8=4)
    (hS : subtractions f n K=6)
    (hla : Recaman.ThreeNonsuppliedData.localSupply (seg f n (a-n))=true)
    (hlb : Recaman.ThreeNonsuppliedData.localSupply (seg f n (b-n))=true)
    (heq : subtractions f n (a-n)=subtractions f n (b-n)) : a=b := by
  obtain ⟨_,ha3,hsa,ha2,ha1⟩:=low_cross_local_cut f n K a hna ha hAa hQ hmod hS hla
  obtain ⟨_,hb3,hsb,hb2,hb1⟩:=low_cross_local_cut f n K b hnb hb hAb hQ hmod hS hlb
  by_cases hab : a<b
  · have hlt:=SAA_endpoints_rank_strict f n a b hab ha3 hb3 ha2 ha1 hsb
    omega
  · by_cases hba : b<a
    · have hlt:=SAA_endpoints_rank_strict f n b a hba hb3 ha3 hb2 hb1 hsa
      omega
    · omega

/-- At low odd cross, the same original history has at most two local
and one old supplied additions in the interval. -/
theorem low_cross_original_supply_three (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hS : subtractions f n K=6)
    (hQ : cross (seg f n K)≤20) (hmod : cross (seg f n K)%8=4) :
    cN (EndN f 0) n K≤3 := by
  let O := fun t => f t=true ∧ tailOldRay w (seg f n (t-n)) 0
  let L := fun r t => f t=true ∧
    Recaman.ThreeNonsuppliedData.localSupply (seg f n (t-n))=true ∧ subtractions f n (t-n)=r
  have hO : cN O n K≤1 := by
    apply interval_unique_count
    intro a b hna ha hnb hb hoa hob
    have hA:=low_cross_old_cut f n K a w hna ha hoa.1 hw hQ hS hoa.2
    have hB:=low_cross_old_cut f n K b w hnb hb hob.1 hw hQ hS hob.2
    by_cases h : a≤b
    · exact old_same_rank_unique f n a b w hw hna h (by omega) (by omega) hoa.2 hob.2
    · exact (old_same_rank_unique f n b a w hw hnb (by omega) (by omega) (by omega) hob.2 hoa.2).symm
  have hL (r : Nat) : cN (L r) n K≤1 := by
    apply interval_unique_count
    intro a b hna ha hnb hb hla hlb
    exact local_same_rank_unique f n K a b hna ha hnb hb hla.1 hlb.1 hQ hmod hS hla.2.1 hlb.2.1
      (hla.2.2.trans hlb.2.2.symm)
  have hcovered : cN (EndN f 0) n K≤cN (fun t=>O t ∨ (L 5 t ∨ L 6 t)) n K := by
    apply cN_mono
    intro t hnt ht he
    let x:=seg f n (t-n)
    have hwhole : seg f 0 t=w++x := by
      have h:=seg_add f 0 n (t-n)
      rwa [Nat.zero_add,hpre,show n+(t-n)=t by omega] at h
    have hh:= (localSupply_seg_iff f 0 t (Nat.zero_le _) he.1).mpr he
    have hh' : Recaman.ThreeNonsuppliedData.localSupply ((w++x)++List.replicate 0 true)=true := by
      simpa only [Nat.sub_zero,hwhole,List.replicate_zero,List.append_nil] using hh
    rcases (ray_supply_append_iff w x 0).mp hh' with ho|hl
    · exact Or.inl ⟨he.1,ho⟩
    · have hl' : Recaman.ThreeNonsuppliedData.localSupply (seg f n (t-n))=true := by
        simpa only [List.replicate_zero,List.append_nil] using hl
      have hs:=(low_cross_local_cut f n K t hnt ht he.1 hQ hmod hS hl').1
      rcases hs with h5|h6
      · exact Or.inr (Or.inl ⟨he.1,hl',h5⟩)
      · exact Or.inr (Or.inr ⟨he.1,hl',h6⟩)
  have hu1:=interval_or_count O (fun t=>L 5 t ∨ L 6 t) n K
  have hu2:=interval_or_count (L 5) (L 6) n K
  have h5:=hL 5
  have h6:=hL 6
  omega

/-- Even cross allows a local source containing three S signs. -/
theorem even_cross_local_control :
    let x:=[false,false,true,true,true,true,false]
    cross (x++[true])=16 ∧ Recaman.ThreeNonsuppliedData.localSupply x=true ∧
      x.drop 4≠[false,true,true] := by decide

end Recaman.LowCrossSupplyCount
