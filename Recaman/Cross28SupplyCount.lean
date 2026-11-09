import Recaman.Cross28SourceCuts
import Recaman.LowCrossSupplyCount

namespace Recaman.Cross28SupplyCount

open Recaman.AdditionRankSlack Recaman.LowCrossLocalClocks Recaman.LowCrossSegmentCuts
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic Recaman.LowCrossSupplyCount

private def shortAt (f : Nat → Bool) (n r t : Nat) : Prop :=
  subtractions f n (t-n)=r ∧ n+3≤t ∧
    f (t-3)=false ∧ f (t-2)=true ∧ f (t-1)=true ∧ f t=true

private theorem short_unique (f : Nat → Bool) (n r a b : Nat)
    (ha : shortAt f n r a) (hb : shortAt f n r b) : a=b := by
  obtain ⟨hsa,ha3,haS,ha2,ha1,_⟩:=ha
  obtain ⟨hsb,hb3,hbS,hb2,hb1,_⟩:=hb
  by_cases hab : a<b
  · have hlt:=SAA_endpoints_rank_strict f n a b hab ha3 hb3 ha2 ha1 hbS
    omega
  · by_cases hba : b<a
    · have hlt:=SAA_endpoints_rank_strict f n b a hba hb3 ha3 hb2 hb1 haS
      omega
    · omega

/-- Seven AS pairs allow at most three original EndN suppliers.
The fourth sign separates the early and long local clauses. The old
clause and the final short local clause compete for eight additions. -/
theorem cross28_original_supply_three (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : subtractions f n K=6) (hA : additions f n K≤7)
    (hQ : cross (seg f n K)=28) :
    cN (EndN f 0) n K≤3 := by
  let P := fun t => (t=n+11 ∧ f (n+3)=true) ∨ (t=n+6 ∧ f (n+3)=false)
  let O := fun t => t=n+9 ∧ subtractions f n (t-n)=5 ∧ additions f n (t-n)=4 ∧ f t=true
  let Q := fun t => O t ∨ shortAt f n 6 t
  have hP : cN P n K≤1 := by
    apply interval_unique_count
    intro a b _ _ _ _ ha hb
    rcases ha with ⟨ha,hs⟩|⟨ha,hs⟩ <;> rcases hb with ⟨hb,ht⟩|⟨hb,ht⟩
    · omega
    · rw [hs] at ht; cases ht
    · rw [hs] at ht; cases ht
    · omega
  have hmix (a b : Nat) (hna : n≤a) (hb : b<n+K) (ho : O a)
      (hl : shortAt f n 6 b) : False := by
    obtain ⟨_,hS5,hA4,haa⟩:=ho
    obtain ⟨hS6,hb3,_,hb2,hb1,hab⟩:=hl
    exact Cross28SourceCuts.old_excludes_final_SAA f n K a b hna hb hb3 haa hab
      hA hA4 hS5 hS6 hb2 hb1
  have hQ1 : cN Q n K≤1 := by
    apply interval_unique_count
    intro a b hna ha hnb hb hQa hQb
    rcases hQa with hoa|hla <;> rcases hQb with hob|hlb
    · exact hoa.1.trans hob.1.symm
    · exact (hmix a b hna hb hoa hlb).elim
    · exact (hmix b a hnb ha hob hla).elim
    · exact short_unique f n 6 a b hla hlb
  have hL : cN (shortAt f n 5) n K≤1 := by
    apply interval_unique_count
    intro a b _ _ _ _ ha hb
    exact short_unique f n 5 a b ha hb
  have hcovered : cN (EndN f 0) n K≤cN (fun t=>P t ∨ (Q t ∨ shortAt f n 5 t)) n K := by
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
    · obtain ⟨ht9,hs5,ha4⟩:=Cross28SourceCuts.old_cut f n K t w hnt ht he.1 hw hQ hS ho
      exact Or.inr (Or.inl (Or.inl ⟨ht9,hs5,ha4,he.1⟩))
    · have hl' : Recaman.ThreeNonsuppliedData.localSupply x=true := by
        simpa only [List.replicate_zero,List.append_nil] using hl
      rcases Cross28SourceCuts.local_cut f n K t hnt ht he.1 hQ hS hl' with hLong|hShort
      · exact Or.inl (Or.inl hLong)
      · obtain ⟨hS4,hS6,h4,h3,hS',ha2,ha1⟩:=hShort
        have hCases : subtractions f n (t-n)=4 ∨ subtractions f n (t-n)=5 ∨
            subtractions f n (t-n)=6 := by omega
        rcases hCases with h|h|h
        · exact Or.inl (Or.inr (h4 h))
        · exact Or.inr (Or.inr ⟨h,h3,hS',ha2,ha1,he.1⟩)
        · exact Or.inr (Or.inl (Or.inr ⟨h,h3,hS',ha2,ha1,he.1⟩))
  have hu1:=interval_or_count P (fun t=>Q t ∨ shortAt f n 5 t) n K
  have hu2:=interval_or_count Q (shortAt f n 5) n K
  omega

end Recaman.Cross28SupplyCount
