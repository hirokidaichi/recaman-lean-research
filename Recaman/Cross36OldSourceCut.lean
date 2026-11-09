import Recaman.LowCrossSupplyCount

namespace Recaman.Cross36OldSourceCut

open Recaman.LowCrossLocalClocks Recaman.LowCrossOldClocks
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction

/-- Nine AS pairs and six S signs leave two possible old-source ranks.
The old word and all its suffix lengths remain unrestricted. -/
theorem old_cross36_cut (w x z : List Bool) (hw : BlockWord w)
    (hS : cntF x+cntF z=6) (hQ : cross (x++[true]++z)=36)
    (ho : tailOldRay w x 0) :
    (cntF x=4 ∧ ones x=3 ∧ cross x=0) ∨
      (cntF x=5 ∧ ones x=4 ∧ 8≤cross x ∧ cross x≤10) := by
  have hlow:=runKey_count_lower x
  have hp : 1≤cntF x := by
    by_cases h : 1≤cntF x
    · exact h
    · have h0 : cntF x=0 := by omega
      rw [h0] at hlow
      exact (Recaman.NonnegativeFutureOldSource.no_old_source w x hw (by omega) 0 ho).elim
  have hQx:=cross_nonnegative x
  have hQz:=cross_nonnegative z
  obtain ⟨hn,he⟩:=Recaman.OldSourceNegativeThreshold.old_source_key_threshold w x 0 hw hp ho
  obtain ⟨hC,hk,h1,h2⟩:=gate_constraints x 0
    (Recaman.OldMassEndpointGate.old_source_passes_mass_gate w x 0 hw ho)
  let c:=1-mass x
  let k:=runKey x+4*c*(cntF x : Int)
  change 1≤1-mass x-(0 : Int) at hC
  have hc : 1≤c := by dsimp [c]; omega
  have hk' : k≤0 := by dsimp [k,c]; simpa using hk
  have h1' : c=1 → k= -2 := by dsimp [k,c]; simpa using h1
  have h2' : c=2 → k= -2 ∨ k=0 := by dsimp [k,c]; simpa using h2
  have hmass:=mass_eq x
  have hcnt:=cntF_int x
  have hca : c=1-ones x+(cntF x : Int) := by dsimp [c]; omega
  have hkey : k=cross x-2*(cntF x : Int)^2+4*c*(cntF x : Int) := by
    unfold cross
    dsimp [k]
    omega
  rw [cross_at_addition] at hQ
  have hcases : cntF x=1 ∨ cntF x=2 ∨ cntF x=3 ∨ cntF x=4 ∨ cntF x=5 ∨ cntF x=6 := by omega
  rcases hcases with hs|hs|hs|hs|hs|hs
  · rw [hs] at hlow hn
    omega
  · have hu:=he (by rw [hs] <;> decide)
    rw [hs] at hlow hu
    omega
  · obtain ⟨ha,hq⟩:=old_at_three_S_data w x hw hs ho
    rw [ha,hq,show cntF z=3 by omega] at hQ
    omega
  · have hu:=he (by rw [hs] <;> decide)
    have hq : cross x=0 := by unfold cross; rw [hs] at hlow hu ⊢; omega
    rw [hs,hq] at hkey
    have hc2 : c=2 := by
      by_cases h : c=1
      · have hu:=h1' h
        omega
      · omega
    rw [hs] at hca
    exact Or.inl ⟨hs,by omega,hq⟩
  · rw [hs] at hca hkey
    rw [show cntF z=1 by omega] at hQ
    have hc2 : c=2 := by
      by_cases h : c=1
      · have hu:=h1' h
        omega
      · omega
    have hu:=h2' hc2
    exact Or.inr ⟨hs,by omega,by omega,by omega⟩
  · have hz : cntF z=0 := by omega
    rw [cross_zero_of_no_S z hz,hz] at hQ
    rw [hs] at hkey
    by_cases h : c=1
    · have hu:=h1' h
      omega
    · omega

open Recaman.AdditionRankSlack Recaman.LowCrossSegmentCuts Recaman.LowCrossSupplyCount
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem actual_old_ranks (f : Nat → Bool) (n K t : Nat) (w : List Bool)
    (hw : BlockWord w) (hnt : n≤t) (ht : t<n+K) (hAt : f t=true)
    (hS : subtractions f n K=6) (hQ : cross (seg f n K)=36)
    (ho : tailOldRay w (seg f n (t-n)) 0) :
    let x:=seg f n (t-n)
    (t=n+7 ∧ cntF x=4 ∧ ones x=3 ∧ cross x=0) ∨
      (t=n+9 ∧ cntF x=5 ∧ ones x=4 ∧ cross x≤10) := by
  let x:=seg f n (t-n)
  let z:=seg f (t+1) (n+K-(t+1))
  have hs : seg f n K=x++[true]++z := split_at_addition f n K t hnt ht hAt
  have hc : cntF (seg f n K)=6 := by rw [cntF_seg]; exact hS
  rw [hs,cntF_append,cntF_append,show cntF [true]=0 by decide,Nat.add_zero] at hc
  rw [hs] at hQ
  have hLen:=cntF_int x
  have hLen' : x.length=t-n := seg_length f n (t-n)
  rcases old_cross36_cut w x z hw hc hQ ho with ⟨hs,ha,hq⟩|⟨hs,ha,_,hq⟩
  · exact Or.inl ⟨by omega,hs,ha,hq⟩
  · exact Or.inr ⟨by omega,hs,ha,hq⟩

private theorem old_ranks_conflict (f : Nat → Bool) (n a b : Nat)
    (hna : n≤a) (hab : a<b) (hAa : f a=true)
    (hSa : cntF (seg f n (a-n))=4) (hAb : ones (seg f n (a-n))=3)
    (hSb : cntF (seg f n (b-n))=5) (hQb : cross (seg f n (b-n))≤10) : False := by
  let x:=seg f n (a-n)
  let z:=seg f (a+1) (b-(a+1))
  have hs : seg f n (b-n)=x++[true]++z := by
    have h:=split_at_addition f n (b-n) a hna (by omega) hAa
    rw [show n+(b-n)=b by omega] at h
    exact h
  rw [hs,cntF_append,cntF_append,show cntF [true]=0 by decide,Nat.add_zero] at hSb
  change cntF x=4 at hSa
  have hz : cntF z=1 := by omega
  have hqx:=cross_nonnegative x
  have hqz:=cross_nonnegative z
  change ones x=3 at hAb
  rw [hs,cross_at_addition,hAb,hz] at hQb
  omega

/-- The two candidate old ranks compete for the same original cross
budget, so there is at most one old-supplied endpoint in the interval. -/
theorem cross36_original_old_count (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : BlockWord w) (hS : subtractions f n K=6) (hQ : cross (seg f n K)=36) :
    cN (fun t=>f t=true ∧ tailOldRay w (seg f n (t-n)) 0) n K≤1 := by
  apply interval_unique_count
  intro a b hna ha hnb hb hOa hOb
  have hca:=actual_old_ranks f n K a w hw hna ha hOa.1 hS hQ hOa.2
  have hcb:=actual_old_ranks f n K b w hw hnb hb hOb.1 hS hQ hOb.2
  rcases hca with ⟨h7a,hsa,haa,_⟩|⟨h9a,hsa,_,hqa⟩ <;>
    rcases hcb with ⟨h7b,hsb,hab,_⟩|⟨h9b,hsb,_,hqb⟩
  · omega
  · exact (old_ranks_conflict f n a b hna (by omega) hOa.1 hsa haa hsb hqb).elim
  · exact (old_ranks_conflict f n b a hnb (by omega) hOb.1 hsb hab hsa hqa).elim
  · omega

end Recaman.Cross36OldSourceCut
