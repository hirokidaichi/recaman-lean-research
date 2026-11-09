import Recaman.AdditionRankSlack

namespace Recaman.EarlySubtractionFloor

open Recaman.AdditionRankSlack Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Strict positivity forces the original interval to begin with S. -/
theorem first_subtraction (f : Nat → Bool) (n K : Nat) (hK : 0<K)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k) : f n=false := by
  cases h : f n with
  | false => rfl
  | true =>
    have hh:=hp 1 (by decide) (by omega)
    have hs : subtractions f n 1=0 := by simp [subtractions,cN,h]
    omega

/-- SAAA has a supplied third addition, so three actual additions in
an interval with strict prefix positivity require a second subtraction. -/
theorem two_subtractions_of_three_additions (f : Nat → Bool) (n K : Nat)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (ha : 3≤additions f n K) : 2≤subtractions f n K := by
  by_cases hs : 2≤subtractions f n K
  · exact hs
  · have ht : additions f n K+subtractions f n K=K := (cN_walk f n K).2
    have hpos:=hp K (by omega) (Nat.le_refl _)
    have hS : subtractions f n K=1 := by omega
    have h0:=first_subtraction f n K (by omega) hp
    have hS1 : subtractions f n 1=1 := by simp [subtractions,cN,h0]
    have hadd:=cN_add (fun x=>f x=false) n 1 (K-1)
    rw [show 1+(K-1)=K by omega] at hadd
    change subtractions f n K=subtractions f n 1+cN (fun x=>f x=false) (n+1) (K-1) at hadd
    have hz : cN (fun x=>f x=false) (n+1) (K-1)=0 := by omega
    have hA (t : Nat) (h1 : 1≤t) (ht : t<K) : f (n+t)=true := by
      have hn := not_of_cN_zero (P := fun x=>f x=false) (s := n+1) (K-1) hz (n+t)
        (by omega) (by omega)
      cases h : f (n+t) with
      | true => rfl
      | false => exact False.elim (hn h)
    have h1:=hA 1 (by decide) (by omega)
    have h2:=hA 2 (by decide) (by omega)
    have h3:=hA 3 (by decide) (by omega)
    have hseg : seg f n 3=[false,true,true] := by
      simp [seg,List.range_succ,Nat.add_assoc,h0,h1,h2]
    have hl : Recaman.ThreeNonsuppliedData.localSupply (seg f n ((n+3)-n))=true := by
      rw [show n+3-n=3 by omega,hseg]
      decide
    obtain ⟨haa,t,k,ht,hk,hw⟩:=(localSupply_seg_iff f n (n+3) (by omega) h3).mp hl
    have he : EndN f 0 (n+3) := ⟨haa,t,k,by omega,hk,hw⟩
    have hE4 : cN (EndN f 0) n 4=cN (EndN f 0) n 3+1 := cN_succ_pos _ n 3 he
    have hE:=count_prefix_le (EndN f 0) n 4 K (by omega)
    omega

end Recaman.EarlySubtractionFloor
