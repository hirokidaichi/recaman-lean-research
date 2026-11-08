import Recaman.BlockOldRay

namespace Recaman.ChronologicalSupplyKeyBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Classical

/-- Chronological pairs consisting of an already supplied A followed by
an actual free A. No future supplier is counted as an earlier resource. -/
noncomputable def suppliedFreePairs (f : Nat → Bool) (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => suppliedFreePairs f n k+
      if f (n+k)=true ∧ ¬EndN f 0 (n+k) then cN (EndN f 0) n k else 0

/-- An actual all-run key budget with the chronological E-before-free
penalty retained. It assumes only the explicit strict prefix deficits. -/
theorem actual_chronological_key_budget (f : Nat → Bool) (n K : Nat)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    runKey (seg f n K)+2*(cN (fun x=>f x=false) n K : Int)^2+
      4*(cN (fun x=>f x=true) n K : Int)+
      2*(cN (EndN f 0) n K : Int)*((cN (EndN f 0) n K : Int)+1)+
      4*(suppliedFreePairs f n K : Int)≤
      4*(cN (fun x=>f x=true) n K : Int)*(cN (fun x=>f x=false) n K : Int) := by
  revert hpos
  induction K with
  | zero => intro hpos; simp [seg,cN,suppliedFreePairs,runKey,areaW,mass]
  | succ K ih =>
    intro hpos
    have hIH:=ih (fun k hk hkK=>hpos k hk (by omega))
    have hP:=hpos (K+1) (by omega) (by omega)
    by_cases hA : f (n+K)=true
    · have hAc:=cN_succ_pos (fun x=>f x=true) n K hA
      have hSc:=cN_succ_neg (fun x=>f x=false) n K (by rw [hA]; decide)
      have hk : runKey (seg f n (K+1))=runKey (seg f n K) := by
        rw [seg_succ,hA]
        exact runKey_append_A (seg f n K) 1
      rw [hSc] at hP
      by_cases hE : EndN f 0 (n+K)
      · have hEc:=cN_succ_pos (EndN f 0) n K hE
        have hJ : suppliedFreePairs f n (K+1)=suppliedFreePairs f n K := by
          simp only [suppliedFreePairs,if_neg (show ¬(f (n+K)=true ∧ ¬EndN f 0 (n+K)) by intro hh; exact hh.2 hE),Nat.add_zero]
        rw [hEc] at hP
        rw [hk,hAc,hSc,hEc,hJ]
        simp only [Int.natCast_add,Int.natCast_one]
        grind only
      · have hEc:=cN_succ_neg (EndN f 0) n K hE
        have hJ : suppliedFreePairs f n (K+1)=suppliedFreePairs f n K+cN (EndN f 0) n K := by
          simp only [suppliedFreePairs,if_pos (show f (n+K)=true ∧ ¬EndN f 0 (n+K) from ⟨hA,hE⟩)]
        rw [hEc] at hP
        rw [hk,hAc,hSc,hEc,hJ]
        simp only [Int.natCast_add,Int.natCast_one]
        grind only
    · have hfalse : f (n+K)=false := by cases hf : f (n+K) <;> simp_all
      have hAc:=cN_succ_neg (fun x=>f x=true) n K hA
      have hSc:=cN_succ_pos (fun x=>f x=false) n K hfalse
      have hEc:=cN_succ_neg (EndN f 0) n K (by intro he; exact hA he.1)
      have hJ : suppliedFreePairs f n (K+1)=suppliedFreePairs f n K := by
        simp only [suppliedFreePairs,if_neg (show ¬(f (n+K)=true ∧ ¬EndN f 0 (n+K)) by intro hh; exact hA hh.1),Nat.add_zero]
      have hmass : mass (seg f n K)=(cN (fun x=>f x=true) n K : Int)-(cN (fun x=>f x=false) n K : Int) := by
        have hm:=seg_mass f n K
        have hw:=(cN_walk f n K).1
        omega
      have hk : runKey (seg f n (K+1))=runKey (seg f n K)+
          4*((cN (fun x=>f x=true) n K : Int)-(cN (fun x=>f x=false) n K : Int))-2 := by
        rw [seg_succ,hfalse]
        have he:=runKey_append_S (seg f n K) 1
        rw [hmass] at he
        grind only
      rw [hk,hAc,hSc,hEc,hJ]
      simp only [Int.natCast_add,Int.natCast_one]
      grind only

end Recaman.ChronologicalSupplyKeyBudget
