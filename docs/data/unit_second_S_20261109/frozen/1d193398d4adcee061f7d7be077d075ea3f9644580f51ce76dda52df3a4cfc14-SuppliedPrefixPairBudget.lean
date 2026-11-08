import Recaman.BlockSuffixPositivity

namespace Recaman.SuppliedPrefixPairBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Number of chronological S-before-A pairs in the actual interval.
This is a count, not an additional hypothesis or a supply tag. -/
noncomputable def saWeight (f : Nat → Bool) (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => saWeight f n k + if f (n+k)=true then cN (fun x=>f x=false) n k else 0

/-- Every supplied A needs one more earlier S than its running supply
count. Summing the exact actual prefix deficits gives a triangular cost,
for arbitrary histories and every number of runs. -/
theorem actual_SA_triangle (f : Nat → Bool) (n K : Nat)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    2*cN (fun x=>f x=true) n K+cN (EndN f 0) n K*(cN (EndN f 0) n K+1)≤2*saWeight f n K := by
  revert hpos
  induction K with
  | zero => intro hpos; simp only [cN,saWeight,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
  | succ K ih =>
    intro hpos
    have hIH:=ih (fun k hk hkK=>hpos k hk (by omega))
    have hP:=hpos (K+1) (by omega) (by omega)
    by_cases hA : f (n+K)=true
    · have hAc:=cN_succ_pos (fun x=>f x=true) n K hA
      have hSc:=cN_succ_neg (fun x=>f x=false) n K (by rw [hA]; decide)
      rw [hSc] at hP
      simp only [saWeight,if_pos hA]
      rw [hAc]
      by_cases hE : EndN f 0 (n+K)
      · have hEc:=cN_succ_pos (EndN f 0) n K hE
        rw [hEc] at hP ⊢
        have ht : (cN (EndN f 0) n K+1)*(cN (EndN f 0) n K+1+1)=
            cN (EndN f 0) n K*(cN (EndN f 0) n K+1)+2*(cN (EndN f 0) n K+1) := by grind only
        rw [ht]
        omega
      · have hEc:=cN_succ_neg (EndN f 0) n K hE
        rw [hEc] at hP ⊢
        omega
    · have hAc:=cN_succ_neg (fun x=>f x=true) n K hA
      have hEc:=cN_succ_neg (EndN f 0) n K (by intro he; exact hA he.1)
      simp only [saWeight,if_neg hA,Nat.add_zero]
      rw [hAc,hEc]
      exact hIH

end Recaman.SuppliedPrefixPairBudget
