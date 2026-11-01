import Recaman.OneSLocalSaturation
import Recaman.MomentSmallHeadPruning

namespace Recaman.OneSMiddleSourcePruning

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.SourceFamilyFreeCount

private theorem one_S_numbers (S M m s R : Nat)
    (hS12 : 12≤S) (hS14 : S≤14) (hM5 : 5≤M) (hM6 : M≤6)
    (hR5 : 5≤R) (hRM : R≤M) (hm : 1≤m) (hs : 2≤s)
    (hklo : -2≤2*(S : Int)^2-4*(M : Int)*(m : Int)-4*((S : Int)-4)*(s : Int)-12*(S : Int)-10-2*(R : Int)^2)
    (hkhi : 2*(S : Int)^2-4*(M : Int)*(m : Int)-4*((S : Int)-4)*(s : Int)-12*(S : Int)-10-2*(R : Int)^2≤2) :
      (S=12 ∧ M=5 ∧ R=5 ∧ m=1 ∧ s=2) ∨
      (S=13 ∧ M=6 ∧ R=5 ∧ m=2 ∧ s=2) ∨
      (S=14 ∧ M=5 ∧ R=6 ∧ m=3 ∧ s=2) ∨
      (S=14 ∧ M=5 ∧ R=6 ∧ m=1 ∧ s=3) ∨
      (S=14 ∧ M=6 ∧ R=6 ∧ m=1 ∧ s=3) := by
  have hMs : M=5 ∨ M=6 := by omega
  have hRs : R=5 ∨ R=6 := by omega
  have hSs : S=12 ∨ S=13 ∨ S=14 := by omega
  rcases hMs with rfl|rfl
  · rcases hRs with rfl|rfl
    · rcases hSs with rfl|rfl|rfl
      · exact Or.inl ⟨rfl,rfl,rfl,by omega,by omega⟩
      · omega
      · omega
    · rcases hSs with rfl|rfl|rfl
      · omega
      · omega
      · have hsc : s=2 ∨ s=3 := by omega
        rcases hsc with rfl|rfl
        · exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,by omega,rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,by omega,rfl⟩)))
  · rcases hRs with rfl|rfl
    · rcases hSs with rfl|rfl|rfl
      · omega
      · exact Or.inr (Or.inl ⟨rfl,rfl,rfl,by omega,by omega⟩)
      · omega
    · rcases hSs with rfl|rfl|rfl
      · omega
      · omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,rfl,by omega,by omega⟩)))

/-- The internally necessary U4/M5..6/R5..6 bounds leave five integer
head tuples. None admits the required middle-S source, including q=m.
The source prefix itself and all old history remain untruncated. -/
theorem one_S_middle_source_excluded (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (S M m L s R i : Nat) (hS10 : 10≤S) (hS14 : S≤14)
    (hM5 : 5≤M) (hM6 : M≤6) (hR5 : 5≤R) (hRM : R≤M)
    (hm : 1≤m) (hs : 2≤s) (hL : 1≤L) (hzero : M+L+4=S)
    (B : Int) (hB : B=(S : Int)^2-2*((M : Int)*(m : Int)+((S : Int)-4)*(s : Int)))
    (hkeyTarget : runKey u=2*B-12*(S : Int)-10-2*(R : Int)^2) :
    ¬sourceAt false m (List.replicate L true++List.replicate s false++List.replicate 4 true++List.replicate 1 false) i := by
  intro he
  obtain ⟨q,hq,hqm,hbal,hkey⟩:=he
  have hlow : -2≤runKey u := by rcases block_mass_three hu hcu with rfl|rfl|rfl <;> decide
  have hupp : runKey u≤2 := by rcases block_mass_three hu hcu with rfl|rfl|rfl <;> decide
  have hklo : -2≤2*(S : Int)^2-4*(M : Int)*(m : Int)-4*((S : Int)-4)*(s : Int)-12*(S : Int)-10-2*(R : Int)^2 := by
    rw [hB] at hkeyTarget
    grind only
  have hkhi : 2*(S : Int)^2-4*(M : Int)*(m : Int)-4*((S : Int)-4)*(s : Int)-12*(S : Int)-10-2*(R : Int)^2≤2 := by
    rw [hB] at hkeyTarget
    grind only
  have hS12 : 12≤S := by
    by_cases hh : 12≤S
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)-1 by omega)
      have hq:=Int.mul_nonneg (show 0≤(S : Int)-4 by omega) (show 0≤(s : Int)-2 by omega)
      have hr:=Int.mul_nonneg (show 0≤(R : Int)-5 by omega) (show 0≤(R : Int)+5 by omega)
      have ht:=Int.mul_nonneg (show 0≤11-(S : Int) by omega) (show 0≤(S : Int)+1 by omega)
      grind only
  have hcases:=one_S_numbers S M m s R hS12 hS14 hM5 hM6 hR5 hRM hm hs hklo hkhi
  have hk : runKey (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate 4 true++List.replicate 1 false)= -2 := by
    simpa only [List.append_assoc] using hkey
  rw [runKey_five_runs] at hk
  rcases hcases with hc|hc|hc|hc|hc
  all_goals rcases hc with ⟨rfl,rfl,rfl,rfl,rfl⟩
  all_goals
    have hqs : q=1 ∨ q=2 ∨ q=3 := by omega
    rcases hqs with rfl|rfl|rfl <;> omega

end Recaman.OneSMiddleSourcePruning
