import Recaman.TwoSNextASpectrum

namespace Recaman.TwoSSmallSourceShapes

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

private theorem five_S_factor (L U v : Nat) (hL : 1≤L) (hL2 : L≤2)
    (hU : 1≤U) (hv : 1≤v) (hv4 : v≤4) (hLU : L+U≤6)
    (he : (5 : Int)*(L : Int)+(U : Int)*(v : Int)=12) :
    L=2 ∧ ((U=1 ∧ v=2) ∨ (U=2 ∧ v=1)) := by
  have hLc : L=1 ∨ L=2 := by omega
  rcases hLc with hL1|hL2'
  · rw [hL1] at he
    have hvc : v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
    rcases hvc with hv1|hv2|hv3|hv4'
    · rw [hv1] at he; omega
    · rw [hv2] at he; omega
    · rw [hv3] at he; omega
    · rw [hv4'] at he; omega
  · have hp:=Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
    rw [hL2'] at he
    have hU2 : U≤2 := by grind only
    have hUc : U=1 ∨ U=2 := by omega
    refine ⟨hL2',?_⟩
    rcases hUc with hu1|hu2
    · rw [hu1] at he
      exact Or.inl ⟨hu1,by omega⟩
    · rw [hu2] at he
      exact Or.inr ⟨hu2,by omega⟩

/-- Unlike the mixed-future spectrum, the genuine S/A/S future and
this source's own nonnegative clock leave exactly two source shapes. -/
theorem R_five_SAS_source_shapes (L s U v i : Nat) (hL : 1≤L) (hU : 1≤U)
    (hs : 1≤s) (hv : 1≤v) (hF : s+v=5)
    (htarget : runKey (List.replicate 2 false++(List.replicate L true++
      (List.replicate s false++List.replicate U true++List.replicate v false)))= -50)
    (hsource : sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false) i) :
    L=2 ∧ ((s=3 ∧ U=1 ∧ v=2 ∧ i=3) ∨ (s=4 ∧ U=2 ∧ v=1 ∧ i=2)) := by
  obtain ⟨a,ha,haL,hm,hkey⟩:=hsource
  let x:=List.replicate s false++List.replicate U true++List.replicate v false
  have hFx : cntF x=5 := by
    simp only [x,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  obtain ⟨haeq,hcases⟩:=Recaman.TwoSNextASpectrum.next_A_depth_spectrum x L 5 a ha haL
    (by decide) (by omega) htarget hkey
  have hL2 : L≤2 := by rcases hcases with hh|hh <;> omega
  rw [haeq] at hm hkey
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hm
  have hclock : L+U+i=6 := by omega
  rw [runKey_prepend_A] at hkey
  simp only [← List.append_assoc] at hkey
  rw [runKey_S_A_S] at hkey
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,Nat.add_zero] at hkey
  have hfi : (s : Int)+(v : Int)=5 := by omega
  rw [hfi] at hkey
  have he : (5 : Int)*(L : Int)+(U : Int)*(v : Int)=12 := by grind only
  obtain ⟨hL2',hc⟩:=five_S_factor L U v hL hL2 hU hv (by omega) (by omega) he
  refine ⟨hL2',?_⟩
  rcases hc with hh|hh
  · exact Or.inl ⟨by omega,hh.1,hh.2,by omega⟩
  · exact Or.inr ⟨by omega,hh.1,hh.2,by omega⟩

end Recaman.TwoSSmallSourceShapes
