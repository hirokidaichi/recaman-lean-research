import Recaman.ThreeRunSupplyBudget

namespace Recaman.SourceFamilyFreeCount

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget
open Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem suffix_const (N : Nat) (b : Bool) (v : List Bool) (P : List Bool → Prop) :
    (∃ t, t<(List.replicate N b++v).length ∧ P ((List.replicate N b++v).drop t)) ↔
      (∃ k, 1≤k ∧ k≤N ∧ P (List.replicate k b++v)) ∨
      (∃ t, t<v.length ∧ P (v.drop t)) := by
  rw [exists_drop_append]
  apply or_congr
  · simp only [List.length_replicate,List.drop_replicate]
    constructor
    · rintro ⟨t,ht,hp⟩
      exact ⟨N-t,by omega,by omega,hp⟩
    · rintro ⟨k,hk,hkN,hp⟩
      exact ⟨N-k,by omega,by simpa only [show N-(N-k)=k by omega] using hp⟩
  · rfl

theorem runKey_five_runs (q M m L s : Nat) :
    runKey (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)=
      4*(M : Int)*((m : Int)+(s : Int))+4*(L : Int)*(s : Int)-
        2*((q : Int)+(m : Int)+(s : Int))^2 := by
  rw [runKey_append_S,runKey_append_A,runKey_S_A_S]
  simp only [mass_append,mass_rep_false,mass_replicate_A]
  grind

private theorem first_A_key_impossible (e R : Nat) (he : 1≤e) (he3 : e≤3)
    (hR : 5≤R) :
    ¬runKey (List.replicate e true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false)=-2 := by
  intro hk
  have hz := runKey_five_runs 0 e (R+1) R 1
  simp only [List.replicate_zero,List.nil_append] at hz
  rw [hz] at hk
  simp only [Int.natCast_add,Int.natCast_one] at hk
  by_cases hr5 : R=5
  · subst R
    have hc : e=1 ∨ e=2 ∨ e=3 := by omega
    rcases hc with rfl|rfl|rfl <;> simp at hk
  · have hp := Int.mul_nonneg (show 0≤(R : Int)-6 by omega)
      (show 0≤(R : Int)+2 by omega)
    have heprod := Int.mul_nonneg (show 0≤3-(e : Int) by omega)
      (show 0≤2*((R : Int)+2) by omega)
    have eq : 2*(e : Int)*((R : Int)+2)=(R : Int)^2+2*(R : Int)+3 := by grind
    grind

private theorem first_S_key_impossible (q M R : Nat) (hq : 1≤q) (hM : M≤3)
    (hR : 5≤R) :
    ¬runKey (List.replicate q false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false)=-2 := by
  intro hk
  rw [runKey_five_runs] at hk
  simp only [Int.natCast_add,Int.natCast_one] at hk
  have hp := Int.mul_nonneg (show 0≤(q : Int)-1 by omega)
    (show 0≤(q : Int)+2*(R : Int)+5 by omega)
  have hr := Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
    (show 0≤(R : Int)+3 by omega)
  have hm := Int.mul_nonneg (show 0≤3-(M : Int) by omega)
    (show 0≤2*((R : Int)+2) by omega)
  grind

private theorem middle_S_key_impossible (q R i : Nat) (hq : 1≤q) (hR : 5≤R)
    (hm : mass (List.replicate q false++List.replicate R true++List.replicate 1 false)+
      (i : Int)=1) :
    ¬runKey (List.replicate q false++List.replicate R true++List.replicate 1 false)=-2 := by
  intro hk
  rw [runKey_S_A_S] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  have hp := Int.mul_nonneg (show 0≤(q : Int)+2-(R : Int) by omega)
    (show 0≤(q : Int)+(R : Int) by omega)
  have hr := Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
    (show 0≤(R : Int)+1 by omega)
  grind

/-- All five local source runs are retained. For this family every local
    supply along the third A ray is at clock2, for unbounded R and h. -/
theorem third_ray_local_clock (h M R i : Nat) (hM : M≤3) (hR : 5≤R)
    (hs : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
        List.replicate R true++List.replicate 1 false++List.replicate i true)=true) : i=2 := by
  obtain ⟨t,ht,hm,hk⟩ := (localSupply_A_S_iff
    (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false) i 0).mp (by simpa using hs)
  let P := fun v : List Bool => mass v+(i : Int)=1 ∧ runKey v=-2
  have hh : ∃ t, t<(List.replicate h false++(List.replicate M true++
      (List.replicate (R+1) false++(List.replicate R true++List.replicate 1 false)))).length ∧
      P ((List.replicate h false++(List.replicate M true++
      (List.replicate (R+1) false++(List.replicate R true++List.replicate 1 false)))).drop t) := by
    exact ⟨t,by simpa only [List.append_assoc] using ht,
      by simpa only [List.append_assoc,P] using hm,
      by simpa only [List.append_assoc,P] using hk⟩
  rw [suffix_const,suffix_const,suffix_const,suffix_const] at hh
  rcases hh with ⟨q,hq,hqh,hm,hk⟩|⟨e,he,heM,hm,hk⟩|⟨q,hq,hqR,hm,hk⟩|
    ⟨e,he,heR,hm,hk⟩|⟨t,ht,hm,hk⟩
  · exact False.elim (first_S_key_impossible q M R hq hM hR (by simpa only [List.append_assoc] using hk))
  · exact False.elim (first_A_key_impossible e R he (by omega) hR (by simpa only [List.append_assoc] using hk))
  · exact False.elim (middle_S_key_impossible q R i hq hR
      (by simpa only [List.append_assoc] using hm) (by simpa only [List.append_assoc] using hk))
  · have heq := runKey_A_S e 1
    have hk' : runKey (List.replicate e true++List.replicate 1 false)=-2 := hk
    rw [heq] at hk'
    omega
  · simp only [List.length_replicate] at ht
    have ht0 : t=0 := by omega
    subst t
    simp only [List.drop_zero,mass_rep_false] at hm
    omega

end Recaman.SourceFamilyFreeCount
