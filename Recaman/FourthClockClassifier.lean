import Recaman.OneGapInteriorA

namespace Recaman.FourthClockClassifier

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunTargetArea Recaman.SourceFamilyFreeCount Recaman.AdjacentRunSupply

def fourthClock (h M m L s U v i : Nat) : Bool :=
  let q : Int := (M : Int)+(L : Int)+(U : Int)-(m : Int)-(s : Int)-(v : Int)+(i : Int)-1
  let e : Int := (m : Int)+(s : Int)+(v : Int)+1-(L : Int)-(U : Int)-(i : Int)
  let r : Int := (L : Int)+(U : Int)-(s : Int)-(v : Int)+(i : Int)-1
  let a : Int := (s : Int)+(v : Int)+1-(U : Int)-(i : Int)
  let b : Int := (U : Int)-(v : Int)+(i : Int)-1
  decide (i=2 ∨
    (1≤q ∧ q≤(h : Int) ∧ (q+(m : Int)+(s : Int)+(v : Int))^2=
      2*(M : Int)*((m : Int)+(s : Int)+(v : Int))+2*(L : Int)*((s : Int)+(v : Int))+2*(U : Int)*(v : Int)+1) ∨
    (1≤e ∧ e≤(M : Int) ∧ 2*e*((m : Int)+(s : Int)+(v : Int))+2*(L : Int)*((s : Int)+(v : Int))+
      2*(U : Int)*(v : Int)=((m : Int)+(s : Int)+(v : Int))^2-1) ∨
    (1≤r ∧ r≤(m : Int) ∧ (r+(s : Int)+(v : Int))^2=
      2*(L : Int)*((s : Int)+(v : Int))+2*(U : Int)*(v : Int)+1) ∨
    (1≤a ∧ a≤(L : Int) ∧ 2*a*((s : Int)+(v : Int))+2*(U : Int)*(v : Int)=
      ((s : Int)+(v : Int))^2-1) ∨
    (1≤b ∧ b≤(s : Int) ∧ (b+(v : Int))^2=2*(U : Int)*(v : Int)+1))

private theorem suffix_const (N : Nat) (b : Bool) (x : List Bool) (P : List Bool → Prop) :
    (∃ t, t<(List.replicate N b++x).length ∧ P ((List.replicate N b++x).drop t)) ↔
      (∃ k, 1≤k ∧ k≤N ∧ P (List.replicate k b++x)) ∨
      (∃ t, t<x.length ∧ P (x.drop t)) := by
  rw [exists_drop_append]
  apply or_congr
  · simp only [List.length_replicate,List.drop_replicate]
    constructor
    · rintro ⟨t,ht,hp⟩
      exact ⟨N-t,by omega,by omega,hp⟩
    · rintro ⟨k,hk,hkN,hp⟩
      exact ⟨N-k,by omega,by simpa only [show N-(N-k)=k by omega] using hp⟩
  · rfl

/-- All actual local P2 source positions in the seven preceding runs
are included. This direction is sufficient for safe candidate pruning;
no finite head bound or independent local/old tag is assumed. -/
theorem fourthClock_sound (h M m L s U v i : Nat) (hv : 1≤v)
    (hlocal : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++
        List.replicate v false++List.replicate i true)=true) :
    fourthClock h M m L s U v i=true := by
  obtain ⟨t,ht,hm,hk⟩:=(localSupply_A_S_iff
    (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) i 0).mp
    (by simpa only [List.replicate_zero,List.append_nil] using hlocal)
  let P:=fun x : List Bool=>mass x+(i : Int)=1 ∧ runKey x= -2
  have hh : ∃ t, t<(List.replicate h false++(List.replicate M true++(List.replicate m false++
      (List.replicate L true++(List.replicate s false++(List.replicate U true++List.replicate v false)))))).length ∧
      P ((List.replicate h false++(List.replicate M true++(List.replicate m false++
      (List.replicate L true++(List.replicate s false++(List.replicate U true++List.replicate v false)))))).drop t) := by
    exact ⟨t,by simpa only [List.append_assoc] using ht,
      by simpa [P,List.append_assoc] using hm,by simpa [P,List.append_assoc] using hk⟩
  rw [suffix_const,suffix_const,suffix_const,suffix_const,suffix_const,suffix_const] at hh
  simp only [fourthClock,decide_eq_true_eq]
  rcases hh with ⟨q,hq,hqh,hm,hk⟩|⟨e,he,heM,hm,hk⟩|⟨q,hq,hqm,hm,hk⟩|
    ⟨e,he,heL,hm,hk⟩|⟨q,hq,hqs,hm,hk⟩|⟨e,he,heU,hm,hk⟩|⟨t,ht,hm,hk⟩
  · right; left
    simp only [P,mass_append,mass_rep_false,mass_replicate_A] at hm
    have hqeq : (M : Int)+(L : Int)+(U : Int)-(m : Int)-(s : Int)-(v : Int)+(i : Int)-1=(q : Int) := by omega
    rw [hqeq]
    refine ⟨by omega,by omega,?_⟩
    have hh : runKey (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)= -2 := by
      simpa only [List.append_assoc] using hk
    rw [runKey_seven_runs] at hh
    grind only
  · right; right; left
    simp only [P,mass_append,mass_rep_false,mass_replicate_A] at hm
    have heq : (m : Int)+(s : Int)+(v : Int)+1-(L : Int)-(U : Int)-(i : Int)=(e : Int) := by omega
    rw [heq]
    refine ⟨by omega,by omega,?_⟩
    have hh:=runKey_seven_runs 0 e m L s U v
    simp only [List.replicate_zero,List.nil_append] at hh
    have hkk : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false)= -2 := by simpa only [List.append_assoc] using hk
    rw [hh] at hkk
    simp only [Int.natCast_zero,Int.zero_add] at hkk
    grind only
  · right; right; right; left
    simp only [P,mass_append,mass_rep_false,mass_replicate_A] at hm
    have heq : (L : Int)+(U : Int)-(s : Int)-(v : Int)+(i : Int)-1=(q : Int) := by omega
    rw [heq]
    refine ⟨by omega,by omega,?_⟩
    have hkk : runKey (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)= -2 := by simpa only [List.append_assoc] using hk
    rw [runKey_five_runs] at hkk
    grind only
  · right; right; right; right; left
    simp only [P,mass_append,mass_rep_false,mass_replicate_A] at hm
    have heq : (s : Int)+(v : Int)+1-(U : Int)-(i : Int)=(e : Int) := by omega
    rw [heq]
    refine ⟨by omega,by omega,?_⟩
    have hh:=runKey_five_runs 0 e s U v
    simp only [List.replicate_zero,List.nil_append] at hh
    have hkk : runKey (List.replicate e true++List.replicate s false++List.replicate U true++List.replicate v false)= -2 := by simpa only [List.append_assoc] using hk
    rw [hh] at hkk
    simp only [Int.natCast_zero,Int.zero_add] at hkk
    grind only
  · right; right; right; right; right
    simp only [P,mass_append,mass_rep_false,mass_replicate_A] at hm
    have heq : (U : Int)-(v : Int)+(i : Int)-1=(q : Int) := by omega
    rw [heq]
    refine ⟨by omega,by omega,?_⟩
    have hkk : runKey (List.replicate q false++List.replicate U true++List.replicate v false)= -2 := by simpa only [List.append_assoc] using hk
    rw [runKey_S_A_S] at hkk
    grind only
  · exact False.elim (preceding_A_key_exclusion e v he hv (by simpa only [List.append_assoc] using hk))
  · left
    simp only [P,List.length_replicate,List.drop_replicate,mass_rep_false] at ht hm hk
    have hq : 1≤v-t := by omega
    rw [runKey_S] at hk
    have hsquare : ((v-t : Nat) : Int)^2=1 := by grind only
    have hq1 : v-t=1 := by
      by_cases hh : v-t=1
      · exact hh
      · have hp:=Int.mul_nonneg (show 0≤((v-t : Nat) : Int)-2 by omega)
          (show 0≤((v-t : Nat) : Int)+2 by omega)
        grind only
    rw [hq1] at hm
    omega

def fourthFastCount (h M m L s U v K : Nat) : Nat :=
  ((List.range K).filter (fourthClock h M m L s U v)).length

/-- The sound source classifier bounds the unchanged local ray count.
A finite check of fourthFastCount is usable only after its quantified
head/target domain has also been supplied. -/
theorem fourth_ray_fast_bound (h M m L s U v K : Nat) (hv : 1≤v) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      fourthFastCount h M m L s U v K := by
  rw [show fourthFastCount h M m L s U v K=cN (fun i=>fourthClock h M m L s U v i=true) 0 K from
    (Recaman.RunClockClassifier.cN_bool_filter (fourthClock h M m L s U v) K).symm]
  apply cN_mono
  intro i _ _ hi
  exact fourthClock_sound h M m L s U v i hv hi

/-- The classifier retains clock0 from the known B64 three-run word,
while an empty source family is not used as an extra supplier. -/
theorem fourth_clock_controls :
    fourthClock 2 1 6 5 2 4 1 0=true ∧
    fourthClock 0 0 0 0 0 0 1 2=true ∧
    fourthClock 0 0 0 0 0 4 1 0=false := by decide

end Recaman.FourthClockClassifier
