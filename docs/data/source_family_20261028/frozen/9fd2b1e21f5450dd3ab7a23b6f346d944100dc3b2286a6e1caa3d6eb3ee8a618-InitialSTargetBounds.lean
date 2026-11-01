import Recaman.MiddleSTargetFreeGap

namespace Recaman.InitialSTargetBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget
open Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount
open Recaman.ThreeRunSourceShape Recaman.MiddleSTargetFreeGap Recaman.ASourceReuse
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A bound on the A signs gives a one-sided dominance for local windows
    after an arbitrary S prefix. No old-window or EndN erasure is asserted. -/
theorem localSupply_S_prefix_domination (h H : Nat) (v : List Bool)
    (hbudget : ones v≤(H : Int)+1)
    (hs : Recaman.ThreeNonsuppliedData.localSupply (List.replicate h false++v)=true) :
    Recaman.ThreeNonsuppliedData.localSupply (List.replicate H false++v)=true := by
  rw [localSupply_iff] at hs ⊢
  let P := fun x : List Bool => mass x=1 ∧ Recaman.ThreeNonsuppliedData.wordArea x=0
  have hh : (∃ t, t<(List.replicate h false++v).length ∧ P ((List.replicate h false++v).drop t)) := hs
  rw [exists_drop_append] at hh
  rcases hh with ⟨t,ht,hm,ha⟩|⟨t,ht,hm,ha⟩
  · simp only [List.length_replicate,List.drop_replicate,mass_append,mass_rep_false] at ht hm ha
    have hmV := mass_eq v
    have hv := ones_bounds v
    have hqH : h-t≤H := by omega
    refine ⟨H-(h-t),?_,?_,?_⟩
    · simp only [List.length_append,List.length_replicate]
      omega
    · rw [List.drop_append,List.drop_replicate,List.length_replicate,
        show H-(h-t)-H=0 by omega,List.drop_zero,
        show H-(H-(h-t))=h-t by omega,mass_append,mass_rep_false]
      exact hm
    · rw [List.drop_append,List.drop_replicate,List.length_replicate,
        show H-(h-t)-H=0 by omega,List.drop_zero,
        show H-(H-(h-t))=h-t by omega]
      exact ha
  · have hd : (List.replicate H false++v).drop (H+t)=v.drop t := by
      rw [List.drop_append,List.drop_replicate,List.length_replicate,
        show H-(H+t)=0 by omega,List.replicate_zero,List.nil_append,
        show H+t-H=t by omega]
    refine ⟨H+t,by simp only [List.length_append,List.length_replicate]; omega,?_,?_⟩
    · simpa only [hd] using hm
    · simpa only [hd] using ha

theorem rayCount_S_prefix_domination (h H : Nat) (v : List Bool) (K : Nat)
    (hbudget : ones v+(K : Int)≤(H : Int)+2) :
    rayCount (List.replicate h false++v) K≤rayCount (List.replicate H false++v) K := by
  unfold rayCount
  apply cN_mono
  intro i _ hi hs
  have hb : ones (v++List.replicate i true)≤(H : Int)+1 := by
    rw [ones_append,ones_replicate_A]
    omega
  simpa only [List.append_assoc] using localSupply_S_prefix_domination h H
    (v++List.replicate i true) hb (by simpa only [List.append_assoc] using hs)

theorem initial_S_target_equations (q M m L s T j : Nat) (hM : 1≤M) (hm : 1≤m)
    (hmass : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    M+L+T=q+m+s+j+1 ∧
    ((q : Int)+(m : Int)+(s : Int))^2-((j : Int)+1)^2=
      2*(M : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int) ∧
    j+2<q+m+s ∧ 2*(j+1)+2≤M+L+T := by
  have hkey := source_key_before_gap
    (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T j hmass harea
  rw [runKey_five_runs] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
  have hpos := Int.mul_pos (show 0<2*(M : Int) by omega) (show 0<(m : Int)+(s : Int) by omega)
  have hnonneg := Int.mul_nonneg (show 0≤2*(L : Int) by omega) (show 0≤(s : Int) by omega)
  have hgreater : j+1<q+m+s := by
    by_cases h : j+1<q+m+s
    · exact h
    · have hp := Int.mul_nonneg (show 0≤(j : Int)+1-((q : Int)+(m : Int)+(s : Int)) by omega)
        (show 0≤(j : Int)+1+((q : Int)+(m : Int)+(s : Int)) by omega)
      grind
  have heq : ((q : Int)+(m : Int)+(s : Int))^2-((j : Int)+1)^2=
      2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) := by grind
  have hne : q+m+s≠j+2 := by
    intro hh
    have hi : (q : Int)+(m : Int)+(s : Int)=(j : Int)+2 := by omega
    have hid : ((j : Int)+2)^2-((j : Int)+1)^2=2*(j : Int)+3 := by grind
    rw [hi,hid] at heq
    omega
  exact ⟨by omega,by grind,by omega,by omega⟩

theorem S_prefix_domination_boundary :
    Recaman.ThreeNonsuppliedData.localSupply ([false]++[true,true])=true ∧
      Recaman.ThreeNonsuppliedData.localSupply ([]++[true,true])=false := by decide

end Recaman.InitialSTargetBounds
