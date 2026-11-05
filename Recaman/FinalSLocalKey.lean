import Recaman.FourCrossExact
import Recaman.FourthSourceFamilies
import Recaman.ShortCounterFactorBounds

namespace Recaman.FinalSLocalKey

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile Recaman.ShortCounterFactorBounds

theorem fourth_prefix_key (h M m L s U v : Nat) :
    runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)=
    4*(((M : Int)+(L : Int)+(U : Int))*(v : Int)+(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))-
      2*((h : Int)+(m : Int)+(s : Int)+(v : Int))^2 := by
  have he:=Recaman.FourCrossExact.four_cross_exact h M m L s U v 0
  dsimp only at he
  simp only [List.replicate_zero,List.append_nil,cntF_append,cntF_A,cntF_replicate_S,
    Nat.add_zero,Int.natCast_add] at he
  omega

theorem third_separator_A_floor (s U v i : Nat) (hv : 1≤v)
    (he : sourceAt false s (List.replicate U true++List.replicate v false) i) :
    v+2≤2*U := by
  obtain ⟨q,hq,_,_,hk⟩:=he
  rw [←List.append_assoc,runKey_S_A_S] at hk
  have hsq:=square_lower ((q : Int)+(v : Int)) ((v : Int)+1) (by omega) (by omega)
  by_cases hb : v+2≤2*U
  · exact hb
  · have hp:=Int.mul_pos (show 0<(v : Int) by omega) (show 0<(v : Int)+2-2*(U : Int) by omega)
    grind only

/-- On a small head with a long final separator, neither of the first
two final-ray clocks has a local source. Old clocks remain separate. -/
theorem small_head_no_local_early (h M m L s U v i : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hN : M+L+U≤5) (hv : 3≤v ∨ (M+L+U=3 ∧ 2≤v)) (hi : i≤1) :
    ¬Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++
        List.replicate v false++List.replicate i true)=true := by
  intro he
  rcases (local_fourth_sources h M m L s U v i (by omega)).mp he with h0|h1|h2|h3|h4|h5
  · obtain ⟨q,hq,_,hb,_⟩:=h0
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hb
    omega
  · obtain ⟨e,he,eM,hb,hk⟩:=h1
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hb
    have hm1 : m=1 := by omega
    have hs1 : s=1 := by omega
    have hv3 : v=3 := by omega
    have hk' : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
        List.replicate s false++List.replicate U true++List.replicate v false)= -2 := by
      simpa only [List.append_assoc] using hk
    have hh:=fourth_prefix_key 0 e m L s U v
    simp only [List.replicate_zero,List.nil_append] at hh
    rw [hk',hm1,hs1,hv3] at hh
    grind only
  · obtain ⟨q,hq,_,hb,_⟩:=h2
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hb
    omega
  · obtain ⟨e,he,eL,hb,hk⟩:=h3
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hb
    have hs1 : s=1 := by omega
    have hv3 : v=3 := by omega
    have hk' : runKey (List.replicate e true++List.replicate s false++
        List.replicate U true++List.replicate v false)= -2 := by simpa only [List.append_assoc] using hk
    have hh:=fourth_prefix_key 0 0 0 e s U v
    simp only [List.replicate_zero,List.nil_append] at hh
    rw [hk',hs1,hv3] at hh
    have hh' : (-2 : Int)=4*(4*(e : Int)+3*(U : Int))-32 := by grind only
    omega
  · obtain ⟨q,hq,_,hb,_⟩:=h4
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hb
    omega
  · omega

end Recaman.FinalSLocalKey
