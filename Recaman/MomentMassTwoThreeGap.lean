import Recaman.ThreeGapInteriorA

namespace Recaman.MomentMassTwoThreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortGapSourceClocks Recaman.ThreeGapInteriorA

/-- In all three v3 target parameter groups, local supply occupies at
most five of the six clocks. The exceptional initial-S family is paid by
merging the second-A family into clock0. -/
theorem mass_two_three_local_budget (h M m L s U S : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hSsum : h+m+s=S) (hAsum : M+L+U=S) (B : Int)
    (haz : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B)
    (hlo : 4*(S : Int)+6≤B) (hhi : B≤6*(S : Int)+4)
    (hparam : (S=12 ∧ B=76) ∨ (S=13 ∧ B=79) ∨ (S=14 ∧ B=84)) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) 6≤5 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
    List.replicate U true++List.replicate 3 false)
  let R:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false)
  let E : Nat → Prop:=if B=6*(S : Int)+1 then sourceAt false h (x++List.replicate 3 false)
    else sourceAt true L (List.replicate s false++List.replicate U true++List.replicate 3 false)
  have hS12 : 12≤S := by rcases hparam with h|h|h <;> omega
  have hmz : mass (List.replicate h false++x)=0 := by
    clear haz hlo hhi hparam
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hcnt : cntF (List.replicate h false++x)=S := by
    have hc:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=2*S := by
      simp only [x,List.length_append,List.length_replicate]
      omega
    rw [hmz,hl] at hc
    omega
  have hpoint : ∀ i, i<6 → Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false++
        List.replicate i true)=true → P i ∨ Q i ∨ R i ∨ E i := by
    intro i hi hl
    rcases (local_fourth_sources h M m L s U 3 i (by decide)).mp hl with h0|h1|h2|h3|h4|h5
    · by_cases hEx : B=6*(S : Int)+1
      · right; right; right
        simpa only [E,if_pos hEx,x,List.append_assoc] using h0
      · have hc:=initial_family_small_band h 3 i x B hmz
          (by simpa only [x,List.append_assoc] using haz)
          (by rw [hcnt]; omega) (by rw [hcnt]; exact hlo) (by rw [hcnt]; exact hhi)
          (by decide) (by decide) (by simpa only [x,List.append_assoc] using h0)
        rw [hcnt] at hc
        rcases hc with hc|hc <;> omega
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · by_cases hEx : B=6*(S : Int)+1
      · have hS13 : S=13 := by rcases hparam with h|h|h <;> omega
        have hB79 : B=79 := by omega
        obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        have hi0:=special_second_A_clock_zero h M m L s U e i hh hM hm hL hs hU
          (by omega) (by omega) (by simpa only [hB79] using haz) he heL hi
          (by simpa only [List.append_assoc] using hbal)
          (by simpa only [List.append_assoc] using hkey)
        exact Or.inl (Or.inl hi0)
      · right; right; right
        simpa only [E,if_neg hEx] using h3
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
      exact Or.inl (tail_S_small_gap_clock q U 3 i hq (by decide) (by decide)
        (by simpa only [List.append_assoc] using hbal) (by simpa only [List.append_assoc] using hkey))
    · exact Or.inl (Or.inr h5)
  have hb : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 3 false) 6≤
      cN (fun i=>P i ∨ Q i ∨ R i ∨ E i) 0 6 := by
    apply cN_mono
    intro i _ hi hl
    exact hpoint i (by omega) hl
  have hp : cN P 0 6≤2 := zero_two_count _
  have hq : cN Q 0 6≤1 := sourceAt_count_le_one true M _ _
  have hr : cN R 0 6≤1 := sourceAt_count_le_one false m _ _
  have he : cN E 0 6≤1 := by
    by_cases hEx : B=6*(S : Int)+1
    · simpa only [E,if_pos hEx] using sourceAt_count_le_one false h (x++List.replicate 3 false) 6
    · simpa only [E,if_neg hEx] using sourceAt_count_le_one true L
        (List.replicate s false++List.replicate U true++List.replicate 3 false) 6
  have h1:=cN_or_le P (fun i=>Q i ∨ R i ∨ E i) 6
  have h2:=cN_or_le Q (fun i=>R i ∨ E i) 6
  have h3:=cN_or_le R E 6
  omega

end Recaman.MomentMassTwoThreeGap
