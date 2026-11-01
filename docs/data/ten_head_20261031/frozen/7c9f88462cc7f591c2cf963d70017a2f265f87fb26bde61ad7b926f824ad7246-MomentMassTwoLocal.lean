import Recaman.MomentFirstASource
import Recaman.FourthSourceFamilies

namespace Recaman.MomentMassTwoLocal

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortGapSourceClocks Recaman.OneGapInteriorA Recaman.MomentFirstASource

/-- The target-derived v1/2 parameter groups need no finite head table:
the first A source joins clocks0/2, leaving local budgets3/4. -/
theorem mass_two_short_local_budget (h M m L s U S v : Nat) (hh : 1≤h) (hs : 1≤s)
    (hSsum : h+m+s=S) (hAsum : M+L+U=S) (B : Int)
    (haz : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B)
    (hlo : 4*(S : Int)+6≤B) (hhi : B≤6*(S : Int)+4)
    (hparam : (v=1 ∧ 12≤S ∧ S≤14 ∧ (B=4*(S : Int)+27 ∨ B=4*(S : Int)+28)) ∨
      (v=2 ∧ ((S=12 ∧ B=76) ∨ (S=13 ∧ B=81) ∨ (S=14 ∧ B=84)))) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) (v+3)≤v+2 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let R:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  have hv12 : v=1 ∨ v=2 := by rcases hparam with h|h <;> omega
  have hv : 1≤v := by omega
  have hv3 : v≤3 := by omega
  have hS12 : 12≤S := by rcases hparam with h|h; omega; rcases h.2 with h|h|h <;> omega
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
  have hpoint : ∀ i, i<v+3 → Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true → P i ∨ Q i ∨ (v=2 ∧ R i) := by
    intro i hi hl
    rcases (local_fourth_sources h M m L s U v i hv).mp hl with h0|h1|h2|h3|h4|h5
    · have he:=initial_family_small_clock h v i x B hmz
        (by simpa only [x,List.append_assoc] using haz) (by rw [hcnt]; omega)
        (by rw [hcnt]; exact hlo) (by rw [hcnt]; exact hhi) hv hv3
        (by simpa only [x,List.append_assoc] using h0)
      left
      change i=0 ∨ i=2
      rcases he with he|he <;> omega
    · obtain ⟨e,he,heM,hbal,hkey⟩:=h1
      have heq:=first_A_clock_equation h M m L s U S v e i B hSsum hAsum haz
        (by simpa only [List.append_assoc] using hbal)
        (by simpa only [List.append_assoc] using hkey)
      left
      change i=0 ∨ i=2
      rcases hparam with h1|h2
      · obtain ⟨hv1,hSlo,hShi,hB⟩:=h1
        subst v
        exact first_A_one_gap_low_clock h S i B hh hSlo hShi hB (by omega) (by grind only)
      · obtain ⟨hv2,hSB⟩:=h2
        subst v
        exact first_A_two_gap_low_clock h S i B hh hSB (by omega) (by grind only)
    · exact Or.inr (Or.inl h2)
    · by_cases hv2 : v=2
      · exact Or.inr (Or.inr ⟨hv2,h3⟩)
      · have hv1 : v=1 := by omega
        subst v
        obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        have hi2:=interior_A_one_gap_clock e s U i he hs
          (by simpa only [List.replicate_one,List.append_assoc] using hbal)
          (by simpa only [List.replicate_one,List.append_assoc] using hkey)
        exact Or.inl (Or.inr hi2)
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
      exact Or.inl (tail_S_small_gap_clock q U v i hq hv hv3
        (by simpa only [List.append_assoc] using hbal) (by simpa only [List.append_assoc] using hkey))
    · exact Or.inl (Or.inr h5)
  have hb : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) (v+3)≤
      cN (fun i=>P i ∨ Q i ∨ (v=2 ∧ R i)) 0 (v+3) := by
    apply cN_mono
    intro i _ hi hl
    exact hpoint i (by omega) hl
  have hp : cN P 0 (v+3)≤2 := zero_two_count _
  have hq : cN Q 0 (v+3)≤1 := sourceAt_count_le_one false m _ _
  have hr : cN (fun i=>v=2 ∧ R i) 0 (v+3)≤v-1 := by
    by_cases hv2 : v=2
    · have he : cN (fun i=>v=2 ∧ R i) 0 (v+3)≤cN R 0 (v+3) := by
        apply cN_mono
        intro i _ _ hi
        exact hi.2
      have hh : cN R 0 (v+3)≤1 := sourceAt_count_le_one true L _ _
      omega
    · have hz : cN (fun i=>v=2 ∧ R i) 0 (v+3)=0 := by
        apply cN_zero_of
        intro i _ _ hi
        exact hv2 hi.1
      rw [hz]
      omega
  have h1:=cN_or_le P (fun i=>Q i ∨ (v=2 ∧ R i)) (v+3)
  have h2:=cN_or_le Q (fun i=>v=2 ∧ R i) (v+3)
  omega

end Recaman.MomentMassTwoLocal
