import Recaman.LowSeparatorSources

namespace Recaman.LowSeparatorLocalBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortGapSourceClocks Recaman.OneGapInteriorA

/-- The same mass-three target removes the first two source families.
For S1/S2, the remaining local ray costs respectively three/four clocks.
This is not yet the free-gap: a critical one-unit deficit remains. -/
theorem low_separator_source_cover (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U v R i : Nat) (hv : v=1 ∨ v=2) (hR : 1≤R)
    (hzero : M+L+U=h+m+s) (hs : 1≤s) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2)
    (hi : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++
        List.replicate s false++List.replicate U true++List.replicate v false++List.replicate i true)=true) :
    (i=0 ∨ i=2) ∨
    sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) i ∨
    (v=2 ∧ sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false) i) := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  have hvpos : 1≤v := by omega
  have hv2 : v≤2 := by omega
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF (List.replicate h false++x)=h+m+s := by
    have hc:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=h+M+m+L+s+U := by
      simp only [x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hc
    omega
  have hBx : runKey (List.replicate h false++x)= -2*B := by
    simpa only [x,List.append_assoc] using hB
  have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true → P i ∨ Q i ∨ (v=2 ∧ D i) := by
    intro i hi
    rcases (local_fourth_sources h M m L s U v i hvpos).mp hi with h0|h1|h2|h3|h4|h5
    · have hn:=Recaman.LowSeparatorSources.low_separator_initial_source_excluded u x hu h v R i hv hR hmz
        (by rw [hBx,hSz]; simp only [Int.natCast_add]; omega)
      exact False.elim (hn (by simpa only [x,List.append_assoc] using h0))
    · exact False.elim (Recaman.LowSeparatorSources.low_separator_first_A_excluded u hu hcu h M m L s U v R i
        hv hzero hbudget B hB hkeyTarget h1)
    · exact Or.inr (Or.inl h2)
    · by_cases hvTwo : v=2
      · exact Or.inr (Or.inr ⟨hvTwo,h3⟩)
      · have hvOne : v=1 := by omega
        subst v
        obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        have hi2:=interior_A_one_gap_clock e s U i he hs
          (by simpa only [List.replicate_one,List.append_assoc] using hbal)
          (by simpa only [List.replicate_one,List.append_assoc] using hkey)
        exact Or.inl (Or.inr hi2)
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
      have hi02:=tail_S_small_gap_clock q U v i hq hvpos (by omega)
        (by simpa only [List.append_assoc] using hbal)
        (by simpa only [List.append_assoc] using hkey)
      exact Or.inl hi02
    · exact Or.inl (Or.inr h5)
  exact hpoint i hi

theorem low_separator_local_budget (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U v R K : Nat) (hv : v=1 ∨ v=2) (hR : 1≤R)
    (hzero : M+L+U=h+m+s) (hs : 1≤s) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤v+2 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  have hvpos : 1≤v := by omega
  have hv2 : v≤2 := by omega
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF (List.replicate h false++x)=h+m+s := by
    have hc:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=h+M+m+L+s+U := by
      simp only [x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hc
    omega
  have hBx : runKey (List.replicate h false++x)= -2*B := by
    simpa only [x,List.append_assoc] using hB
  have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true → P i ∨ Q i ∨ (v=2 ∧ D i) := by
    intro i hi
    rcases (local_fourth_sources h M m L s U v i hvpos).mp hi with h0|h1|h2|h3|h4|h5
    · have hn:=Recaman.LowSeparatorSources.low_separator_initial_source_excluded u x hu h v R i hv hR hmz
        (by rw [hBx,hSz]; simp only [Int.natCast_add]; omega)
      exact False.elim (hn (by simpa only [x,List.append_assoc] using h0))
    · exact False.elim (Recaman.LowSeparatorSources.low_separator_first_A_excluded u hu hcu h M m L s U v R i
        hv hzero hbudget B hB hkeyTarget h1)
    · exact Or.inr (Or.inl h2)
    · by_cases hvTwo : v=2
      · exact Or.inr (Or.inr ⟨hvTwo,h3⟩)
      · have hvOne : v=1 := by omega
        subst v
        obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        have hi2:=interior_A_one_gap_clock e s U i he hs
          (by simpa only [List.replicate_one,List.append_assoc] using hbal)
          (by simpa only [List.replicate_one,List.append_assoc] using hkey)
        exact Or.inl (Or.inr hi2)
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
      have hi02:=tail_S_small_gap_clock q U v i hq hvpos (by omega)
        (by simpa only [List.append_assoc] using hbal)
        (by simpa only [List.append_assoc] using hkey)
      exact Or.inl hi02
    · exact Or.inl (Or.inr h5)
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>P i ∨ Q i ∨ (v=2 ∧ D i)) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpoint i (by simpa only [List.append_assoc] using hi)
  have hP : cN P 0 K≤2 := zero_two_count K
  have hQ : cN Q 0 K≤1 := sourceAt_count_le_one false m _ K
  have hD : cN (fun i=>v=2 ∧ D i) 0 K≤v-1 := by
    by_cases hvTwo : v=2
    · have hh : cN (fun i=>v=2 ∧ D i) 0 K≤cN D 0 K := by
        apply cN_mono
        intro i _ _ hi
        exact hi.2
      have hd : cN D 0 K≤1 := sourceAt_count_le_one true L _ K
      omega
    · have hz : cN (fun i=>v=2 ∧ D i) 0 K=0 := by
        apply cN_zero_of
        intro i _ _ hi
        exact hvTwo hi.1
      rw [hz]
      omega
  have h1:=cN_or_le P (fun i=>Q i ∨ (v=2 ∧ D i)) K
  have h2:=cN_or_le Q (fun i=>v=2 ∧ D i) K
  omega

theorem low_separator_middle_source_bound (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U v R K : Nat) (hv : v=1 ∨ v=2) (hR : 1≤R)
    (hzero : M+L+U=h+m+s) (hs : 1≤s) (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤v+1+cN (sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)) 0 K := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  have hvpos : 1≤v := by omega
  have hv2 : v≤2 := by omega
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF (List.replicate h false++x)=h+m+s := by
    have hc:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=h+M+m+L+s+U := by
      simp only [x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hc
    omega
  have hBx : runKey (List.replicate h false++x)= -2*B := by
    simpa only [x,List.append_assoc] using hB
  have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true → P i ∨ Q i ∨ (v=2 ∧ D i) := by
    intro i hi
    rcases (local_fourth_sources h M m L s U v i hvpos).mp hi with h0|h1|h2|h3|h4|h5
    · have hn:=Recaman.LowSeparatorSources.low_separator_initial_source_excluded u x hu h v R i hv hR hmz
        (by rw [hBx,hSz]; simp only [Int.natCast_add]; omega)
      exact False.elim (hn (by simpa only [x,List.append_assoc] using h0))
    · exact False.elim (Recaman.LowSeparatorSources.low_separator_first_A_excluded u hu hcu h M m L s U v R i
        hv hzero hbudget B hB hkeyTarget h1)
    · exact Or.inr (Or.inl h2)
    · by_cases hvTwo : v=2
      · exact Or.inr (Or.inr ⟨hvTwo,h3⟩)
      · have hvOne : v=1 := by omega
        subst v
        obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        have hi2:=interior_A_one_gap_clock e s U i he hs
          (by simpa only [List.replicate_one,List.append_assoc] using hbal)
          (by simpa only [List.replicate_one,List.append_assoc] using hkey)
        exact Or.inl (Or.inr hi2)
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
      have hi02:=tail_S_small_gap_clock q U v i hq hvpos (by omega)
        (by simpa only [List.append_assoc] using hbal)
        (by simpa only [List.append_assoc] using hkey)
      exact Or.inl hi02
    · exact Or.inl (Or.inr h5)
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>P i ∨ Q i ∨ (v=2 ∧ D i)) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpoint i (by simpa only [List.append_assoc] using hi)
  have hP : cN P 0 K≤2 := zero_two_count K
  have hD : cN (fun i=>v=2 ∧ D i) 0 K≤v-1 := by
    by_cases hvTwo : v=2
    · have hh : cN (fun i=>v=2 ∧ D i) 0 K≤cN D 0 K := by
        apply cN_mono
        intro i _ _ hi
        exact hi.2
      have hd : cN D 0 K≤1 := sourceAt_count_le_one true L _ K
      omega
    · have hz : cN (fun i=>v=2 ∧ D i) 0 K=0 := by
        apply cN_zero_of
        intro i _ _ hi
        exact hvTwo hi.1
      rw [hz]
      omega
  have h1:=cN_or_le P (fun i=>Q i ∨ (v=2 ∧ D i)) K
  have h2:=cN_or_le Q (fun i=>v=2 ∧ D i) K
  omega

end Recaman.LowSeparatorLocalBudget
