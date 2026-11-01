import Recaman.FourthSourceFamilies

namespace Recaman.SmallInversionSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SourceFamilyFreeCount Recaman.FourthSourceFamilies

private theorem initial_numbers (q m s I : Int) (hq : 1≤q) (hm : 1≤m) (hs : 1≤s)
    (hI : I≤14) (he : (q+m+s)^2=2*I+1) :
    (q+m+s=3 ∧ I=4) ∨ (q+m+s=5 ∧ I=12) := by
  have hlo : 3≤q+m+s := by omega
  have hhi : q+m+s≤5 := by
    by_cases hh : q+m+s≤5
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤q+m+s-6 by omega) (show 0≤q+m+s+6 by omega)
      grind only
  have hc : q+m+s=3 ∨ q+m+s=4 ∨ q+m+s=5 := by omega
  rcases hc with hh|hh|hh <;> rw [hh] at he <;> omega

private theorem first_A_numbers (M m L s e i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (he : 1≤e) (heM : e≤M) (hi : 0≤i)
    (hI : M*(m+s)+L*s≤14) (hbal : e+L-m-s+i=1)
    (hkey : 2*e*(m+s)+2*L*s=(m+s)^2-1) :
    i=2 ∨ (M=2 ∧ m=3 ∧ L=1 ∧ s=2 ∧ i=3) := by
  have hLs1:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hL1s:=Int.mul_nonneg (show 0≤L by omega) (show 0≤s-1 by omega)
  have hLs : 1≤L*s := by grind only
  have hMe:=Int.mul_nonneg (show 0≤M-e by omega) (show 0≤m+s by omega)
  have hb5 : m+s≤5 := by
    by_cases hh : m+s≤5
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤m+s-6 by omega) (show 0≤m+s+6 by omega)
      grind only
  have hb : m+s=2 ∨ m+s=3 ∨ m+s=4 ∨ m+s=5 := by omega
  rcases hb with hb|hb|hb|hb
  · rw [hb] at hkey
    omega
  · rw [hb] at hkey hI
    have he1 : e=1 := by omega
    have hLsval : L*s=1 := by rw [he1] at hkey; omega
    have hLval : L=1 := by grind only
    have hsval : s=1 := by grind only
    left
    omega
  · rw [hb] at hkey
    omega
  · rw [hb] at hkey hI
    have hev : e=1 ∨ e=2 := by omega
    rcases hev with rfl|rfl
    · have hs4 : s≤4 := by omega
      have hL5 : L≤5 := by omega
      have hsv : s=1 ∨ s=2 ∨ s=3 ∨ s=4 := by omega
      rcases hsv with rfl|rfl|rfl|rfl <;> omega
    · have hLsval : L*s=2 := by omega
      have hL2 : L≤2 := by grind only
      have hs2 : s≤2 := by grind only
      have hM2 : M=2 := by omega
      have hLv : L=1 ∨ L=2 := by omega
      rcases hLv with rfl|rfl
      · right
        exact ⟨hM2,by omega,rfl,by omega,by omega⟩
      · left
        omega

private theorem second_S_numbers (M m L s q i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hq : 1≤q) (hqm : q≤m)
    (hI : M*(m+s)+L*s≤14) (hbal : L-q-s+i=1)
    (hkey : (q+s)^2=2*L*s+1) :
    i=2 ∨ (L=4 ∧ s=1 ∧ 2≤m ∧ i=0) := by
  have hMpos:=Int.mul_nonneg (show 0≤M-1 by omega) (show 0≤m+s by omega)
  have hLs1:=Int.mul_nonneg (show 0≤L-1 by omega) (show 0≤s by omega)
  have hL1s:=Int.mul_nonneg (show 0≤L by omega) (show 0≤s-1 by omega)
  have hLs : 1≤L*s := by grind only
  have hLs12 : L*s≤12 := by grind only
  have hQ5 : q+s≤5 := by
    by_cases hh : q+s≤5
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤q+s-6 by omega) (show 0≤q+s+6 by omega)
      grind only
  have hQ : q+s=2 ∨ q+s=3 ∨ q+s=4 ∨ q+s=5 := by omega
  have hQ3 : q+s=3 := by
    rcases hQ with h|h|h|h
    · rw [h] at hkey; omega
    · exact h
    · rw [h] at hkey; omega
    · rw [h] at hkey
      have hLsval : L*s=12 := by omega
      have hms : m+s≤2 := by grind only
      have hm1 : m=1 := by omega
      have hs1 : s=1 := by omega
      omega
  have hLsval : L*s=4 := by rw [hQ3] at hkey; omega
  have hs4 : s≤4 := by grind only
  have hsv : s=1 ∨ s=2 ∨ s=3 ∨ s=4 := by omega
  rcases hsv with rfl|rfl|rfl|rfl
  · right
    exact ⟨by omega,rfl,by omega,by omega⟩
  · left
    omega
  · omega
  · omega

private theorem initial_with_second_zero (q M m L s i : Int)
    (hq : 1≤q) (hM : 1≤M) (hm : 2≤m) (hL : L=4) (hs : s=1)
    (hI : M*(m+s)+L*s≤14)
    (hbal : M+L-q-m-s+i=1)
    (hkey : (q+m+s)^2=2*(M*(m+s)+L*s)+1) : i=0 := by
  subst L
  subst s
  have hv:=initial_numbers q m 1 (M*(m+1)+4) hq (by omega) (by decide) hI hkey
  have hp:=Int.mul_nonneg (show 0≤M-1 by omega) (show 0≤m+1 by omega)
  rcases hv with hv|hv
  · grind only
  · have hm3 : m≤3 := by omega
    have hmv : m=2 ∨ m=3 := by omega
    rcases hmv with rfl|rfl <;> omega

theorem small_inversion_first_A (M m L s i : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤14)
    (he : sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false) i) :
    i=2 ∨ (M=2 ∧ m=3 ∧ L=1 ∧ s=2 ∧ i=3) := by
  obtain ⟨e,he,heM,hbal,hkey⟩:=he
  have hk:=runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append] at hk
  rw [hk] at hkey
  simp only [Int.natCast_zero,Int.zero_add] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
  have hc:=first_A_numbers (M : Int) (m : Int) (L : Int) (s : Int) (e : Int) (i : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hI
    (by omega) (by grind only)
  rcases hc with hc|hc
  · left; omega
  · right; omega

theorem small_inversion_second_S (M m L s i : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤14)
    (he : sourceAt false m (List.replicate L true++List.replicate s false) i) :
    i=2 ∨ (L=4 ∧ s=1 ∧ 2≤m ∧ i=0) := by
  obtain ⟨q,hq,hqm,hbal,hkey⟩:=he
  rw [runKey_S_A_S] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
  have hc:=second_S_numbers (M : Int) (m : Int) (L : Int) (s : Int) (q : Int) (i : Int)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hI
    (by omega) (by grind only)
  rcases hc with hc|hc
  · left; omega
  · right; omega

end Recaman.SmallInversionSources
