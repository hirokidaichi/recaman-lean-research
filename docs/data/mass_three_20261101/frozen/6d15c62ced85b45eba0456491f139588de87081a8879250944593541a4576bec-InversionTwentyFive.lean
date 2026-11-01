import Recaman.SmallInversionJoint

namespace Recaman.InversionTwentyFive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.SmallInversionSources Recaman.FourthSourceFamilies Recaman.SourceFamilyFreeCount

private theorem second_numbers (M m L s q i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hq : 1≤q)
    (hi : 0≤i) (hiL : i<L) (hI : M*(m+s)+L*s≤25)
    (hbal : M+i=q+m+1) (hkey : (q+m)^2=2*(M*m)+1) :
    i=2 ∨ (M=4 ∧ m=1 ∧ i=0) ∨ (M=6 ∧ m=2 ∧ i=0) ∨ (M=3 ∧ m=4 ∧ i=3) := by
  have hp:=Int.mul_nonneg (show 0≤s-1 by omega) (show 0≤M+L by omega)
  have hbound : M*m+M+L≤25 := by grind only
  have hQ6 : q+m≤6 := by
    by_cases hh : q+m≤6
    · exact hh
    · have hn:=Int.mul_nonneg (show 0≤q+m-7 by omega) (show 0≤q+m+7 by omega)
      grind only
  have hv : q+m=2 ∨ q+m=3 ∨ q+m=4 ∨ q+m=5 ∨ q+m=6 := by omega
  have hQ : q+m=3 ∨ q+m=5 := by
    rcases hv with h|h|h|h|h <;> rw [h] at hkey <;> omega
  rcases hQ with hQ|hQ
  · have hMm : M*m=4 := by rw [hQ] at hkey; omega
    have hmv : m=1 ∨ m=2 := by omega
    rcases hmv with rfl|rfl <;> omega
  · have hMm : M*m=12 := by rw [hQ] at hkey; omega
    have hmv : m=1 ∨ m=2 ∨ m=3 ∨ m=4 := by omega
    rcases hmv with rfl|rfl|rfl|rfl <;> omega

theorem second_local_clock (h M m L s i : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤25)
    (hi : i<L) (he : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate i true)=true) :
    i=2 ∨ (M=4 ∧ m=1 ∧ i=0) ∨ (M=6 ∧ m=2 ∧ i=0) ∨ (M=3 ∧ m=4 ∧ i=3) := by
  have hc:=Recaman.RunClockClassifier.secondClock_sound h M m i hm he
  simp only [Recaman.RunClockClassifier.secondClock,decide_eq_true_eq] at hc
  rcases hc with hc|hc
  · exact Or.inl hc
  · have hn:=second_numbers (M : Int) (m : Int) (L : Int) (s : Int)
      ((i : Int)+(M : Int)-(m : Int)-1) (i : Int)
      (by omega) (by omega) (by omega) (by omega) hc.1 (by omega) (by omega)
      hI (by omega) (by grind only)
    rcases hn with hn|hn|hn|hn <;> omega

private theorem exceptional_initial (M m L s q i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hq : 1≤q) (hi : 0≤i)
    (hI : M*(m+s)+L*s≤25)
    (hex : (M=4 ∧ m=1 ∧ 3≤L) ∨ (M=6 ∧ m=2 ∧ 3≤L) ∨ (M=3 ∧ m=4 ∧ 4≤L))
    (hbal : M+L+i=q+m+s+1) (hkey : (q+m+s)^2=2*(M*(m+s)+L*s)+1) : False := by
  have hQ : 6≤q+m+s := by rcases hex with h|h|h <;> omega
  have hQ7 : q+m+s≤7 := by
    by_cases hh : q+m+s≤7
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤q+m+s-8 by omega) (show 0≤q+m+s+8 by omega)
      grind only
  have hv : q+m+s=6 ∨ q+m+s=7 := by omega
  have hI24 : M*(m+s)+L*s=24 := by rcases hv with h|h <;> rw [h] at hkey <;> omega
  rcases hex with ⟨rfl,rfl,hL3⟩|⟨rfl,rfl,hL3⟩|⟨rfl,rfl,hL4⟩
  · have hLv : L=3 ∨ L=4 := by omega
    rcases hLv with rfl|rfl <;> omega
  · omega
  · have hLv : L=4 ∨ L=5 := by omega
    rcases hLv with rfl|rfl <;> omega

private theorem exceptional_first (M m L s e i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (he : 1≤e) (hi : 0≤i)
    (hI : M*(m+s)+L*s≤25)
    (hex : (M=4 ∧ m=1 ∧ 3≤L) ∨ (M=6 ∧ m=2 ∧ 3≤L) ∨ (M=3 ∧ m=4 ∧ 4≤L))
    (hbal : e+L-m-s+i=1) (hkey : 2*(e*(m+s)+L*s)=(m+s)^2-1) : False := by
  rcases hex with ⟨rfl,rfl,hL3⟩|⟨rfl,rfl,hL3⟩|⟨rfl,rfl,hL4⟩
  · have hp:=Int.mul_nonneg (show 0≤L-3 by omega) (show 0≤s by omega)
    have hsv : s=1 ∨ s=2 ∨ s=3 := by grind only
    rcases hsv with rfl|rfl|rfl <;> omega
  · have hp:=Int.mul_nonneg (show 0≤L-3 by omega) (show 0≤s by omega)
    have hs1 : s=1 := by grind only
    subst s
    omega
  · have hp:=Int.mul_nonneg (show 0≤L-4 by omega) (show 0≤s by omega)
    have hs1 : s=1 := by grind only
    subst s
    omega

private theorem exceptional_second (M m L s q i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hq : 1≤q) (hqm : q≤m) (hi : 0≤i)
    (hI : M*(m+s)+L*s≤25)
    (hex : (M=4 ∧ m=1 ∧ 3≤L) ∨ (M=6 ∧ m=2 ∧ 3≤L) ∨ (M=3 ∧ m=4 ∧ 4≤L))
    (hbal : L-q-s+i=1) (hkey : (q+s)^2=2*(L*s)+1) : i=0 ∨ i=2 := by
  rcases hex with ⟨rfl,rfl,hL3⟩|⟨rfl,rfl,hL3⟩|⟨rfl,rfl,hL4⟩
  · have hq1 : q=1 := by omega
    subst q
    have hp:=Int.mul_nonneg (show 0≤L-3 by omega) (show 0≤s by omega)
    have hsv : s=1 ∨ s=2 ∨ s=3 := by grind only
    rcases hsv with rfl|rfl|rfl <;> omega
  · have hp:=Int.mul_nonneg (show 0≤L-3 by omega) (show 0≤s by omega)
    have hs1 : s=1 := by grind only
    subst s
    have hqv : q=1 ∨ q=2 := by omega
    rcases hqv with rfl|rfl <;> omega
  · have hp:=Int.mul_nonneg (show 0≤L-4 by omega) (show 0≤s by omega)
    have hs1 : s=1 := by grind only
    subst s
    have hqv : q=1 ∨ q=2 ∨ q=3 ∨ q=4 := by omega
    rcases hqv with rfl|rfl|rfl|rfl <;> omega

theorem exceptional_third_two (h M m L s K : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤25)
    (hex : (M=4 ∧ m=1 ∧ 3≤L) ∨ (M=6 ∧ m=2 ∧ 3≤L) ∨ (M=3 ∧ m=4 ∧ 4≤L)) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) K≤2 := by
  have hx : ((M : Int)=4 ∧ (m : Int)=1 ∧ 3≤(L : Int)) ∨
      ((M : Int)=6 ∧ (m : Int)=2 ∧ 3≤(L : Int)) ∨
      ((M : Int)=3 ∧ (m : Int)=4 ∧ 4≤(L : Int)) := by rcases hex with h|h|h <;> omega
  have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true → i=0 ∨ i=2 := by
    intro i hi
    rcases (local_third_sources h M m L s i hs).mp hi with ha|ha|ha|ha
    · obtain ⟨q,hq,_,hbal,hkey⟩:=ha
      have hk : runKey (List.replicate q false++List.replicate M true++List.replicate m false++
          List.replicate L true++List.replicate s false)= -2 := by simpa only [List.append_assoc] using hkey
      rw [runKey_five_runs] at hk
      simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
      exact False.elim (exceptional_initial (M : Int) (m : Int) (L : Int) (s : Int) (q : Int) (i : Int)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hI hx (by omega) (by grind only))
    · obtain ⟨e,he,_,hbal,hkey⟩:=ha
      have hk:=runKey_five_runs 0 e m L s
      simp only [List.replicate_zero,List.nil_append] at hk
      simp only [List.append_assoc] at hk hkey
      rw [hk] at hkey
      simp only [Int.natCast_zero,Int.zero_add] at hkey
      simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
      exact False.elim (exceptional_first (M : Int) (m : Int) (L : Int) (s : Int) (e : Int) (i : Int)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hI hx (by omega) (by grind only))
    · obtain ⟨q,hq,hqm,hbal,hkey⟩:=ha
      have hk : runKey (List.replicate q false++List.replicate L true++List.replicate s false)= -2 := by
        simpa only [List.append_assoc] using hkey
      rw [runKey_S_A_S] at hk
      simp only [mass_append,mass_rep_false,mass_replicate_A] at hbal
      have hc:=exceptional_second (M : Int) (m : Int) (L : Int) (s : Int) (q : Int) (i : Int)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hI hx (by omega) (by grind only)
      omega
    · exact Or.inr ha
  have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) K≤cN (fun i=>i=0 ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpoint i hi
  have hb:=zero_two_count K
  omega

theorem joint_count_four (h M m L s K : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hI : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)≤25) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L+
      rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false) K≤4 := by
  by_cases hex : (M=4 ∧ m=1 ∧ 3≤L) ∨ (M=6 ∧ m=2 ∧ 3≤L) ∨ (M=3 ∧ m=4 ∧ 4≤L)
  · have ha:=rayCount_S_A_S h M m L
    have hb:=exceptional_third_two h M m L s K hM hm hL hs hI hex
    omega
  · have ha : rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤1 := by
      apply cN_le_one_of_unique
      intro a haL b hbL haP hbP
      have ca:=second_local_clock h M m L s a hM hm hL hs hI haL haP
      have cb:=second_local_clock h M m L s b hM hm hL hs hI hbL hbP
      rcases ca with ca|ca|ca|ca <;> rcases cb with cb|cb|cb|cb <;> omega
    have hb:=small_inversion_third_local_three h M m L s K hM hm hL hs (by omega)
    omega

end Recaman.InversionTwentyFive
