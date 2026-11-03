import Recaman.RunClockClassifier
import Recaman.BlockOldRay

namespace Recaman.KFiveHeadSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.RunClockClassifier

theorem K_five_bounds (M m L s : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hK : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5) :
    M≤2 ∧ m+s≤4 ∧ (L : Int)*(s : Int)≤3 ∧ M+L≤4 ∧ s≤2 ∧ (M : Int)*(m : Int)≤3 := by
  have hp:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int) by omega)
  have hq:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)-2 by omega)
  have hr:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
  have hu:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(s : Int) by omega)
  have hv:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
  have hw:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int) by omega)
  grind only

private theorem no_small_odd_square (x A : Int) (hx : 2≤x) (hA1 : 1≤A) (hA3 : A≤3)
    (he : x^2=2*A+1) : False := by
  by_cases hx2 : x≤2
  · have hh : x=2 := by omega
    rw [hh] at he
    omega
  · have hp:=Int.mul_nonneg (show 0≤x-3 by omega) (show 0≤x+3 by omega)
    grind only

private theorem no_eleven (x : Int) (hx : 0≤x) (he : x^2=11) : False := by
  by_cases hx3 : x≤3
  · have hp:=Int.mul_nonneg (show 0≤3-x by omega) (show 0≤3+x by omega)
    grind only
  · have hp:=Int.mul_nonneg (show 0≤x-4 by omega) (show 0≤x+4 by omega)
    grind only

theorem second_only_two (h M m L s i : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hK : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5)
    (hi : secondClock h M m i=true) : i=2 := by
  have hb:=K_five_bounds M m L s hM hm hL hs hK
  simp only [secondClock,decide_eq_true_eq] at hi
  rcases hi with hi|hi
  · exact hi
  · have hp:=Int.mul_pos (show 0<(M : Int) by omega) (show 0<(m : Int) by omega)
    exact False.elim (no_small_odd_square ((i : Int)+(M : Int)-1) ((M : Int)*(m : Int)) (by omega) (by omega)
      hb.2.2.2.2.2 (by have he:=hi.2.2; grind only))

theorem third_only_two (h M m L s i : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hK : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5)
    (hi : thirdClock h M m L s i=true) : i=2 := by
  have hb:=K_five_bounds M m L s hM hm hL hs hK
  simp only [thirdClock,decide_eq_true_eq] at hi
  rcases hi with hi|hi|hi|hi
  · exact hi
  · exact False.elim (no_eleven ((i : Int)+(M : Int)+(L : Int)-1) (by omega) (by have he:=hi.2.2; grind only))
  · have hN : (m : Int)+(s : Int)=2 ∨ (m : Int)+(s : Int)=3 ∨ (m : Int)+(s : Int)=4 := by omega
    have he:=hi.2.2
    rcases hN with h2|h3|h4
    · rw [h2] at he
      grind only
    · rw [h3] at he hK
      grind only
    · rw [h4] at he
      grind only
  · have hp:=Int.mul_pos (show 0<(L : Int) by omega) (show 0<(s : Int) by omega)
    exact False.elim (no_small_odd_square ((i : Int)+(L : Int)-1) ((L : Int)*(s : Int)) (by omega) (by omega)
      hb.2.2.1 (by have he:=hi.2.2; grind only))

theorem second_old_excluded (w : List Bool) (hw : BlockWord w) (h M m L s i : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hS : h+m+s=7)
    (hK : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5) (hi : i<L) :
    ¬tailOldRay w (List.replicate h false++List.replicate M true++List.replicate m false) i := by
  have hb:=K_five_bounds M m L s hM hm hL hs hK
  rintro ⟨t,ht,hmt,hkt⟩
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hlo : -2≤runKey (w.drop t) := by have hh:=block_area_quadratic_lower hu; unfold runKey; omega
  let S : Int:=(h : Int)+(m : Int)
  have hS5 : 5≤S := by dsimp [S]; omega
  have hcfA : cntF (List.replicate M true)=0 := by
    have he:=mass_cntF (List.replicate M true)
    rw [mass_replicate_A,List.length_replicate] at he
    omega
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmt
  rw [runKey_S_A_S] at hkt
  simp only [cntF_append,cntF_replicate_S,hcfA] at hkt
  have hD : S-2≤mass (w.drop t) := by dsimp [S]; omega
  have hp:=Int.mul_nonneg (show 0≤mass (w.drop t)-(S-2) by omega) (show 0≤S by omega)
  have hq:=Int.mul_nonneg (show 0≤S-5 by omega) (show 0≤S+1 by omega)
  have hr:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int) by omega)
  simp only [Int.natCast_add] at hkt
  have hkt2 : runKey (w.drop t)+(4*(M : Int)*(m : Int)-2*S^2)+4*mass (w.drop t)*S= -2 := by dsimp [S]; grind only
  grind only

theorem second_ray_one (w : List Bool) (hw : BlockWord w) (h M m L s : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hS : h+m+s=7)
    (hK : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5) :
    rayCount (w++(List.replicate h false++List.replicate M true++List.replicate m false)) L≤1 := by
  unfold rayCount
  apply cN_le_one_of_unique
  intro i hi k hk hei hek
  have only (a : Nat) (ha : a<L)
      (he : Recaman.ThreeNonsuppliedData.localSupply
        ((w++(List.replicate h false++List.replicate M true++List.replicate m false))++List.replicate a true)=true) : a=2 := by
    rcases (ray_supply_append_iff w _ a).mp he with ho|hl
    · exact False.elim (second_old_excluded w hw h M m L s a hM hm hL hs hS hK ha ho)
    · exact second_only_two h M m L s a hM hm hL hs hK (secondClock_sound h M m a hm hl)
  have h1:=only i hi hei
  have h2:=only k hk hek
  omega

theorem third_ray_one (h M m L s U : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hK : (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)=5) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) U≤1 := by
  unfold rayCount
  apply cN_le_one_of_unique
  intro i hi k hk hei hek
  have h1:=third_only_two h M m L s i hM hm hL hs hK (thirdClock_sound h M m L s i hs hei)
  have h2:=third_only_two h M m L s k hM hm hL hs hK (thirdClock_sound h M m L s k hs hek)
  omega

end Recaman.KFiveHeadSources
