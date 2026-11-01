import Recaman.OldTargetLocalTail

namespace Recaman.OldTargetClockCollision

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- A first-A local source in the final band forces an extra m+s
A signs in the same old target's total A budget. No finite cutoff. -/
theorem first_A_tail_A_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s i T j e : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    2*(j+1)+(m+s)≤M+L+T := by
  let C := mass u
  let R : Int := (j : Int)+1
  let K : Int := (m : Int)+(s : Int)
  let v := List.replicate m false++List.replicate L true++List.replicate s false
  have hC : 1≤C := (sufPos_block hu [] u rfl hne).1
  have hlow := block_area_quadratic_lower hu
  have hku : -2≤runKey u := by unfold runKey; omega
  have hp : 0≤C-(h : Int)+(M : Int)-(e : Int) := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1 hm2
    dsimp [C]
    omega
  have hcnt : (cntF v : Int)=K := by
    simp only [v,cntF_append,cntF_replicate_S,cntF_A,Int.natCast_add]
    dsimp [K]
    omega
  have hk := source_key_before_gap
    (u++List.replicate h false++List.replicate M true++v) T j
    (by simpa only [v,List.append_assoc] using hm2)
    (by simpa only [v,List.append_assoc] using ha2)
  have hl : runKey (List.replicate e true++v)= -2 := by
    simpa only [v,List.append_assoc] using hk1
  rw [runKey_prepend_A,hcnt] at hl
  rw [runKey_append,runKey_append_A,runKey_append_S,hcnt] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hk
  have hnonneg := Int.mul_nonneg hp (show 0≤K by dsimp [K]; omega)
  have hquad : R^2-2≤(h : Int)*((h : Int)-2*C) := by
    dsimp [R,C] at *
    grind
  have hR : 3≤R := by dsimp [R]; omega
  have hhC : C≤(h : Int) := by
    by_cases hh : C≤(h : Int)
    · exact hh
    · have hn := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(h : Int) by omega)
        (show (h : Int)-2*C≤0 by omega)
      have hrr := Int.mul_nonneg (show 0≤R-3 by omega) (show 0≤R+3 by omega)
      grind
  have hhR : C+R≤(h : Int) := by
    by_cases hh : C+R≤(h : Int)
    · exact hh
    · have hp1 := Int.mul_nonneg (show 0≤R-1-((h : Int)-C) by omega)
        (show 0≤R-1+((h : Int)-C) by omega)
      have hp2 := Int.mul_nonneg (show 0≤C-1 by omega) (show 0≤C+1 by omega)
      grind
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm2
  dsimp [C,R] at hhR
  omega

theorem first_A_tail_clock_two (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s i T j e : Nat) (hj : 4≤j) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (he : 1≤e) (hband : T≤i+j) (hbudget : M+L+T≤j+10)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) : i=2 := by
  have hb := first_A_tail_A_budget u hu hne h M m L s i T j e (by omega) hband hm1 hk1 hm2 ha2
  have hK : m+s=2 ∨ m+s=3 ∨ m+s=4 := by omega
  have hkey := runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append] at hkey
  rw [hkey] at hk1
  have hLs := Int.mul_pos (show 0<(L : Int) by omega) (show 0<(s : Int) by omega)
  have heK := Int.mul_nonneg (show 0≤(e : Int)-1 by omega)
    (show 0≤(m : Int)+(s : Int) by omega)
  have heq : 2*(e : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
      ((m : Int)+(s : Int))^2-1 := by grind
  rcases hK with hK|hK|hK
  · have hc : (m : Int)+(s : Int)=2 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    have hn : 2*((2*(e : Int))+((L : Int)*(s : Int)))=3 := by grind
    omega
  · have hc : (m : Int)+(s : Int)=3 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    have hn : 6*(e : Int)+2*((L : Int)*(s : Int))=8 := by grind
    have he1 : e=1 := by omega
    have hLs1 : (L : Int)*(s : Int)=1 := by rw [he1] at hn; simp at hn; omega
    have hL1 : L=1 := by
      have hp := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)-1 by omega)
      grind
    have hs1 : s=1 := by rw [hL1] at hLs1; simp at hLs1; omega
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1
    omega
  · have hc : (m : Int)+(s : Int)=4 := by omega
    rw [hc] at heq
    simp only [Int.reducePow,Int.reduceSub] at heq
    have hn : 2*((4*(e : Int))+((L : Int)*(s : Int)))=15 := by grind
    omega

def twoClock (m L s i : Nat) : Bool :=
  let v : Int := (i : Int)+(L : Int)-(s : Int)-1
  decide (i=2 ∨ (1≤v ∧ v≤(m : Int) ∧ (v+(s : Int))^2=2*(L : Int)*(s : Int)+1))

theorem old_target_two_clock_sound (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s i T j : Nat) (hj : 4≤j) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hband : T≤i+j) (hbudget : M+L+T≤j+10)
    (hm2 : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hc : tailClock M m L s i=true) : twoClock m L s i=true := by
  simp only [tailClock,decide_eq_true_eq] at hc
  simp only [twoClock,decide_eq_true_eq]
  rcases hc with hi|⟨he,heM,heq⟩|hv
  · exact Or.inl hi
  · let e : Int := (m : Int)+(s : Int)+1-(L : Int)-(i : Int)
    have he0 : 0≤e := by dsimp [e]; omega
    have heN : (e.toNat : Int)=e := Int.toNat_of_nonneg he0
    have hmass : mass (List.replicate e.toNat true++List.replicate m false++List.replicate L true++
        List.replicate s false)+(i : Int)=1 := by
      simp only [mass_append,mass_rep_false,mass_replicate_A,heN]
      dsimp [e]
      omega
    have hkey : runKey (List.replicate e.toNat true++List.replicate m false++List.replicate L true++
        List.replicate s false)= -2 := by
      have hk := runKey_five_runs 0 e.toNat m L s
      simp only [List.replicate_zero,List.nil_append,heN,Int.natCast_zero,Int.zero_add] at hk
      rw [hk]
      grind
    exact Or.inl (first_A_tail_clock_two u hu hne h M m L s i T j e.toNat hj hm hL hs
      (by omega) hband hbudget hmass hkey hm2 ha2)
  · exact Or.inr hv

theorem twoClock_count_le_two (m L s T : Nat) :
    cN (fun i => twoClock m L s i=true) 0 T≤2 := by
  let P := fun i : Nat => i=2
  let V := fun i : Nat =>
    let v : Int := (i : Int)+(L : Int)-(s : Int)-1
    1≤v ∧ v≤(m : Int) ∧ (v+(s : Int))^2=2*(L : Int)*(s : Int)+1
  have hp : cN P 0 T≤1 := cN_le_one_of_unique P T (by intros; omega)
  have hv : cN V 0 T≤1 := by
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    dsimp [V] at hi hk
    have hz : ((i : Int)-(k : Int))*((i : Int)+(k : Int)+2*(L : Int)-2)=0 := by grind
    have hp : 0<(i : Int)+(k : Int)+2*(L : Int)-2 := by omega
    rcases Int.mul_eq_zero.mp hz with h|h <;> omega
  have hall := cN_or_le P V T
  have heq : cN (fun i => twoClock m L s i=true) 0 T=cN (fun i => P i ∨ V i) 0 T := by
    apply cN_congr
    intro i _ _
    simp only [twoClock,decide_eq_true_eq,P,V]
  omega

theorem full_old_target_two_clock (w : List Bool) (hw : BlockWord w)
    (t h M m L s i T j : Nat) (ht : t<w.length)
    (hj : 4≤j) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s)
    (hband : T≤i+j) (hbudget : M+L+T≤j+10)
    (hm2 : mass (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hc : Recaman.ThreeNonsuppliedData.localSupply
      (w++List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true) :
    twoClock m L s i=true := by
  have htail := full_old_target_tail_clock w hw t h M m L s i T j hs (by omega) hband hm2 ha2 hc
  have hu := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  exact old_target_two_clock_sound (w.drop t) hu (drop_nonempty w t ht)
    h M m L s i T j hj hm hL hs hband hbudget hm2 ha2 htail

private theorem cN_length_bound (P : Nat → Prop) (n : Nat) : ∀ K, cN P n K≤K
  | 0 => Nat.le_refl 0
  | K+1 => by have hh := cN_succ_le P n K; have ih := cN_length_bound P n K; omega

theorem full_old_target_ray_count_two (w : List Bool) (hw : BlockWord w)
    (t h M m L s T j : Nat) (ht : t<w.length)
    (hj : 4≤j) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hbudget : M+L+T≤j+10)
    (hm2 : mass (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    rayCount (w++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T≤T-j+2 := by
  let P := fun i => Recaman.ThreeNonsuppliedData.localSupply
    ((w++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)++List.replicate i true)=true
  let Q := fun i => twoClock m L s i=true
  have hp := cN_add P 0 (T-j) (T-(T-j))
  have hq := cN_add Q 0 (T-j) (T-(T-j))
  simp only [Nat.zero_add,show T-j+(T-(T-j))=T by omega] at hp hq
  have hmono : cN P (T-j) (T-(T-j))≤cN Q (T-j) (T-(T-j)) := by
    apply cN_mono
    intro i hi hiT hh
    exact full_old_target_two_clock w hw t h M m L s i T j ht hj hm hL hs (by omega)
      hbudget hm2 ha2 hh
  have hfirst := cN_length_bound P 0 (T-j)
  have hlast := twoClock_count_le_two m L s T
  change cN P 0 T≤T-j+2
  change cN Q 0 T≤2 at hlast
  omega

end Recaman.OldTargetClockCollision
