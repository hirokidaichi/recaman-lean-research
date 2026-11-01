import Recaman.InitialSTargetOldPair

namespace Recaman.InitialSTargetTail

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.OldTargetMiddleCharge Recaman.InitialSTargetBounds
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Initial-S target: a final-band first-A source forces q>=j+1,
hence a stronger total-A budget. No bound on the real initial S length. -/
theorem first_A_tail_budget (q M m L s i T j e : Nat) (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    j+1≤q ∧ 2*(j+1)+(m+s)≤M+L+T := by
  have hp : 0≤(M : Int)-(e : Int)-(q : Int) := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm1 hmt
    omega
  have ht := source_key_before_gap
    (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T j hmt hat
  rw [runKey_five_runs] at ht
  have hke := runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append,Int.natCast_zero,Int.zero_add] at hke
  rw [hke] at hk1
  have hprod := Int.mul_nonneg hp (show 0≤(m : Int)+(s : Int) by omega)
  have hquad : ((j : Int)+1)^2-1≤(q : Int)^2 := by grind
  have hq : j+1≤q := by
    by_cases hh : j+1≤q
    · exact hh
    · have hp := Int.mul_nonneg (show 0≤(j : Int)-(q : Int) by omega)
        (show 0≤(j : Int)+(q : Int) by omega)
      grind
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmt
  exact ⟨hq,by omega⟩

private theorem small_S_first_A_clock (m L s i e : Nat)
    (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (he : 1≤e) (hb : m+s≤4)
    (hm1 : mass (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)+(i : Int)=1)
    (hk1 : runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)= -2) : i=2 := by
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

theorem local_tail_two_clock (h q M m L s i T j : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hj : 4≤j)
    (hband : T≤i+j) (hbudget : M+L+T≤j+10)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hlocal : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true) :
    twoClock m L s i=true := by
  have hc := thirdClock_sound h M m L s i hs hlocal
  simp only [thirdClock,decide_eq_true_eq] at hc
  simp only [twoClock,decide_eq_true_eq]
  rcases hc with hi|⟨hq',hqh',hquad⟩|⟨he,heM,heq⟩|hv
  · exact Or.inl hi
  · have ht := initial_S_target_equations q M m L s T j hM hm hmt hat
    let q' : Int := (i : Int)+(M : Int)+(L : Int)-(m : Int)-(s : Int)-1
    have hqq : (q : Int)≤q' := by dsimp [q']; omega
    have hp := Int.mul_nonneg (show 0≤q'-(q : Int) by omega)
      (show 0≤q'+(q : Int)+2*((m : Int)+(s : Int)) by dsimp [q']; omega)
    have hR := Int.mul_nonneg (show 0≤(j : Int) by omega) (show 0≤(j : Int)+2 by omega)
    dsimp [q'] at *
    grind
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
    have hb := first_A_tail_budget q M m L s i T j e.toNat (by omega) hband hmass hkey hmt hat
    exact Or.inl (small_S_first_A_clock m L s i e.toNat hm hL hs (by omega) (by omega) hmass hkey)
  · exact Or.inr hv

theorem local_tail_small_first (h q M m L s i T j : Nat)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hj : 4≤j)
    (hband : T≤i+j) (hbudget : M+L+T≤j+10) (hMj : M≤j)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hlocal : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true) : i=2 := by
  have hc := local_tail_two_clock h q M m L s i T j hM hm hL hs hj hband hbudget hmt hat hlocal
  simp only [twoClock,decide_eq_true_eq] at hc
  rcases hc with hi|hmid
  · exact hi
  · have hb := middle_clock_first_run [] BlockWord.nil q M m L s i T j (by omega) hband
      (by simpa only [List.nil_append] using hmt) (by simpa only [List.nil_append] using hat) hmid
    omega

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- Old suppliers remain as a real shared-prefix predicate and consume
at most one count. They are never replaced with a freely chosen tag. -/
theorem ray_band_with_old (w v : List Bool) (hw : BlockWord w) (hS : 3≤cntF v)
    (T j b : Nat) (Q : Nat → Prop) (hQ : cN Q 0 T≤b)
    (hlocal : ∀ i, i<T → T≤i+j →
      Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true → Q i) :
    rayCount (w++v) T≤T-j+(b+1) := by
  let O := fun i => tailOldRay w v i
  have ho : cN O 0 T≤1 := by
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    exact tailOldRay_clock_unique hw v hS i k hi hk
  have hbound := cN_or_le O Q T
  apply ray_count_band_bound (w++v) T j (b+1) (fun i => O i ∨ Q i) (by omega)
  intro i hi hb hh
  rcases (ray_supply_append_iff w v i).mp hh with hold|hl
  · exact Or.inl hold
  · exact Or.inr (hlocal i hi hb hl)

theorem initial_S_ray_bounds (w : List Bool) (hw : BlockWord w)
    (h q M m L s T j : Nat) (hqh : q≤h)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hj : 4≤j)
    (hbudget : M+L+T≤j+10)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    let v := List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false
    rayCount (w++v) T≤5 ∧ rayCount (w++v) T≤T-j+3 ∧
    (M≤j → rayCount (w++v) T≤T-j+2) ∧
    (M≤j → j+3≤T → rayCount (w++v) T≤T-j+1) ∧
    (T≤3 → L≤3 → rayCount (w++v) T≤T-j+2) := by
  dsimp only
  let v := List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false
  have ht := initial_S_target_equations q M m L s T j hM hm hmt hat
  have hS : 3≤cntF v := by
    simp only [v,cntF_append,cntF_replicate_S,cntF_A]
    omega
  have h2 (i : Nat) (hb : T≤i+j)
      (hl : Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true) :
      twoClock m L s i=true := by
    apply local_tail_two_clock h q M m L s i T j hM hm hL hs hj hb hbudget hmt hat
    simpa only [v,List.append_assoc] using hl
  have hsmall (hMj : M≤j) (i : Nat) (hb : T≤i+j)
      (hl : Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true) : i=2 := by
    apply local_tail_small_first h q M m L s i T j hM hm hL hs hj hb hbudget hMj hmt hat
    simpa only [v,List.append_assoc] using hl
  have hcount1 : cN (fun i : Nat => i=2) 0 T≤1 := by
    apply cN_le_one_of_unique
    intros
    omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · have ho := block_rayCount_append hw v hS T
    have hl := Recaman.MiddleSTargetFreeGap.third_ray_four_source_bound h M m L s T hs
    change rayCount v T≤4 at hl
    omega
  · exact ray_band_with_old w v hw hS T j 2 (fun i => twoClock m L s i=true)
      (twoClock_count_le_two m L s T) (by intro i _ hb hl; exact h2 i hb hl)
  · intro hMj
    exact ray_band_with_old w v hw hS T j 1 (fun i => i=2) hcount1
      (by intro i _ hb hl; exact hsmall hMj i hb hl)
  · intro hMj hT
    have hz : cN (fun _ => False) 0 T≤0 := Nat.le_of_eq (cN_zero_of (fun _ => False) 0 T (by intros; simp))
    apply ray_band_with_old w v hw hS T j 0 (fun _ => False) hz
    intro i hi hb hl
    have hi2 := hsmall hMj i hb hl
    omega
  · intro hT hL3
    apply ray_band_with_old w v hw hS T j 1 (fun i => i=2) hcount1
    intro i hi hb hl
    exact twoClock_short_small_L m L s i hs hL3 (by omega) (h2 i hb hl)

end Recaman.InitialSTargetTail
