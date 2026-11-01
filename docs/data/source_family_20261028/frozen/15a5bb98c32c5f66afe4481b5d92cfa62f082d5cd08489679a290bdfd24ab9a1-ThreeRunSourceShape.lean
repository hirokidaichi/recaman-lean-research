import Recaman.ASourceReuse
import Recaman.SourceFamilyFreeCount

namespace Recaman.ThreeRunSourceShape

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget
open Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount
open Recaman.ASourceReuse
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A target window starting in the first A run has a strictly larger
    internal S sum than j+1. All run lengths are quantified. -/
theorem first_A_target_equations (d m L s T j : Nat) (hd : 1≤d) (hm : 1≤m)
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    d+L+T=m+s+j+1 ∧
      2*(d : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
        ((m : Int)+(s : Int))^2-((j : Int)+1)^2 ∧ j+1<m+s := by
  have hkey := source_key_before_gap
    (List.replicate d true++List.replicate m false++List.replicate L true++List.replicate s false)
    T j hmass harea
  have he := runKey_five_runs 0 d m L s
  simp only [List.replicate_zero,List.nil_append] at he
  rw [he] at hkey
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hmass
  have hpos := Int.mul_pos (show 0<2*(d : Int) by omega)
    (show 0<(m : Int)+(s : Int) by omega)
  have hnonneg := Int.mul_nonneg (show 0≤2*(L : Int) by omega) (show 0≤(s : Int) by omega)
  have hs : j+1<m+s := by
    by_cases h : j+1<m+s
    · exact h
    · have hp := Int.mul_nonneg (show 0≤(j : Int)+1-((m : Int)+(s : Int)) by omega)
        (show 0≤(j : Int)+1+((m : Int)+(s : Int)) by omega)
      grind
  refine ⟨by omega,by grind,hs⟩

theorem first_A_target_residual (M d m L s T j : Nat) (hd : 1≤d) (hdM : d≤M)
    (hm : 1≤m) (hbudget : M+L+T≤20)
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    j+2≤m+s ∧ m+s+j+1≤20 ∧ j≤8 := by
  have he := first_A_target_equations d m L s T j hd hm hmass harea
  omega

/-- This is the same actual P2 window from the same sign sequence;
    the whole first block M may include signs before its source. -/
theorem actual_first_A_target_residual (f : Nat → Bool) (t M d m L s T j : Nat)
    (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hbudget : M+L+T≤20)
    (hword : seg f t (d+m+L+s+T+j)=
      List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)
    (hwin : Win f t (d+m+L+s+T+j)) :
    j+2≤m+s ∧ m+s+j+1≤20 ∧ j≤8 := by
  have hmass := seg_mass f t (d+m+L+s+T+j)
  have harea := Ar_areaW f t (d+m+L+s+T+j)
  rw [hword] at hmass harea
  exact first_A_target_residual M d m L s T j hd hdM hm hbudget
    (by rw [hmass]; have hh := hwin.2.1; omega) (by rw [←harea]; exact hwin.2.2)

/-- The second-S source has an even smaller A-free preceding context.
    Its target square and balance share exactly the same suffix. -/
theorem middle_S_target_equations (q L s T j : Nat) (hL : 1≤L) (hs : 1≤s)
    (hmass : mass (List.replicate q false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate q false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    L+T=q+s+j+1 ∧
      ((q : Int)+(s : Int))^2-((j : Int)+1)^2=2*(L : Int)*(s : Int) ∧ j+1<q+s := by
  have hkey := source_key_before_gap
    (List.replicate q false++List.replicate L true++List.replicate s false) T j hmass harea
  rw [runKey_S_A_S] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
  have hpos := Int.mul_pos (show 0<2*(L : Int) by omega) (show 0<(s : Int) by omega)
  have hqs : j+1<q+s := by
    by_cases h : j+1<q+s
    · exact h
    · have hp := Int.mul_nonneg (show 0≤(j : Int)+1-((q : Int)+(s : Int)) by omega)
        (show 0≤(j : Int)+1+((q : Int)+(s : Int)) by omega)
      grind
  exact ⟨by omega,by grind,hqs⟩

theorem first_A_target_later_A (d m L s T j : Nat) (hd : 1≤d) (hm : 1≤m)
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    2*(j+1)+1≤L+T := by
  have he := first_A_target_equations d m L s T j hd hm hmass harea
  have hdsmall : (d : Int)<(m : Int)+(s : Int)-((j : Int)+1) := by
    by_cases h : (d : Int)<(m : Int)+(s : Int)-((j : Int)+1)
    · exact h
    · have hp := Int.mul_nonneg
        (show 0≤(d : Int)-((m : Int)+(s : Int)-((j : Int)+1)) by omega)
        (show 0≤2*((m : Int)+(s : Int)) by omega)
      have hsq := Int.mul_pos
        (show 0<(m : Int)+(s : Int)-((j : Int)+1) by omega)
        (show 0<(m : Int)+(s : Int)-((j : Int)+1) by omega)
      have hls := Int.mul_nonneg (show 0≤2*(L : Int) by omega) (show 0≤(s : Int) by omega)
      grind
  omega

private theorem small_reuse_arithmetic (R K : Nat) (d e P : Int)
    (hR1 : 5≤R) (hR2 : R≤10) (hK1 : R<K) (hK2 : K+R≤20)
    (hkey : 2*d*(K : Int)+2*P=(K : Int)^2-(R : Int)^2)
    (hreuse : 2*(K : Int)*(e-d)=(R : Int)^2-1) : False := by
  have hRs : R=5 ∨ R=6 ∨ R=7 ∨ R=8 ∨ R=9 ∨ R=10 := by omega
  have hre : 2*((K : Int)*(e-d))=(R : Int)^2-1 := by grind
  rcases hRs with rfl|rfl|rfl|rfl|rfl|rfl
  · have hKs : K=6 ∨ K=7 ∨ K=8 ∨ K=9 ∨ K=10 ∨ K=11 ∨ K=12 ∨ K=13 ∨ K=14 ∨ K=15 := by omega
    rcases hKs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  · omega
  · have hKs : K=8 ∨ K=9 ∨ K=10 ∨ K=11 ∨ K=12 ∨ K=13 := by omega
    rcases hKs with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  · omega
  · have hKs : K=10 ∨ K=11 := by omega
    rcases hKs with rfl|rfl <;> omega
  · omega

/-- Under the derived counterexample budget, a target in the first A run
    prevents every earlier third-ray supply from that same A source run. -/
theorem first_A_target_excludes_ray_key (M d m L s T j e : Nat)
    (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hbudget : M+L+T≤20) (hj : 4≤j)
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    ¬runKey (List.replicate e true++List.replicate m false++List.replicate L true++
      List.replicate s false)=-2 := by
  intro hk
  have he := first_A_target_equations d m L s T j hd hm hmass harea
  have hb := first_A_target_residual M d m L s T j hd hdM hm hbudget hmass harea
  have hformula := runKey_five_runs 0 e m L s
  simp only [List.replicate_zero,List.nil_append] at hformula
  rw [hformula] at hk
  have hre : 2*((m : Int)+(s : Int))*((e : Int)-(d : Int))=((j : Int)+1)^2-1 := by grind
  apply small_reuse_arithmetic (j+1) (m+s) (d : Int) (e : Int) ((L : Int)*(s : Int))
    (by omega) (by omega) (by omega) (by omega)
  · simp only [Int.natCast_add,Int.natCast_one]
    grind
  · simpa only [Int.natCast_add,Int.natCast_one] using hre

private theorem A_S_key_impossible (e s : Nat) (he : 1≤e) (hs : 1≤s) :
    ¬runKey (List.replicate e true++List.replicate s false)=-2 := by
  intro hk
  rw [runKey_A_S] at hk
  have heq : (s : Int)*((s : Int)-2*(e : Int))=1 := by grind
  by_cases hn : (s : Int)-2*(e : Int)≤0
  · have hp := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(s : Int) by omega) hn
    omega
  · have hp := Int.mul_nonneg (show 0≤(s : Int) by omega)
      (show 0≤(s : Int)-2*(e : Int)-1 by omega)
    have hs1 : s=1 := by grind
    subst s
    simp at heq
    omega

private theorem rayCount_erase_const (b : Bool) (N : Nat) (v : List Bool) (K : Nat)
    (hn : ∀ e, 1≤e → e≤N → ¬runKey (List.replicate e b++v)=-2) :
    rayCount (List.replicate N b++v) K=rayCount v K := by
  unfold rayCount
  apply cN_congr
  intro i _ _
  rw [ray_supply_append_iff]
  constructor
  · rintro (ho|hl)
    · obtain ⟨t,ht,hm,hk⟩ := ho
      simp only [List.length_replicate] at ht
      have heq := runKey_append ((List.replicate N b).drop t) v
      rw [List.drop_replicate] at heq hk
      have hz : runKey (List.replicate (N-t) b++v)=-2 := by omega
      exact False.elim (hn (N-t) (by omega) (by omega) hz)
    · exact hl
  · exact Or.inr

private theorem rayCount_S_le_one (s K : Nat) : rayCount (List.replicate s false) K≤1 := by
  apply cN_le_one_of_unique
  intro i _ j _ hi hj
  have hi2 := (localSupply_three_runs_iff s i 0).mp (by simpa using hi)
  have hj2 := (localSupply_three_runs_iff s j 0).mp (by simpa using hj)
  omega

/-- The conditional deletion of an entire source run changes actual
    supply counts; it is not a repaired unconditional local-count guess. -/
theorem first_A_target_third_ray_count (h M d m L s T j K : Nat)
    (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hs : 1≤s) (hbudget : M+L+T≤20) (hj : 4≤j)
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) K≤3 := by
  have herase := rayCount_erase_const true M
    (List.replicate m false++List.replicate L true++List.replicate s false) K
    (fun e _ _ => by
      simpa only [List.append_assoc] using first_A_target_excludes_ray_key M d m L s T j e
        hd hdM hm hbudget hj hmass harea)
  have hlast := rayCount_erase_const true L (List.replicate s false) K
    (fun e he _ => A_S_key_impossible e s he hs)
  have hb0 := rayCount_S_le_one s K
  have hb1 := rayCount_const_append false m (List.replicate L true++List.replicate s false) K
  have hb2 := rayCount_const_append false h
    (List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false) K
  simp only [List.append_assoc] at *
  omega

end Recaman.ThreeRunSourceShape
