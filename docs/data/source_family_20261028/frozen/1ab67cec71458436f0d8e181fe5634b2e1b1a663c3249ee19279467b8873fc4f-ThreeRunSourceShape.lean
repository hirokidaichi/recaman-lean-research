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

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- Original-base free-gap under the small budget derived for a genuine
    counterexample. The supplied target's same first-A window is essential. -/
theorem first_A_target_free_bounded (f : Nat → Bool) (n h M d m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hs : 1≤s) (hbudget : M+L+T≤20) (hj : 4≤j)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos2 : cN (EndN f 0) n (h+M+m+L)+1≤cN (fun x => f x=false) n (h+M+m+L))
    (hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+M+m+L+s+T) := by
  let P := fun i => f i=true ∧ ¬EndN f 0 i
  have ha1 : seg f (n+h) M=List.replicate M true := by
    apply seg_A
    intro x hx hxM
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+h)) (by omega)
  have ha2 : seg f (n+h+M+m) L=List.replicate L true := by
    apply seg_A
    intro x hx hxL
    simpa only [Nat.add_sub_cancel' hx] using hA2 (x-(n+h+M+m)) (by omega)
  have hp2 : seg f 0 (n+h+M+m)=
      w++(List.replicate h false++List.replicate M true++List.replicate m false) := by
    rw [seg_add,show 0+(n+h+M)=n+h+M by omega,seg_false f (n+h+M) m hS2,
      seg_add,show 0+(n+h)=n+h by omega,ha1,
      seg_add,show 0+n=n by omega,hpre,seg_false f n h hS]
    simp only [List.append_assoc]
  have hp3 : seg f 0 (n+h+M+m+L+s)=
      w++(List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false) := by
    rw [seg_add,show 0+(n+h+M+m+L)=n+h+M+m+L by omega,seg_false f (n+h+M+m+L) s hS3,
      seg_add,show 0+(n+h+M+m)=n+h+M+m by omega,ha2,hp2]
    simp only [List.append_assoc]
  have he2 := endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  have he3 := endable_A_run_count f (n+h+M+m+L+s) T _ hp3 hA3
  have hb2 : cN (EndN f 0) (n+h+M+m) L≤3 := by
    by_cases hSsum : 3≤h+m
    · have hcount : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false) := by
        simp only [cntF_append,cntF_replicate_S,cntF_A]
        omega
      have ho := block_rayCount_append hw _ hcount L
      have hl := rayCount_S_A_S h M m L
      omega
    · have hword2 := Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0
        hS hA hS2 hA2 (by intro x hx hx0; omega) (by intro i hi; omega)
      have hcS := cntF_seg f n (h+M+m+L)
      have hcSeq : cN (fun x => f x=false) n (h+M+m+L)=h+m := by
        have hword : seg f n (h+M+m+L)=
            List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true := by
          simpa using hword2
        rw [hword,cntF_append,cntF_append,cntF_append,cntF_replicate_S,cntF_replicate_S,cntF_A,cntF_A] at hcS
        omega
      have hc := cN_add (EndN f 0) n (h+M+m) L
      rw [hcSeq] at hpos2
      simp only [Nat.add_assoc] at *
      omega
  have htarget := first_A_target_equations d m L s T j hd hm hmass harea
  have hcS3 : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A]
    omega
  have ho3 := block_rayCount_append hw _ hcS3 T
  have hl3 := first_A_target_third_ray_count h M d m L s T j T hd hdM hm hs hbudget hj hmass harea
  have hb3 : cN (EndN f 0) (n+h+M+m+L+s) T≤4 := by omega
  have hfirst0 : P (n+h+0) := ⟨hA 0 (by omega),
    first_two_A_not_supplied f n h M w hw hpre hS hA 0 (by omega) (by omega)⟩
  have hc0 := cN_succ_pos P (n+h) 0 hfirst0
  have hprefix := count_prefix_le P (n+h) 1 M (by omega)
  have hfirst : 1≤cN P (n+h) M := by
    change cN P (n+h) 1=cN P (n+h) 0+1 at hc0
    omega
  have hpA2 := addition_endable_partition f (n+h+M+m) L
  have hpA3 := addition_endable_partition f (n+h+M+m+L+s) T
  rw [count_A_run f _ L hA2] at hpA2
  rw [count_A_run f _ T hA3] at hpA3
  change L=_+cN P (n+h+M+m) L at hpA2
  change T=_+cN P (n+h+M+m+L+s) T at hpA3
  have hlater := first_A_target_later_A d m L s T j hd hm hmass harea
  have hsum : j+1≤cN P (n+h) M+cN P (n+h+M+m) L+cN P (n+h+M+m+L+s) T := by omega
  have a := cN_add P n h M
  have b := cN_add P n (h+M) m
  have c := cN_add P n (h+M+m) L
  have d := cN_add P n (h+M+m+L) s
  have e := cN_add P n (h+M+m+L+s) T
  change j+1≤cN P n (h+M+m+L+s+T)
  simp only [Nat.add_assoc] at *
  omega

private theorem first_A_source_word (f : Nat → Bool) (n h M d m L s T j : Nat) (hdM : d≤M)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false) :
    seg f (n+h+M-d) (d+m+L+s+T+j)=
      List.replicate d true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate T true++List.replicate j false := by
  have hword := Recaman.SeparatorSupplyReset.three_run_word f (n+h+M-d) 0 d m L s T
    (by intro x hx hx0; omega)
    (by
      intro i hi
      have hh := hA (M-d+i) (by omega)
      simpa only [show n+h+(M-d+i)=n+h+M-d+0+i by omega] using hh)
    (by intro x hx hx1; exact hS2 x (by omega) (by omega))
    (by
      intro i hi
      simpa only [show n+h+M+m+i=n+h+M-d+0+d+m+i by omega] using hA2 i hi)
    (by intro x hx hx1; exact hS3 x (by omega) (by omega))
    (by
      intro i hi
      simpa only [show n+h+M+m+L+s+i=n+h+M-d+0+d+m+L+s+i by omega] using hA3 i hi)
  have hs := seg_false f ((n+h+M-d)+(d+m+L+s+T)) j
    (fun x hx hxj => hgap x (by omega) (by omega))
  rw [seg_add,hs]
  simpa using congrArg (fun v : List Bool => v++List.replicate j false) hword

/-- A genuine three-run free-gap counterexample cannot have a target
    source inside its first A run. No numerical free tag is an input. -/
theorem three_run_first_A_free_gap (f : Nat → Bool) (n h M d m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hs : 1≤s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hwin : Win f (n+h+M-d) (d+m+L+s+T+j)) :
    j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+M+m+L+s+T) := by
  by_cases hgood : j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+M+m+L+s+T)
  · exact hgood
  · have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
      (by omega) hpos hgap he (by omega)
    have hword := first_A_source_word f n h M d m L s T j hdM hA hS2 hA2 hS3 hA3 hgap
    have hmass : mass (List.replicate d true++List.replicate m false++List.replicate L true++
        List.replicate s false++List.replicate T true++List.replicate j false)=1 := by
      rw [←hword,seg_mass]
      have hh := hwin.2.1
      omega
    have harea : areaW (List.replicate d true++List.replicate m false++List.replicate L true++
        List.replicate s false++List.replicate T true++List.replicate j false)=0 := by
      rw [←hword,←Ar_areaW]
      exact hwin.2.2
    have hwhole := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
    have hc := ones_seg_eq_count f n (h+M+m+L+s+T)
    rw [hwhole] at hc
    simp only [ones_append,ones_replicate_S,ones_replicate_A] at hc
    exact first_A_target_free_bounded f n h M d m L s T j w hw hpre hd hdM hm hs
      (by omega) (by omega) hS hA hS2 hA2 hS3 hA3
      (hpos (h+M+m+L) (by omega) (by omega)) hmass harea

theorem three_run_first_A_free_gap_from_zero (f : Nat → Bool) (n h M d m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hs : 1≤s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hzero : cN (EndN f 0) 0 n=cN (fun x => f x=false) 0 n)
    (hpos : ∀ u, n<u → u≤n+h+M+m+L+s+T+j →
      cN (EndN f 0) 0 u+1≤cN (fun x => f x=false) 0 u)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hwin : Win f (n+h+M-d) (d+m+L+s+T+j)) :
    j+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+M+m+L+s+T) := by
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k := by
    intro k hk hkB
    have hp := hpos (n+k) (by omega) (by omega)
    have hE := cN_add (EndN f 0) 0 n k
    have hS := cN_add (fun x => f x=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  exact three_run_first_A_free_gap f n h M d m L s T j w hw hpre hd hdM hm hs
    hS hA hS2 hA2 hS3 hA3 hrel hgap he hwin

open Classical in
theorem three_run_first_A_free_gap_int (e : Int → Bool) (p : Int)
    (n a h M d m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hd : 1≤d) (hdM : d≤M) (hm : 1≤m) (hs : 1≤s)
    (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false)
    (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false)
    (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false)
    (hA3 : ∀ i, i<T → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ u, n<u → u≤n+h+M+m+L+s+T+j → endableCount e p u+1≤subtractionCount e p u)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → e (p+(x : Int))=false)
    (he : Endable e p (p+((n+h+M+m+L+s+T+j : Nat) : Int)))
    (hwindow : P2 (past e (p+((n+h+M+m+L+s+T+j : Nat) : Int)) (d+m+L+s+T+j))) :
    j+1≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [nonsupplied_count_shift]
  have hb := past_bridge e p (n+h+M-d) (d+m+L+s+T+j)
  rw [show (n+h+M-d)+(d+m+L+s+T+j)=n+h+M+m+L+s+T+j by omega] at hb
  have hW : Win (fun i => e (p+(i : Int))) (n+h+M-d) (d+m+L+s+T+j) := by
    refine ⟨by omega,?_,?_⟩
    · have hh := hwindow.1
      rw [hb.1] at hh
      rw [show (n+h+M-d)+(d+m+L+s+T+j)=n+h+M+m+L+s+T+j by omega]
      omega
    · exact hb.2.symm.trans hwindow.2
  apply three_run_first_A_free_gap_from_zero (fun i => e (p+(i : Int))) n h M d m L s T j
    (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre hd hdM hm hs
    hS hA hS2 hA2 hS3 hA3 hzero hpos hgap
  · exact (endable_iff e p p _ 0 (n+h+M+m+L+s+T+j) (by simp) rfl).mp he
  · exact hW

private theorem later_A_count_charge (f : Nat → Bool) (n h M m L s T U : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM : 1≤M) (hprior : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos2 : cN (EndN f 0) n (h+M+m+L)+1≤cN (fun x => f x=false) n (h+M+m+L))
    (hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T≤U) :
    L+T+1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+M+m+L+s+T)+(U+4) := by
  let P := fun i => f i=true ∧ ¬EndN f 0 i
  have ha1 : seg f (n+h) M=List.replicate M true := by
    apply seg_A
    intro x hx hxM
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+h)) (by omega)
  have ha2 : seg f (n+h+M+m) L=List.replicate L true := by
    apply seg_A
    intro x hx hxL
    simpa only [Nat.add_sub_cancel' hx] using hA2 (x-(n+h+M+m)) (by omega)
  have hp2 : seg f 0 (n+h+M+m)=
      w++(List.replicate h false++List.replicate M true++List.replicate m false) := by
    rw [seg_add,show 0+(n+h+M)=n+h+M by omega,seg_false f (n+h+M) m hS2,
      seg_add,show 0+(n+h)=n+h by omega,ha1,
      seg_add,show 0+n=n by omega,hpre,seg_false f n h hS]
    simp only [List.append_assoc]
  have hp3 : seg f 0 (n+h+M+m+L+s)=
      w++(List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false) := by
    rw [seg_add,show 0+(n+h+M+m+L)=n+h+M+m+L by omega,seg_false f (n+h+M+m+L) s hS3,
      seg_add,show 0+(n+h+M+m)=n+h+M+m by omega,ha2,hp2]
    simp only [List.append_assoc]
  have he2 := endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  have he3 := endable_A_run_count f (n+h+M+m+L+s) T _ hp3 hA3
  have hb2 : cN (EndN f 0) (n+h+M+m) L≤3 := by
    by_cases hSsum : 3≤h+m
    · have hcount : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false) := by
        simp only [cntF_append,cntF_replicate_S,cntF_A]
        omega
      have ho := block_rayCount_append hw _ hcount L
      have hl := rayCount_S_A_S h M m L
      omega
    · have hword2 := Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0
        hS hA hS2 hA2 (by intro x hx hx0; omega) (by intro i hi; omega)
      have hcS := cntF_seg f n (h+M+m+L)
      have hcSeq : cN (fun x => f x=false) n (h+M+m+L)=h+m := by
        have hword : seg f n (h+M+m+L)=
            List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true := by
          simpa using hword2
        rw [hword,cntF_append,cntF_append,cntF_append,cntF_replicate_S,cntF_replicate_S,cntF_A,cntF_A] at hcS
        omega
      have hc := cN_add (EndN f 0) n (h+M+m) L
      rw [hcSeq] at hpos2
      simp only [Nat.add_assoc] at *
      omega
  have hcS3 : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A]
    omega
  have ho3 := block_rayCount_append hw _ hcS3 T
  have hb3 : cN (EndN f 0) (n+h+M+m+L+s) T≤U+1 := by omega
  have hfirst0 : P (n+h+0) := ⟨hA 0 (by omega),
    first_two_A_not_supplied f n h M w hw hpre hS hA 0 (by omega) (by omega)⟩
  have hc0 := cN_succ_pos P (n+h) 0 hfirst0
  have hprefix := count_prefix_le P (n+h) 1 M (by omega)
  have hfirst : 1≤cN P (n+h) M := by
    change cN P (n+h) 1=cN P (n+h) 0+1 at hc0
    omega
  have hpA2 := addition_endable_partition f (n+h+M+m) L
  have hpA3 := addition_endable_partition f (n+h+M+m+L+s) T
  rw [count_A_run f _ L hA2] at hpA2
  rw [count_A_run f _ T hA3] at hpA3
  change L=_+cN P (n+h+M+m) L at hpA2
  change T=_+cN P (n+h+M+m+L+s) T at hpA3
  have hsum : L+T+1≤cN P (n+h) M+cN P (n+h+M+m) L+cN P (n+h+M+m+L+s) T+(U+4) := by omega
  have a := cN_add P n h M
  have b := cN_add P n (h+M) m
  have c := cN_add P n (h+M+m) L
  have d := cN_add P n (h+M+m+L) s
  have e := cN_add P n (h+M+m+L+s) T
  change L+T+1≤cN P n (h+M+m+L+s+T)+(U+4)
  simp only [Nat.add_assoc] at *
  omega

end Recaman.ThreeRunSourceShape
