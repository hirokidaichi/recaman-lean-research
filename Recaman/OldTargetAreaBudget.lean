import Recaman.InitialSTargetBounds

namespace Recaman.OldTargetAreaBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount Recaman.ASourceReuse
open Recaman.InitialSTargetBounds
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- The old source carries its mass and area together. The positive area
    of that same BlockWord makes the half-A bound strict. -/
theorem old_target_word_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s T j : Nat)
    (hmass : mass (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false))=1)
    (harea : areaW (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false))=0) :
    mass u=(h : Int)+(m : Int)+(s : Int)+(j : Int)+1-((M : Int)+(L : Int)+(T : Int)) ∧
    2*areaW u+mass u*(mass u-1)=
      2*((M : Int)+(L : Int)+(T : Int))*((M : Int)+(L : Int)+(T : Int)-2*((j : Int)+1))-
        4*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) ∧
    (mass u)^2+2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))≤
      ((M : Int)+(L : Int)+(T : Int))*((M : Int)+(L : Int)+(T : Int)-2*((j : Int)+1))+1 ∧
    2*(j+1)+1≤M+L+T := by
  let A : Int := (M : Int)+(L : Int)+(T : Int)
  let H : Int := (h : Int)+(m : Int)+(s : Int)
  let R : Int := (j : Int)+1
  let I : Int := (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  let v := List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false
  have hC : mass u=H+R-A := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
    dsimp [A,H,R]
    omega
  have hk := source_key_before_gap (u++v) T j
    (by simpa only [v,List.append_assoc] using hmass)
    (by simpa only [v,List.append_assoc] using harea)
  have hcS : (cntF v : Int)=H := by
    simp only [v,cntF_append,cntF_replicate_S,cntF_A,Int.natCast_add]
    dsimp [H]
    omega
  have hkv : runKey v=4*I-2*H^2 := by
    rw [runKey_five_runs]
    dsimp [I,H]
    grind
  rw [runKey_append,hkv,hcS] at hk
  have hid : 2*areaW u+mass u*(mass u-1)=2*A*(A-2*R)-4*I := by
    unfold runKey at hk
    dsimp [R] at *
    grind
  have hlow := block_area_quadratic_lower hu
  have hb : (mass u)^2+2*I≤A*(A-2*R)+1 := by grind
  obtain ⟨hCpos,hDpos⟩ := sufPos_block hu [] u rfl hne
  have hcp := Int.mul_nonneg (show 0≤mass u by omega) (show 0≤mass u-1 by omega)
  have hip : 0≤I := by
    have h1 := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have h2 := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int) by omega)
    dsimp [I]
    omega
  have ha : 2*R<A := by
    by_cases h : 2*R<A
    · exact h
    · have hp := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤A by dsimp [A]; omega)
        (show A-2*R≤0 by omega)
      grind
  exact ⟨hC,hid,hb,by dsimp [A,R] at ha; omega⟩

/-- The raw strict bound is sharp even with three nonempty A runs. This
    constructs P2 windows, not a free-gap or C1 counterexample. -/
theorem old_target_strict_bound_sharp (R : Nat) (hR : 3≤R) :
    let v := [true]++(List.replicate 3 false++List.replicate 1 true++
      List.replicate (R-2) false++List.replicate 1 true++List.replicate 1 false++
      List.replicate (2*R-1) true++List.replicate (R-1) false)
    mass v=1 ∧ areaW v=0 ∧ 1+1+(2*R-1)=2*R+1 := by
  let w := List.replicate 3 false++List.replicate 1 true++List.replicate (R-2) false++
    List.replicate 1 true++List.replicate 1 false
  have hcast1 : ((R-1 : Nat) : Int)=(R : Int)-1 := by omega
  have hcast2 : ((R-2 : Nat) : Int)=(R : Int)-2 := by omega
  have hcastT : ((2*R-1 : Nat) : Int)=2*(R : Int)-1 := by omega
  have hmass : mass ([true]++(w++List.replicate (2*R-1) true++List.replicate (R-1) false))=1 := by
    simp only [w,mass_append,mass_rep_false,mass_replicate_A,hcast1,hcast2,hcastT]
    have hu : mass ([true] : List Bool)=1 := by decide
    rw [hu]
    omega
  have hcS : cntF w=R+2 := by
    simp only [w,cntF_append,cntF_replicate_S,cntF_A]
    omega
  have hkw : runKey w= -2*((R : Int)+2)^2+4*(R : Int) := by
    rw [runKey_five_runs]
    simp only [hcast2]
    grind
  have hku : runKey ([true] : List Bool)=0 := by decide
  have hmu : mass ([true] : List Bool)=1 := by decide
  have hk : runKey ([true]++w)= -2*(R : Int)^2 := by
    rw [runKey_append,hku,hmu,hkw,hcS]
    simp only [Int.natCast_add]
    grind
  have hkfull : runKey (([true]++w)++List.replicate (2*R-1) true++List.replicate (R-1) false)=-2 := by
    rw [runKey_append_S,runKey_append_A,hk]
    simp only [mass_append,w,mass_rep_false,mass_replicate_A,hmu,hcast1,hcast2,hcastT]
    grind
  have har : areaW ([true]++(w++List.replicate (2*R-1) true++List.replicate (R-1) false))=0 := by
    have hkf : runKey ([true]++(w++List.replicate (2*R-1) true++List.replicate (R-1) false))=-2 := by
      simpa only [List.append_assoc] using hkfull
    unfold runKey at hkf
    rw [hmass] at hkf
    omega
  dsimp only
  exact ⟨hmass,har,by omega⟩

theorem actual_old_target_budget (f : Nat → Bool) (n t h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hword : seg f n (h+M+m+L+s+T+j)=
      List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) :
    BlockWord (seg f t (n-t)) ∧ 1≤mass (seg f t (n-t)) ∧
    mass (seg f t (n-t))=(h : Int)+(m : Int)+(s : Int)+(j : Int)+1-((M : Int)+(L : Int)+(T : Int)) ∧
    (mass (seg f t (n-t)))^2+2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))≤
      ((M : Int)+(L : Int)+(T : Int))*((M : Int)+(L : Int)+(T : Int)-2*((j : Int)+1))+1 ∧
    2*(j+1)+1≤M+L+T := by
  let u := seg f t (n-t)
  have hsplit := suffix_split f 0 n t (Nat.zero_le _) (by omega)
  have hu : BlockWord u := block_suffix hw (seg f 0 t) u (by
    simpa only [Nat.zero_add,Nat.sub_zero,hpre,u] using hsplit.symm)
  have hne : u≠[] := by
    intro he
    have hl := seg_length f t (n-t)
    change u.length=n-t at hl
    rw [he] at hl
    simp at hl
    omega
  have hwhole : seg f t (n-t+(h+M+m+L+s+T+j))=
      u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false) := by
    rw [seg_add,show t+(n-t)=n by omega,hword]
  have hmass : mass (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false))=1 := by
    rw [←hwhole,seg_mass]
    have hh := hwin.2.1
    rw [show t+(n-t+(h+M+m+L+s+T+j))=t+(n+h+M+m+L+s+T+j-t) by omega]
    omega
  have harea : areaW (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false))=0 := by
    rw [←hwhole,←Ar_areaW,show n-t+(h+M+m+L+s+T+j)=n+h+M+m+L+s+T+j-t by omega]
    exact hwin.2.2
  have hb := old_target_word_budget u hu hne h M m L s T j hmass harea
  have hc := (sufPos_block hu [] u rfl hne).1
  exact ⟨hu,hc,hb.1,hb.2.2.1,hb.2.2.2⟩

/-- The old-source remainder is much smaller than the earlier A20 band.
    The earlier prefix before this suffix is retained, not erased. -/
theorem old_target_counterexample_band (f : Nat → Bool) (n t h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hs : 1≤s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hB : 0<h+M+m+L+s+T)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1)
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)≤7 ∧
    M+L+T≤17 ∧ 4≤j ∧ j≤7 ∧ mass (seg f t (n-t))≤7 ∧
      h+m+s≤16 ∧ (seg f t (n-t)).length≤17 := by
  have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
    hB hpos hgap he hbad
  have hshape := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
  have hword : seg f n (h+M+m+L+s+T+j)=
      List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false := by
    rw [seg_add,show n+(h+M+m+L+s+T)=n+h+M+m+L+s+T by omega,
      seg_false f (n+h+M+m+L+s+T) j hgap,hshape]
  have ho := actual_old_target_budget f n t h M m L s T j w hw hpre ht hword hwin
  have hprior : 3≤h+m+s := by omega
  have hc10 := three_run_count_of_manyS f n h M m L s T w hw hpre hs hprior
    hS hA hS2 hA2 hS3 hA3 hpos
  have hcount := ones_seg_eq_count f n (h+M+m+L+s+T)
  rw [hshape] at hcount
  simp only [ones_append,ones_replicate_S,ones_replicate_A] at hcount
  have hp := addition_endable_partition f n (h+M+m+L+s+T)
  have hA17 : M+L+T≤17 := by omega
  have hj4 : 4≤j := by omega
  let A : Int := (M : Int)+(L : Int)+(T : Int)
  let C := mass (seg f t (n-t))
  have hip : 0≤(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int) := by
    have h1 := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have h2 := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int) by omega)
    omega
  have ha : 0≤A := by dsimp [A]; omega
  have h17 : A≤17 := by dsimp [A]; omega
  let R : Int := (j : Int)+1
  let E : Int := A-R
  have hE9 : E≤9 := by dsimp [E,A,R]; omega
  have hE0 : 0≤E := by dsimp [E,A,R]; omega
  have hpair := Int.mul_nonneg (show 0≤9-E by omega) (show 0≤9+E by omega)
  have hjp := Int.mul_nonneg (show 0≤R-5 by dsimp [R]; omega) (show 0≤R+5 by dsimp [R]; omega)
  have hC2 : C^2≤57 := by
    have hq := ho.2.2.2.1
    change C^2+_≤A*(A-2*R)+1 at hq
    dsimp [E] at hpair
    grind
  have hC7 : C≤7 := by
    by_cases hh : C≤7
    · exact hh
    · have hcp := Int.mul_nonneg (show 0≤C-8 by omega) (show 0≤C+8 by dsimp [C]; omega)
      grind
  have hdense := dense_of_block ho.1 [] (seg f t (n-t)) rfl
  have hcm := mass_cntF (seg f t (n-t))
  have hlen : (seg f t (n-t)).length≤17 := by
    dsimp [C] at hC7
    omega
  exact ⟨hr.1,by omega,hA17,hj4,by omega,hC7,by dsimp [C,E,A,R] at *; omega,hlen⟩

/-- All actual target sources are covered: old or initialS remain, while
    the firstA/middleS and later source cases have already been eliminated. -/
theorem three_run_counterexample_smaller_band (f : Nat → Bool) (n h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)≤7 ∧
      M+L+T≤17 ∧ 4≤j ∧ j≤7 := by
  have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
    (by omega) hpos hgap he hbad
  obtain ⟨t,k,ht0,htk,hW⟩ := he.2
  have hW' : Win f t (n+h+M+m+L+s+T+j-t) := by
    rw [show n+h+M+m+L+s+T+j-t=k by have hh:=hW.1; omega]
    exact hW
  have hbefore := Recaman.MiddleSTargetFreeGap.three_run_counterexample_source_before_first_A
    f n h M m L s T j t w hw hpre hM hm hL hs hS hA hS2 hA2 hS3 hA3 hpos hgap he hbad hW'
  by_cases ht : t<n
  · have hb := old_target_counterexample_band f n t h M m L s T j w hw hpre ht hs
      hS hA hS2 hA2 hS3 hA3 (by omega) hpos hgap he hbad hW'
    exact ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1⟩
  · let q := n+h-t
    have hWi : Win f (n+h-q) (q+M+m+L+s+T+j) := by
      rw [show n+h-q=t by dsimp [q]; omega,
        show q+M+m+L+s+T+j=n+h+M+m+L+s+T+j-t by dsimp [q]; omega]
      exact hW'
    have hb := initial_S_counterexample_pairs f n h q M m L s T j w hw hpre
      (by dsimp [q]; omega) (by dsimp [q]; omega) hM hm hL hs hT
      hS hA hS2 hA2 hS3 hA3 hpos hgap he hbad hWi
    rcases hb with hb|hb|hb|hb <;> omega

open Classical in
theorem three_run_counterexample_smaller_band_int (e : Int → Bool) (p : Int)
    (n a h M m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
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
    (hbad : countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T)<j+1) :
    4≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T) ∧
    countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T)≤7 ∧
      M+L+T≤17 ∧ 4≤j ∧ j≤7 := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  simp only [nonsupplied_count_shift] at hbad ⊢
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN (fun i => e (p+(i : Int))) 0) n k+1≤cN (fun i => e (p+(i : Int))=false) n k := by
    intro k hk hkB
    have hp := hpos (n+k) (by omega) (by omega)
    have hE := cN_add (EndN (fun i => e (p+(i : Int))) 0) 0 n k
    have hS := cN_add (fun i => e (p+(i : Int))=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  exact three_run_counterexample_smaller_band (fun i => e (p+(i : Int))) n h M m L s T j
    (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre hM hm hL hs hT
    hS hA hS2 hA2 hS3 hA3 hrel hgap
    ((endable_iff e p p _ 0 (n+h+M+m+L+s+T+j) (by simp) rfl).mp he) hbad

end Recaman.OldTargetAreaBudget
