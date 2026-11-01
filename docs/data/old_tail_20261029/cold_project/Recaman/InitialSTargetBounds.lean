import Recaman.MiddleSTargetFreeGap

namespace Recaman.InitialSTargetBounds

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget
open Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount
open Recaman.ThreeRunSourceShape Recaman.MiddleSTargetFreeGap Recaman.ASourceReuse
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A bound on the A signs gives a one-sided dominance for local windows
    after an arbitrary S prefix. No old-window or EndN erasure is asserted. -/
theorem localSupply_S_prefix_domination (h H : Nat) (v : List Bool)
    (hbudget : ones v≤(H : Int)+1)
    (hs : Recaman.ThreeNonsuppliedData.localSupply (List.replicate h false++v)=true) :
    Recaman.ThreeNonsuppliedData.localSupply (List.replicate H false++v)=true := by
  rw [localSupply_iff] at hs ⊢
  let P := fun x : List Bool => mass x=1 ∧ Recaman.ThreeNonsuppliedData.wordArea x=0
  have hh : (∃ t, t<(List.replicate h false++v).length ∧ P ((List.replicate h false++v).drop t)) := hs
  rw [exists_drop_append] at hh
  rcases hh with ⟨t,ht,hm,ha⟩|⟨t,ht,hm,ha⟩
  · simp only [List.length_replicate,List.drop_replicate,mass_append,mass_rep_false] at ht hm ha
    have hmV := mass_eq v
    have hv := ones_bounds v
    have hqH : h-t≤H := by omega
    refine ⟨H-(h-t),?_,?_,?_⟩
    · simp only [List.length_append,List.length_replicate]
      omega
    · rw [List.drop_append,List.drop_replicate,List.length_replicate,
        show H-(h-t)-H=0 by omega,List.drop_zero,
        show H-(H-(h-t))=h-t by omega,mass_append,mass_rep_false]
      exact hm
    · rw [List.drop_append,List.drop_replicate,List.length_replicate,
        show H-(h-t)-H=0 by omega,List.drop_zero,
        show H-(H-(h-t))=h-t by omega]
      exact ha
  · have hd : (List.replicate H false++v).drop (H+t)=v.drop t := by
      rw [List.drop_append,List.drop_replicate,List.length_replicate,
        show H-(H+t)=0 by omega,List.replicate_zero,List.nil_append,
        show H+t-H=t by omega]
    refine ⟨H+t,by simp only [List.length_append,List.length_replicate]; omega,?_,?_⟩
    · simpa only [hd] using hm
    · simpa only [hd] using ha

theorem rayCount_S_prefix_domination (h H : Nat) (v : List Bool) (K : Nat)
    (hbudget : ones v+(K : Int)≤(H : Int)+2) :
    rayCount (List.replicate h false++v) K≤rayCount (List.replicate H false++v) K := by
  unfold rayCount
  apply cN_mono
  intro i _ hi hs
  have hb : ones (v++List.replicate i true)≤(H : Int)+1 := by
    rw [ones_append,ones_replicate_A]
    omega
  simpa only [List.append_assoc] using localSupply_S_prefix_domination h H
    (v++List.replicate i true) hb (by simpa only [List.append_assoc] using hs)

theorem initial_S_target_equations (q M m L s T j : Nat) (hM : 1≤M) (hm : 1≤m)
    (hmass : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    M+L+T=q+m+s+j+1 ∧
    ((q : Int)+(m : Int)+(s : Int))^2-((j : Int)+1)^2=
      2*(M : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int) ∧
    j+2<q+m+s ∧ 2*(j+1)+2≤M+L+T := by
  have hkey := source_key_before_gap
    (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T j hmass harea
  rw [runKey_five_runs] at hkey
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
  have hpos := Int.mul_pos (show 0<2*(M : Int) by omega) (show 0<(m : Int)+(s : Int) by omega)
  have hnonneg := Int.mul_nonneg (show 0≤2*(L : Int) by omega) (show 0≤(s : Int) by omega)
  have hgreater : j+1<q+m+s := by
    by_cases h : j+1<q+m+s
    · exact h
    · have hp := Int.mul_nonneg (show 0≤(j : Int)+1-((q : Int)+(m : Int)+(s : Int)) by omega)
        (show 0≤(j : Int)+1+((q : Int)+(m : Int)+(s : Int)) by omega)
      grind
  have heq : ((q : Int)+(m : Int)+(s : Int))^2-((j : Int)+1)^2=
      2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) := by grind
  have hne : q+m+s≠j+2 := by
    intro hh
    have hi : (q : Int)+(m : Int)+(s : Int)=(j : Int)+2 := by omega
    have hid : ((j : Int)+2)^2-((j : Int)+1)^2=2*(j : Int)+3 := by grind
    rw [hi,hid] at heq
    omega
  exact ⟨by omega,by grind,by omega,by omega⟩

theorem S_prefix_domination_boundary :
    Recaman.ThreeNonsuppliedData.localSupply ([false]++[true,true])=true ∧
      Recaman.ThreeNonsuppliedData.localSupply ([]++[true,true])=false := by decide

private theorem square_mod_two (x : Int) : x^2%2=x%2 := by
  have hm := Int.mul_emod x x 2
  rw [show x^2=x*x by grind]
  rcases Int.emod_two_eq x with h|h <;> simpa [h] using hm

theorem initial_S_target_even_A (q M m L s T j : Nat) (hM : 1≤M) (hm : 1≤m)
    (hmass : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    (M+L+T)%2=0 := by
  have he := initial_S_target_equations q M m L s T j hM hm hmass harea
  have hkey : ((q : Int)+(m : Int)+(s : Int))^2-((j : Int)+1)^2=
      2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) := by
    have hh := he.2.1
    grind
  have hmod : (((q : Int)+(m : Int)+(s : Int))^2-((j : Int)+1)^2)%2=0 := by
    rw [hkey]
    exact Int.mul_emod_right 2 _
  rw [Int.sub_emod,square_mod_two,square_mod_two] at hmod
  omega

/-- Once the known source-count upper bound is used, only four small
    (gap,A-count) pairs can require a finer local-clock calculation. -/
theorem initial_S_critical_pairs (q M m L s T j : Nat) (hM : 1≤M) (hm : 1≤m) (hj : 4≤j)
    (hsmall : M+L+T<j+11)
    (hmass : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (harea : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    (j=4 ∧ M+L+T=12) ∨ (j=4 ∧ M+L+T=14) ∨
      (j=5 ∧ M+L+T=14) ∨ (j=6 ∧ M+L+T=16) := by
  have he := initial_S_target_equations q M m L s T j hM hm hmass harea
  have hp := initial_S_target_even_A q M m L s T j hM hm hmass harea
  omega

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

theorem three_run_count_of_manyS (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤10 := by
  have hb2 := two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
    (fun hk => hpos _ hk (by omega))
  have hword := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
    hS hA hS2 hA2 hS3 (by intro i hi; omega)
  have hp : seg f 0 (n+h+M+m+L+s)=w++(List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false) := by
    rw [show n+h+M+m+L+s=n+(h+M+m+L+s) by omega,seg_add,Nat.zero_add,hpre]
    congr 1
    simpa using hword
  have hcS : 3≤cntF (List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A]
    omega
  have ho := block_rayCount_append hw _ hcS T
  have hl := third_ray_four_source_bound h M m L s T hs
  have he := endable_A_run_count f (n+h+M+m+L+s) T _ hp hA3
  have hz : cN (EndN f 0) (n+h+M+m+L) s=0 := by
    apply cN_zero_of
    intro x hx hxs he
    have hh := he.1
    rw [hS3 x hx hxs] at hh
    contradiction
  have a := cN_add (EndN f 0) n (h+M+m+L) s
  have b := cN_add (EndN f 0) n (h+M+m+L+s) T
  simp only [Nat.add_assoc] at *
  omega

theorem initial_S_source_word (f : Nat → Bool) (n h q M m L s T j : Nat) (hqh : q≤h)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false) :
    seg f (n+h-q) (q+M+m+L+s+T+j)=List.replicate q false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate T true++List.replicate j false := by
  have hword := Recaman.SeparatorSupplyReset.three_run_word f (n+h-q) q M m L s T
    (by intro x hx hxq; exact hS x (by omega) (by omega))
    (by intro i hi; simpa only [show n+h+i=n+h-q+q+i by omega] using hA i hi)
    (by intro x hx hxm; exact hS2 x (by omega) (by omega))
    (by intro i hi; simpa only [show n+h+M+m+i=n+h-q+q+M+m+i by omega] using hA2 i hi)
    (by intro x hx hxs; exact hS3 x (by omega) (by omega))
    (by intro i hi; simpa only [show n+h+M+m+L+s+i=n+h-q+q+M+m+L+s+i by omega] using hA3 i hi)
  have hs := seg_false f ((n+h-q)+(q+M+m+L+s+T)) j
    (fun x hx hxj => hgap x (by omega) (by omega))
  rw [seg_add,hs]
  exact congrArg (fun v : List Bool => v++List.replicate j false) hword

/-- This is an actual-history reduction, not a claim of absence in the
    four pairs. The initial S length and old prefix remain unbounded. -/
theorem initial_S_counterexample_pairs (f : Nat → Bool) (n h q M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hq : 1≤q) (hqh : q≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1)
    (hwin : Win f (n+h-q) (q+M+m+L+s+T+j)) :
    (j=4 ∧ M+L+T=12) ∨ (j=4 ∧ M+L+T=14) ∨
      (j=5 ∧ M+L+T=14) ∨ (j=6 ∧ M+L+T=16) := by
  have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
    (by omega) hpos hgap he hbad
  have hword := initial_S_source_word f n h q M m L s T j hqh hS hA hS2 hA2 hS3 hA3 hgap
  have hmass : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have hh := hwin.2.1
    omega
  have harea : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact hwin.2.2
  have htarget := initial_S_target_equations q M m L s T j hM hm hmass harea
  have hb := three_run_count_of_manyS f n h M m L s T w hw hpre hs (by omega)
    hS hA hS2 hA2 hS3 hA3 hpos
  have hwhole := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
  have hc := ones_seg_eq_count f n (h+M+m+L+s+T)
  rw [hwhole] at hc
  simp only [ones_append,ones_replicate_S,ones_replicate_A] at hc
  have hp := addition_endable_partition f n (h+M+m+L+s+T)
  exact initial_S_critical_pairs q M m L s T j hM hm (by omega) (by omega) hmass harea

end Recaman.InitialSTargetBounds
