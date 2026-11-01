import Recaman.BlockOldRay

namespace Recaman.ThreeRunSupplyBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem count_S_run (f : Nat → Bool) (n K : Nat)
    (hS : ∀ x, n≤x → x<n+K → f x=false) : cN (fun x => f x=false) n K=K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [cN_succ_pos (fun x => f x=false) n K (hS (n+K) (by omega) (by omega)),
      ih (fun x hx hxK => hS x hx (by omega))]

private theorem no_S_in_A_run (f : Nat → Bool) (n K : Nat)
    (hA : ∀ i, i<K → f (n+i)=true) : cN (fun x => f x=false) n K=0 := by
  apply cN_zero_of
  intro x hx hxK he
  have ha := hA (x-n) (by omega)
  rw [Nat.add_sub_cancel' hx,he] at ha
  contradiction

private theorem no_supply_in_S_run (f : Nat → Bool) (n K : Nat)
    (hS : ∀ x, n≤x → x<n+K → f x=false) : cN (EndN f 0) n K=0 := by
  apply cN_zero_of
  intro x hx hxK he
  have ht := he.1
  rw [hS x hx hxK] at ht
  contradiction

private theorem two_run_S_count (f : Nat → Bool) (n h M m L : Nat)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true) :
    cN (fun x => f x=false) n (h+M+m+L)=h+m := by
  have h1 := count_S_run f n h hS
  have h2 := no_S_in_A_run f (n+h) M hA
  have h3 := count_S_run f (n+h+M) m hS2
  have h4 := no_S_in_A_run f (n+h+M+m) L hA2
  have a := cN_add (fun x => f x=false) n h M
  have b := cN_add (fun x => f x=false) n (h+M) m
  have c := cN_add (fun x => f x=false) n (h+M+m) L
  simp only [Nat.add_assoc] at *
  omega

/-- Actual relative positivity supplies the small-S boundary missing from
an unrestricted two-run count bound. Empty runs are retained. -/
theorem two_run_supply_of_positive (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hpos : 0<h+M+m+L → cN (EndN f 0) n (h+M+m+L)+1≤
      cN (fun x => f x=false) n (h+M+m+L)) :
    cN (EndN f 0) n (h+M+m+L)≤5 := by
  by_cases hs : 3≤h+m
  · exact two_A_run_supply_budget f n h M m L w hw hpre hS hA hS2 hA2 hs
  · by_cases hb : 0<h+M+m+L
    · have hp := hpos hb
      have hc := two_run_S_count f n h M m L hS hA hS2 hA2
      omega
    · have h0 : h+M+m+L=0 := by omega
      rw [h0]
      change 0≤5
      omega

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,cntF,ih]

/-- Three actual A runs have at most eleven supplied clocks, independently
of all run lengths and the size of the old BlockWord prefix. -/
theorem three_run_supply_budget (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤11 := by
  have h2 := two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
    (fun hb => hpos _ hb (by omega))
  have hs3 := no_supply_in_S_run f (n+h+M+m+L) s hS3
  have hc2 := cN_add (EndN f 0) n (h+M+m+L) s
  have hc3 := cN_add (EndN f 0) n (h+M+m+L+s) T
  by_cases hs : 3≤h+m+s
  · let v := List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false
    have hp : seg f 0 (n+h+M+m+L+s)=w++v := by
      have ha1 : seg f (n+h) M=List.replicate M true := by
        apply seg_A
        intro x hx hxM
        simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+h)) (by omega)
      have ha2 : seg f (n+h+M+m) L=List.replicate L true := by
        apply seg_A
        intro x hx hxL
        simpa only [Nat.add_sub_cancel' hx] using hA2 (x-(n+h+M+m)) (by omega)
      simp only [v]
      rw [seg_add,show 0+(n+h+M+m+L)=n+h+M+m+L by omega,
        seg_false f (n+h+M+m+L) s hS3,
        seg_add,show 0+(n+h+M+m)=n+h+M+m by omega,ha2,
        seg_add,show 0+(n+h+M)=n+h+M by omega,seg_false f (n+h+M) m hS2,
        seg_add,show 0+(n+h)=n+h by omega,ha1,
        seg_add,show 0+n=n by omega,hpre,seg_false f n h hS]
      simp only [List.append_assoc]
    have hsV : 3≤cntF v := by
      simp only [v,cntF_append,cntF_replicate_S,cntF_A,Nat.add_zero]
      exact hs
    have hb := block_rayCount_append hw v hsV T
    have hv : rayCount v T≤5 := by
      have h := rayCount_runWord [(false,h),(true,M),(false,m),(true,L),(false,s)] T
      simpa [v,runWord,List.append_assoc] using h
    have he := endable_A_run_count f (n+h+M+m+L+s) T (w++v) hp hA3
    simp only [Nat.add_assoc] at *
    omega
  · have hcS := two_run_S_count f n h M m L hS hA hS2 hA2
    have hcS3 := count_S_run f (n+h+M+m+L) s hS3
    have hcA3 := no_S_in_A_run f (n+h+M+m+L+s) T hA3
    have ha := cN_add (fun x => f x=false) n (h+M+m+L) s
    have hb := cN_add (fun x => f x=false) n (h+M+m+L+s) T
    by_cases hB : 0<h+M+m+L+s+T
    · have hp := hpos _ hB (Nat.le_refl _)
      simp only [Nat.add_assoc] at *
      omega
    · have h0 : h+M+m+L+s+T=0 := by omega
      rw [h0]
      change 0≤11
      omega

/-- Any counterexample to free-gap among these three-run histories lies
in a derived finite A/free/gap band. S lengths stay unbounded. -/
theorem three_run_free_gap_residual (f : Nat → Bool) (n h M m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)≤9 ∧
    cN (fun x => f x=true) n (h+M+m+L+s+T)≤20 ∧ j≤9 := by
  have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  have hg := supplied_after_S_gap_half_bound f n 0 (n+h+M+m+L+s+T) j hw hpre0
    (by omega) hgap he
  rw [show n+h+M+m+L+s+T-n=h+M+m+L+s+T by omega,ones_seg_eq_count] at hg
  have hsup := three_run_supply_budget f n h M m L s T w hw hpre hS hA hS2 hA2 hS3 hA3 hpos
  have hp := addition_endable_partition f n (h+M+m+L+s+T)
  have hfree : 4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) := by
    by_cases hr : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)≤3
    · have hx := positive_r3_free_gap f n 0 (h+M+m+L+s+T) j hw hpre0 hB hpos hr
        (by simpa only [Nat.add_assoc] using hgap) (by simpa only [Nat.add_assoc] using he)
      omega
    · omega
  omega


/-- All counts retain the original base zero. The absolute zero/positive
hypotheses supply relative positivity rather than assuming it silently. -/
theorem three_run_bounds_from_zero (f : Nat → Bool) (n h M m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hB : 0<h+M+m+L+s+T)
    (hzero : cN (EndN f 0) 0 n=cN (fun x => f x=false) 0 n)
    (hpos : ∀ u, n<u → u≤n+h+M+m+L+s+T+j →
      cN (EndN f 0) 0 u+1≤cN (fun x => f x=false) 0 u)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j)) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤11 ∧
    (cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1 →
      4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) ∧
      cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)≤9 ∧
      cN (fun x => f x=true) n (h+M+m+L+s+T)≤20 ∧ j≤9) := by
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k := by
    intro k hk hkB
    have hp := hpos (n+k) (by omega) (by omega)
    have hE := cN_add (EndN f 0) 0 n k
    have hS := cN_add (fun x => f x=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  constructor
  · exact three_run_supply_budget f n h M m L s T w hw hpre hS hA hS2 hA2 hS3 hA3 hrel
  · exact three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
      hB hrel hgap he

open Classical in
theorem endable_interval_shift (e : Int → Bool) (p : Int) (n B : Nat) :
    countP (Endable e p) (p+(n : Int)) B=
      cN (EndN (fun i => e (p+(i : Int))) 0) n B := by
  rw [countP_cN (Endable e p) p (p+(n : Int)) n rfl B]
  apply cN_congr
  intro i _ _
  exact endable_iff e p p (p+(i : Int)) 0 i (by simp) rfl

open Classical in
theorem three_run_bounds_int (e : Int → Bool) (p : Int) (n h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w)
    (hS : ∀ i, n≤i → i<n+h → e (p+(i : Int))=false)
    (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true)
    (hS2 : ∀ i, n+h+M≤i → i<n+h+M+m → e (p+(i : Int))=false)
    (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true)
    (hS3 : ∀ i, n+h+M+m+L≤i → i<n+h+M+m+L+s → e (p+(i : Int))=false)
    (hA3 : ∀ i, i<T → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true)
    (hB : 0<h+M+m+L+s+T)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ u, n<u → u≤n+h+M+m+L+s+T+j → endableCount e p u+1≤subtractionCount e p u)
    (hgap : ∀ i, n+h+M+m+L+s+T≤i → i<n+h+M+m+L+s+T+j → e (p+(i : Int))=false)
    (he : Endable e p (p+((n+h+M+m+L+s+T+j : Nat) : Int))) :
    countP (Endable e p) (p+(n : Int)) (h+M+m+L+s+T)≤11 ∧
    (countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T)<j+1 →
      4≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T) ∧
      countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T)≤9 ∧
      countP (fun x => e x=true) (p+(n : Int)) (h+M+m+L+s+T)≤20 ∧ j≤9) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [endable_interval_shift,nonsupplied_count_shift]
  rw [countP_cN (fun x => e x=true) p (p+(n : Int)) n rfl]
  apply three_run_bounds_from_zero (fun i => e (p+(i : Int))) n h M m L s T j w hw hpre
    hS hA hS2 hA2 hS3 hA3 hB hzero hpos hgap
  exact (endable_iff e p p _ 0 (n+h+M+m+L+s+T+j) (by simp) rfl).mp he


/-- The first two actual A signs after a BlockWord and an S run are free.
E407 is applied to the second clock only; its strict n<b condition is retained. -/
theorem first_two_A_not_supplied (f : Nat → Bool) (n h M : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) (i : Nat) (hiM : i<M) (hi2 : i<2) :
    ¬EndN f 0 (n+h+i) := by
  have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  by_cases hi0 : i=0
  · subst i
    simpa only [Nat.zero_add,Nat.add_zero] using
      no_window_after_S_run f 0 n 0 h hw hpre0 (by simpa only [Nat.zero_add] using hS)
  · have hi1 : i=1 := by omega
    subst i
    intro he
    have hg := supplied_after_S_gap_half_bound f n 0 (n+h+1) 0 hw hpre0 (by omega)
      (by intro x hx hxx; omega) (by simpa only [Nat.add_zero] using he)
    have ha : seg f (n+h) 1=List.replicate 1 true := by
      apply seg_A
      intro x hx hx1
      have heq : x=n+h := by omega
      subst x
      simpa only [Nat.add_zero] using hA 0 (by omega)
    rw [show n+h+1-n=h+1 by omega,seg_add,seg_false f n h hS,ha,
      ones_append,ones_replicate_S,ones_replicate_A] at hg
    omega

/-- First-run charge is nonpositive: total A<=twice the actual free A.
No positive-deficit hypothesis or bound on the old prefix is assumed. -/
theorem first_run_additions_free_bound (f : Nat → Bool) (n h M : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) :
    M≤2*cN (fun x => f x=true ∧ ¬EndN f 0 x) (n+h) M := by
  let P := fun x => f x=true ∧ ¬EndN f 0 x
  have hp := addition_endable_partition f (n+h) M
  rw [count_A_run f (n+h) M hA] at hp
  by_cases hM : 2≤M
  · have h0 : P (n+h+0) := ⟨hA 0 (by omega),first_two_A_not_supplied f n h M w hw hpre hS hA 0 (by omega) (by omega)⟩
    have h1 : P (n+h+1) := ⟨hA 1 (by omega),first_two_A_not_supplied f n h M w hw hpre hS hA 1 (by omega) (by omega)⟩
    have hc0 := cN_succ_pos P (n+h) 0 h0
    have hc1 := cN_succ_pos P (n+h) 1 h1
    have hm := count_prefix_le P (n+h) 2 M hM
    have hb := single_A_run_free_budget f n h M w hw hpre hS hA
    change M≤2*cN P (n+h) M
    change M≤cN P (n+h) M+2 at hb
    change cN P (n+h) 1=0+1 at hc0
    change cN P (n+h) 2=cN P (n+h) 1+1 at hc1
    omega
  · have hz : cN (EndN f 0) (n+h) M=0 := by
      apply cN_zero_of
      intro x hx hxM he
      have hn := first_two_A_not_supplied f n h M w hw hpre hS hA (x-(n+h)) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hx] at hn
      exact hn he
    omega

/-- The two-run count consumed by free-gap can be used independently of a
future target: its actual charge totalA-2free is at most one. -/
theorem two_run_additions_free_bound (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (fun x => f x=true) n (h+M+m+L)≤
      2*cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L)+1 := by
  by_cases hr : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L)≤3
  · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
    exact positive_r3_additions_free_bound f n 0 (h+M+m+L) hw hpre0 hpos hr
  · have hb := two_run_supply_of_positive f n h M m L w hw hpre hS hA hS2 hA2
      (fun hk => hpos _ hk (Nat.le_refl _))
    have hp := addition_endable_partition f n (h+M+m+L)
    omega

open Classical in
theorem first_run_additions_free_bound_int (e : Int → Bool) (p : Int) (n h M : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w)
    (hS : ∀ i, n≤i → i<n+h → e (p+(i : Int))=false)
    (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true) :
    M≤2*countP (fun x => e x=true ∧ ¬Endable e p x) (p+((n+h : Nat) : Int)) M := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  rw [nonsupplied_count_shift]
  exact first_run_additions_free_bound (fun i => e (p+(i : Int))) n h M w hw hpre hS hA


open Classical in
theorem two_run_additions_free_bound_int (e : Int → Bool) (p : Int) (n h M m L : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w)
    (hS : ∀ i, n≤i → i<n+h → e (p+(i : Int))=false)
    (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true)
    (hS2 : ∀ i, n+h+M≤i → i<n+h+M+m → e (p+(i : Int))=false)
    (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ u, n<u → u≤n+h+M+m+L → endableCount e p u+1≤subtractionCount e p u) :
    countP (fun x => e x=true) (p+(n : Int)) (h+M+m+L)≤
      2*countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L)+1 := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [nonsupplied_count_shift,countP_cN (fun x => e x=true) p (p+(n : Int)) n rfl]
  apply two_run_additions_free_bound (fun i => e (p+(i : Int))) n h M m L w hw hpre hS hA hS2 hA2
  intro k hk hkB
  have hp := hpos (n+k) (by omega) (by omega)
  have hE := cN_add (EndN (fun i => e (p+(i : Int))) 0) 0 n k
  have hS := cN_add (fun i => e (p+(i : Int))=false) 0 n k
  simp only [Nat.zero_add] at hE hS
  omega

end Recaman.ThreeRunSupplyBudget
