import Recaman.ThreeRunFreeGap

namespace Recaman.FourRunSupplyBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget
open Recaman.ThreeRunSupplyBudget Recaman.SeparatorSupplyReset
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,cntF,ih]

/-- Four A intervals have at most nineteen actual supplied clocks. All
history and lengths are retained; three genuine separators provide the
old-source threshold on the fourth ray. This is a count budget, not free-gap. -/
theorem four_run_supply_budget (f : Nat → Bool) (n h M m L s U v T : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+U+v+T)≤19 := by
  let B := h+M+m+L+s+U
  let D := B+v
  let rs : List (Bool × Nat) :=
    [(false,h),(true,M),(false,m),(true,L),(false,s),(true,U),(false,v)]
  have h3 := three_run_supply_budget f n h M m L s U w hw hpre
    hS hA hS2 hA2 hS3 hA3 (fun k hk hkB => hpos k hk (by omega))
  have hword : seg f n B=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true :=
    three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hshape : seg f 0 (n+D)=w++runWord rs := by
    rw [show n+D=n+(B+v) by rfl,seg_add,Nat.zero_add,hpre,
      seg_add,show n+B=n+h+M+m+L+s+U by omega,
      seg_false f (n+h+M+m+L+s+U) v hS4]
    change w++(seg f n B++List.replicate v false)=w++runWord rs
    rw [hword]
    simp [rs,runWord,List.append_assoc]
  have hcnt : 3≤cntF (runWord rs) := by
    simp only [rs,runWord,cntF_append,cntF_replicate_S,cntF_A,
      List.append_nil,Nat.add_zero]
    omega
  have hA4' : ∀ i, i<T → f (n+D+i)=true := by
    intro i hi
    simpa only [D,B,Nat.add_assoc] using hA4 i hi
  have he4 := endable_A_run_count f (n+D) T (w++runWord rs) hshape hA4'
  have hb := block_rayCount_append hw (runWord rs) hcnt T
  have hl := rayCount_runWord rs T
  have hlen : rs.length=7 := rfl
  rw [hlen] at hl
  have h4 : cN (EndN f 0) (n+D) T≤8 := by omega
  have hSzero : cN (EndN f 0) (n+B) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have hf := hS4 x (by omega) (by omega)
    have ht := he.1
    rw [hf] at ht
    contradiction
  have hc1 := cN_add (EndN f 0) n B v
  have hc2 := cN_add (EndN f 0) n D T
  change cN (EndN f 0) n (D+T)≤19
  change cN (EndN f 0) n B≤11 at h3
  dsimp only [D] at hc2 h4 ⊢
  omega

/-- Derived finite A/free/gap band only. S lengths and old histories
remain unbounded; no finite absence certificate is assumed. -/
theorem four_run_free_gap_residual (f : Nat → Bool) (n h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+U+v+T+j))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
    cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤17 ∧
    cN (fun x => f x=true) n (h+M+m+L+s+U+v+T)≤36 ∧ j≤17 := by
  have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  have hg := supplied_after_S_gap_half_bound f n 0 (n+h+M+m+L+s+U+v+T) j hw hpre0
    (by omega) hgap he
  rw [show n+h+M+m+L+s+U+v+T-n=h+M+m+L+s+U+v+T by omega,ones_seg_eq_count] at hg
  have hb := four_run_supply_budget f n h M m L s U v T w hw hpre hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  have hp := addition_endable_partition f n (h+M+m+L+s+U+v+T)
  have hr : 4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
    by_cases hsmall : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤3
    · have hh := positive_r3_free_gap f n 0 (h+M+m+L+s+U+v+T) j hw hpre0
        (by omega) hpos hsmall (by simpa only [Nat.add_assoc] using hgap)
        (by simpa only [Nat.add_assoc] using he)
      omega
    · omega
  omega

theorem four_run_bounds_from_zero (f : Nat → Bool) (n h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hzero : cN (EndN f 0) 0 n=cN (fun x => f x=false) 0 n)
    (hpos : ∀ q, n<q → q≤n+h+M+m+L+s+U+v+T+j →
      cN (EndN f 0) 0 q+1≤cN (fun x => f x=false) 0 q)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+U+v+T+j)) :
    cN (EndN f 0) n (h+M+m+L+s+U+v+T)≤19 ∧
    (cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 →
      4≤cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) ∧
      cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)≤17 ∧
      cN (fun x => f x=true) n (h+M+m+L+s+U+v+T)≤36 ∧ j≤17) := by
  have hrel : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k := by
    intro k hk hkB
    have hp := hpos (n+k) (by omega) (by omega)
    have hE := cN_add (EndN f 0) 0 n k
    have hS := cN_add (fun x => f x=false) 0 n k
    simp only [Nat.zero_add] at hE hS
    omega
  constructor
  · exact four_run_supply_budget f n h M m L s U v T w hw hpre hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hrel
  · exact four_run_free_gap_residual f n h M m L s U v T j w hw hpre hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hrel hgap he

open Classical in
theorem four_run_bounds_int (e : Int → Bool) (p : Int) (n a h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false)
    (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false)
    (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false)
    (hA3 : ∀ i, i<U → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → e (p+(x : Int))=false)
    (hA4 : ∀ i, i<T → e (p+((n+h+M+m+L+s+U+v+i : Nat) : Int))=true)
    (hzero : endableCount e p n=subtractionCount e p n)
    (hpos : ∀ q, n<q → q≤n+h+M+m+L+s+U+v+T+j →
      endableCount e p q+1≤subtractionCount e p q)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → e (p+(x : Int))=false)
    (he : Endable e p (p+((n+h+M+m+L+s+U+v+T+j : Nat) : Int))) :
    countP (Endable e p) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤19 ∧
    (countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)<j+1 →
      4≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T) ∧
      countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤17 ∧
      countP (fun x => e x=true) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤36 ∧ j≤17) := by
  rw [segment_seg e p p 0 (by simp)] at hpre
  simp only [endableCount_shift,subtractionCount_shift] at hzero hpos
  rw [endable_interval_shift,nonsupplied_count_shift]
  rw [countP_cN (fun x => e x=true) p (p+(n : Int)) n rfl]
  apply four_run_bounds_from_zero (fun i => e (p+(i : Int))) n h M m L s U v T j
    (w++List.replicate a true) (block_append hw (block_replicate_A a)) hpre hm hs hv
    hS hA hS2 hA2 hS3 hA3 hS4 hA4 hzero hpos hgap
  exact (endable_iff e p p _ 0 (n+h+M+m+L+s+U+v+T+j) (by simp) rfl).mp he

end Recaman.FourRunSupplyBudget
