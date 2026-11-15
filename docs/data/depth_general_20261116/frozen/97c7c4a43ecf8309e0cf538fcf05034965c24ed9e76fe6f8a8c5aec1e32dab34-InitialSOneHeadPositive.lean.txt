import Recaman.FirstSOneFreePrefix
import Recaman.SourceDeficitBand
import Recaman.InitialSLowTargetTransport

namespace Recaman.InitialSOneHeadPositive

open Recaman.FirstSOneFreePrefix Recaman.SourceDeficitBand
open Recaman.InitialSLowTargetTransport Recaman.AdditionRankSlack
open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction

/-- An original first S and a height-one ceiling pay every positive
prefix; the two-free budget is derived, never assumed. -/
theorem first_S_height_one_positive (f : Nat → Bool) (B : Nat)
    (hFirst : f 0=false) (hCeil : ∀ k, k≤B → Fw f k≤1) :
    ∀ k, 0<k → k≤B → cN (EndN f 0) 0 k+1≤cN (fun i => f i=false) 0 k := by
  intro k hk hkB
  have hS : 1≤cN (fun i => f i=false) 0 k := by
    have h1 : cN (fun i => f i=false) 0 1=1 := by simp [cN,hFirst]
    have hm := count_prefix_le (fun i => f i=false) 0 1 k (by omega)
    omega
  by_cases hf : free f 0 k≤1
  · have hOne := first_S_one_free_additions f 0 0 k BlockWord.nil (by rfl) hFirst hf
    have hSplit := additions_split f 0 k
    change additions f 0 k=free f 0 k ∧ _ at hOne
    omega
  · have hWalk := walk_eq_free_sub_deficit f k
    have hC := hCeil k hkB
    unfold deficit subtractions at hWalk
    omega

/-- Keeping one initial S automatically preserves the positive domain
under the exact shifted ceiling, as well as original actual/free counts. -/
theorem one_head_preserves_actual_free_positive (f : Nat → Bool) (h K : Nat)
    (hh : 1≤h) (hS : ∀ i, i<h → f i=false)
    (hCeil : ∀ t, h≤t → t≤h+K → Fw f t≤Fw f h+2) :
    let g := fun i => f (h-1+i)
    (∀ q, q≤K → (EndN f 0 (h+q) ↔ EndN g 0 (1+q))) ∧
    cN (EndN f 0) 0 (h+K)=cN (EndN g 0) 0 (K+1) ∧
    free f 0 (h+K)=free g 0 (K+1) ∧
    (∀ k, 0<k → k≤K+1 → cN (EndN g 0) 0 k+1≤cN (fun i => g i=false) 0 k) := by
  dsimp only
  let s := h-1
  have hs : s+1=h := by dsimp [s]; omega
  have hfirst := hS s (by dsimp [s]; omega)
  have hStep := fw_false_run f s 1 (fun i hi hi1 => by
    have hie : i=s := by omega
    simpa only [hie] using hfirst)
  rw [hs] at hStep
  have hrem : ∀ i, i<s → f i=false := fun i hi => hS i (by dsimp [s] at hi; omega)
  have htarget (t : Nat) (ht : s≤t) (htK : t≤h+K) : Fw f t≤Fw f s+1 := by
    by_cases he : t=s
    · rw [he]; omega
    · have hc := hCeil t (by omega) htK
      omega
  have hcounts := initial_S_low_addition_counts f s (K+1) hrem (fun i hi hiK _ =>
    htarget i hi (by omega))
  rw [show s+(K+1)=h+K by omega] at hcounts
  have hshift (k : Nat) : Fw (fun i => f (s+i)) k=Fw f (s+k)-Fw f s := by
    induction k with
    | zero => simp [Fw]
    | succ k ih =>
      rw [Fw_succ,show s+(k+1)=s+k+1 by omega,Fw_succ,ih]
      change Fw f (s+k)-Fw f s+Recaman.ShortPeriodicSupply.sign (f (s+k))=
        Fw f (s+k)+Recaman.ShortPeriodicSupply.sign (f (s+k))-Fw f s
      omega
  have hpositive := first_S_height_one_positive (fun i => f (s+i)) (K+1)
    (by simpa using hfirst) (by
      intro k hk
      rw [hshift]
      exact (by have hc := htarget (s+k) (by omega) (by omega); omega))
  refine ⟨?_,hcounts.1,hcounts.2.1,hpositive⟩
  intro q hq
  have ht := initial_S_low_target_shift_iff f s (1+q) hrem
    (by have hc := htarget (h+q) (by omega) (by omega); simpa only [show s+(1+q)=h+q by omega] using hc)
  simpa only [show s+(1+q)=h+q by omega] using ht

/-- The same paid-positive operation retains any C>=1 S signs. Its
ceiling is explicit and independent of lower excursion depth. -/
theorem retained_head_preserves_actual_free_positive (f : Nat → Bool) (h C K : Nat)
    (hC1 : 1≤C) (hCh : C≤h) (hS : ∀ i, i<h → f i=false)
    (hCeil : ∀ t, h≤t → t≤h+K → Fw f t≤Fw f h+(C : Int)+1) :
    let g := fun i => f (h-C+i)
    (∀ q, q≤K → (EndN f 0 (h+q) ↔ EndN g 0 (C+q))) ∧
    cN (EndN f 0) 0 (h+K)=cN (EndN g 0) 0 (C+K) ∧
    free f 0 (h+K)=free g 0 (C+K) ∧
    (∀ k, 0<k → k≤C+K → cN (EndN g 0) 0 k+1≤cN (fun i => g i=false) 0 k) := by
  dsimp only
  let s := h-C
  have hs : s+C=h := by dsimp [s]; omega
  have hfirst := hS s (by dsimp [s]; omega)
  have hStep := fw_false_run f s C (fun i _ hi => hS i (by omega))
  rw [hs] at hStep
  have hrem : ∀ i, i<s → f i=false := fun i hi => hS i (by dsimp [s] at hi; omega)
  have htarget (t : Nat) (ht : s≤t) (htK : t≤h+K) : Fw f t≤Fw f s+1 := by
    by_cases hht : h≤t
    · have hc := hCeil t hht htK
      omega
    · have hlow := fw_false_run f s (t-s) (fun i _ hi => hS i (by omega))
      rw [show s+(t-s)=t by omega] at hlow
      omega
  have hcounts := initial_S_low_addition_counts f s (C+K) hrem (fun i hi hiK _ =>
    htarget i hi (by omega))
  rw [show s+(C+K)=h+K by omega] at hcounts
  have hshift (k : Nat) : Fw (fun i => f (s+i)) k=Fw f (s+k)-Fw f s := by
    induction k with
    | zero => simp [Fw]
    | succ k ih =>
      rw [Fw_succ,show s+(k+1)=s+k+1 by omega,Fw_succ,ih]
      omega
  have hpositive := first_S_height_one_positive (fun i => f (s+i)) (C+K)
    (by simpa using hfirst) (by
      intro k hk
      rw [hshift]
      have hc := htarget (s+k) (by omega) (by omega)
      omega)
  refine ⟨?_,hcounts.1,hcounts.2.1,hpositive⟩
  intro q hq
  have ht := initial_S_low_target_shift_iff f s (C+q) hrem
    (by have hc := htarget (h+q) (by omega) (by omega); simpa only [show s+(C+q)=h+q by omega] using hc)
  simpa only [show s+(C+q)=h+q by omega] using ht

/-- The positive bootstrap also retains an arbitrary original padded
old history. It supplies no deletion/transport claim across that history. -/
theorem padded_first_S_height_one_positive (f : Nat → Bool) (n a B : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hFirst : f n=false) (hCeil : ∀ k, k≤B → Fw f (n+k)≤Fw f n+1) :
    ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k := by
  intro k hk hkB
  have hS : 1≤cN (fun i => f i=false) n k := by
    have h1 : cN (fun i => f i=false) n 1=1 := by simp [cN,hFirst]
    have hm := count_prefix_le (fun i => f i=false) n 1 k (by omega)
    omega
  by_cases hf : free f n k≤1
  · have hOne := first_S_one_free_additions f n a k hw hpre hFirst hf
    have hSplit := additions_split f n k
    change additions f n k=free f n k ∧ _ at hOne
    omega
  · have hWalk := (cN_walk f n k).1
    have hSplit := additions_split f n k
    have hC := hCeil k hkB
    change Fw f (n+k)=Fw f n+(additions f n k : Int)-(subtractions f n k : Int) at hWalk
    unfold subtractions at hWalk
    omega

end Recaman.InitialSOneHeadPositive
