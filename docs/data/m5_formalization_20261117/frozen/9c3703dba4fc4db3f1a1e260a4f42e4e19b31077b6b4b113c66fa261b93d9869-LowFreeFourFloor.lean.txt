import Recaman.LowFreeFourPast
import Recaman.ThreeAdditionPrefix

namespace Recaman.LowFreeFourFloor

open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.InitialLowFreeRanks
open Recaman.LowFreeFourPast Recaman.OldAreaRecoveryBound
open Recaman.ThreeOldAdditionRecovery Recaman.ThreeAdditionPrefix

set_option maxHeartbeats 2000000

theorem last_minimum (f : Nat → Bool) : ∀ T,
    ∃ v, v≤T ∧ (∀ i, i≤T → Fw f v≤Fw f i) ∧
      ∀ i, v<i → i≤T → Fw f v<Fw f i := by
  intro T
  induction T with
  | zero =>
    refine ⟨0,by omega,?_,?_⟩
    · intro i hi
      have he : i=0 := by omega
      rw [he]
      exact Int.le_refl _
    · intro i hi hi0
      omega
  | succ T ih =>
    obtain ⟨v,hv,hmin,hstrict⟩ := ih
    by_cases hn : Fw f (T+1)≤Fw f v
    · refine ⟨T+1,Nat.le_refl _,?_,?_⟩
      · intro i hi
        by_cases hiT : i≤T
        · have hm := hmin i hiT
          omega
        · have he : i=T+1 := by omega
          rw [he]
          exact Int.le_refl _
      · intro i hi hiT
        omega
    · refine ⟨v,by omega,?_,?_⟩
      · intro i hi
        by_cases hiT : i≤T
        · exact hmin i hiT
        · have he : i=T+1 := by omega
          rw [he]
          omega
      · intro i hvi hi
        by_cases hiT : i≤T
        · exact hstrict i hvi hiT
        · have he : i=T+1 := by omega
          rw [he]
          omega

/-- The first upward return is selected inside the original history. -/
theorem first_return (f : Nat → Bool) (v T : Nat) (d : Int)
    (hvT : v≤T) (hv : Fw f v<d) (hT : d≤Fw f T) :
    ∃ R, v<R ∧ R≤T ∧ Fw f R=d ∧
      ∀ i, v≤i → i<R → Fw f i<d := by
  obtain ⟨R,hRT,⟨hvR,hR⟩,hfirst⟩ := SingleWindowEquality.first_mark
    (fun i => v≤i ∧ d≤Fw f i) T ⟨T,Nat.le_refl _,hvT,hT⟩
  have hvr : v<R := by
    by_cases he : v=R
    · rw [←he] at hR
      omega
    · omega
  have hbefore : ∀ i, v≤i → i<R → Fw f i<d := by
    intro i hvi hiR
    have hn := hfirst i hiR
    by_cases hle : d≤Fw f i
    · exact (hn ⟨hvi,hle⟩).elim
    · omega
  have hp := hbefore (R-1) (by omega) (by omega)
  have hs := fw_cases f (R-1)
  rw [show R-1+1=R by omega] at hs
  have he : Fw f R=d := by rcases hs with ⟨hs,_⟩|⟨hs,_⟩ <;> omega
  exact ⟨R,hvr,by omega,he,hbefore⟩

/-- The whole original free budget at the first return is internally
low. This statement is not extended to the later endpoint T. -/
theorem first_return_total_free (f : Nat → Bool) (h T v R : Nat)
    (hh : 1≤h) (hS : ∀ i, i<h → f i=false) (hRT : R≤T)
    (hA : cN (fun i => f i=true) 0 v≤3)
    (hbefore : ∀ i, v≤i → i<R → Fw f i<2-(h : Int))
    (hlow : cN (fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)) 0 T≤4) :
    cN (fun i => f i=true ∧ ¬EndN f 0 i) 0 R≤4 := by
  let L := fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)
  have hmap : cN (fun i => f i=true ∧ ¬EndN f 0 i) 0 R≤cN L 0 R := by
    apply cN_mono
    intro i _ hi hfree
    refine ⟨hfree.1,hfree.2,?_⟩
    by_cases hiv : i<v
    · have hm := count_prefix_le (fun j => f j=true) 0 (i+1) v (by omega)
      have hs := cN_succ_pos (fun j => f j=true) 0 i (by simpa using hfree.1)
      exact early_free_is_low f h i hh hS hfree.1 (by omega) hfree.2
    · have hb := hbefore i (by omega) (by omega)
      omega
  have hm := count_prefix_le L 0 R T hRT
  change cN L 0 T≤4 at hlow
  omega

private theorem original_old_paid (f : Nat → Bool) (h v : Nat)
    (hh : 1≤h) (hS : ∀ i, i<h → f i=false) :
    oldPaid (cN (fun i => f i=true) 0 v)≤cN (fun i => f i=true ∧ ¬EndN f 0 i) 0 v := by
  let p := cN (fun i => f i=true) 0 v
  change oldPaid p≤_
  by_cases h0 : p=0
  · simp [oldPaid,h0]
  · by_cases h1 : p=1
    · simp only [oldPaid,h0,if_false,h1,if_true]
      obtain ⟨q,hq,hA,hc⟩ := count_rank_clock (fun i => f i=true) 0 v (by dsimp [p] at h0; omega)
      have hf := first_two_not_supplied f q (by omega)
      by_cases hle : 1≤cN (fun i => f i=true ∧ ¬EndN f 0 i) 0 v
      · exact hle
      · exact (not_of_cN_zero (fun i => f i=true ∧ ¬EndN f 0 i) 0 v (by omega)
          q (Nat.zero_le _) (by omega) ⟨hA,hf⟩).elim
    · simp only [oldPaid,h0,if_false,h1]
      have ht := two_low_free_of_two_additions f h v hh hS (by dsimp [p] at h0 h1; omega)
      have hm := cN_mono
        (fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int))
        (fun i => f i=true ∧ ¬EndN f 0 i) 0 v (by intro i _ _ hi; exact ⟨hi.1,hi.2.1⟩)
      omega

/-- Original low free four prevents a visit below -h-4 followed by
return to2-h. The minimum, old A bound, total-free budget and triple
shape are all derived, with no depth, upper-height or length cutoff. -/
theorem low_four_original_floor (f : Nat → Bool) (h T : Nat)
    (hh : 1≤h) (hS : ∀ i, i<h → f i=false) (hend : Fw f T=2-(h : Int))
    (hlow : cN (fun i => f i=true ∧ ¬EndN f 0 i ∧ Fw f i≤1-(h : Int)) 0 T≤4) :
    ∀ x, x≤T → -(h : Int)-4≤Fw f x := by
  intro x hxT
  by_cases hx : -(h : Int)-4≤Fw f x
  · exact hx
  · obtain ⟨v,hvT,hmin,hstrict⟩ := last_minimum f T
    have hmx := hmin x hxT
    have hdeep : Fw f v ≤ -(h : Int)-5 := by omega
    have hA := old_additions_le_three f h T v hh hS hvT hmin hdeep (by omega) hlow
    obtain ⟨R,hvR,hRT,hR,hbefore⟩ := first_return f v T (2-(h : Int)) hvT (by omega) (by omega)
    have hfree := first_return_total_free f h T v R hh hS hRT hA hbefore hlow
    let F := fun i => f i=true ∧ ¬EndN f 0 i
    obtain ⟨u,w,hvu,huw,hwR,huF,hwF,huA,huf,hwA,hwf⟩ :=
      two_nonsupplied_additions_of_recovery f 0 0 v R BlockWord.nil (by simp [seg])
        (Nat.zero_le _) (by omega) (Fw f v) rfl
        (fun i _ hi => hmin i (by omega)) (by omega)
    have hpost : 2≤cN F v (R-v) := two_marks_le_count F v u w (R-v) hvu huw (by omega)
      ⟨huA,huf⟩ ⟨hwA,hwf⟩
    have hsplit := cN_sub0 F v R (by omega)
    have hfreeOld : cN F 0 v≤2 := by change cN F 0 R≤4 at hfree; omega
    let p := cN (fun i => f i=true) 0 v
    have htriple : p=3 → ∃ a b, 3≤b ∧
        seg f 0 v=List.replicate a false ++ List.replicate 3 true ++ List.replicate b false := by
      intro hp
      exact three_additions_at_floor_shape f v hp hfreeOld (fun i hi => hmin i (by omega))
    have hpaid := original_old_paid f h v hh hS
    have hbound := original_recovery_below_seven f v (R-v) p (by dsimp [p]; omega)
      (Nat.le_refl _) (fun i hi => hmin i (by omega)) htriple hpaid
      (by simpa only [Nat.add_sub_cancel' (by omega : v≤R)] using hfree)
      (by intro j hj hjR; exact hstrict (v+j) (by omega) (by omega))
    rw [Nat.add_sub_cancel' (by omega : v≤R)] at hbound
    omega

end Recaman.LowFreeFourFloor
