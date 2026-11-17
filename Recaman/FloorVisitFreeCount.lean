import Recaman.FloorSupplyFreeBudget
import Recaman.LowFreeFourFloor

namespace Recaman.FloorVisitFreeCount

open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.FloorSupplyDistinctCharge
open Recaman.FloorSupplyFreeBudget Recaman.LowFreeFourFloor

set_option maxHeartbeats 2000000

private theorem subtraction_payment (f : Nat → Bool) (T t : Nat) (m : Int)
    (ht : t<T) (hfloor : ∀ i, i≤T → m≤Fw f i)
    (hend : m+2<Fw f T) (hFt : Fw f t=m+2) (hS : f t=false) :
    ∃ r, t<r ∧ r<T ∧ Fw f r=m+1 ∧ f r=true ∧ ¬EndN f 0 r ∧
      ∀ u, t<u → u≤r → Fw f u<m+2 := by
  have hs := fw_cases f t
  have hnext : Fw f (t+1)=m+1 := by
    rcases hs with ⟨_,ha⟩|⟨hs,_⟩
    · rw [hS] at ha; cases ha
    · omega
  obtain ⟨R,htR,hRT,hR,hbefore⟩ := first_return f (t+1) T (m+2)
    (by omega) (by omega) (by omega)
  have hp := hbefore (R-1) (by omega) (by omega)
  have hstep := fw_cases f (R-1)
  rw [show R-1+1=R by omega] at hstep
  have hr : Fw f (R-1)=m+1 ∧ f (R-1)=true := by
    rcases hstep with ⟨hs,ha⟩|⟨hs,_⟩
    · exact ⟨by omega,ha⟩
    · omega
  have hf := block_prefix_low_clock_not_endable f 0 0 (R-1)
    BlockWord.nil (by simp [seg]) (Nat.zero_le _) m
    (fun i _ hi => hfloor i (by omega)) (by omega)
  refine ⟨R-1,by omega,by omega,hr.1,hr.2,hf,?_⟩
  intro u htu hu
  exact hbefore u (by omega) (by omega)

/-- Every visit to floor+2 is paid by a different original free A at
floor, floor+1 or floor+2, provided the endpoint is above that level.
There is no upper excursion bound or bound on the original history. -/
theorem original_floor_visit_count (f : Nat → Bool) (T : Nat) (m : Int)
    (hfloor : ∀ i, i≤T → m≤Fw f i) (hend : m+2<Fw f T) :
    cN (fun q => Fw f q=m+2) 0 T ≤
      cN (fun q => f q=true ∧ ¬EndN f 0 q ∧ Fw f q≤m+2) 0 T := by
  classical
  obtain ⟨qa,hqa,hqaInj⟩ := actual_floor_supply_injection f 0 0 T m
    BlockWord.nil (by simp [seg]) (fun i _ hi => hfloor i (by omega))
  let P := fun t => t<T ∧ Fw f t=m+2 ∧ f t=false
  have hex (t : Nat) (ht : P t) := subtraction_payment f T t m ht.1 hfloor hend ht.2.1 ht.2.2
  let qs := fun t => if ht : P t then Classical.choose (hex t ht) else 0
  have hqs (t : Nat) (ht : P t) :
      t<qs t ∧ qs t<T ∧ Fw f (qs t)=m+1 ∧ f (qs t)=true ∧ ¬EndN f 0 (qs t) ∧
      ∀ u, t<u → u≤qs t → Fw f u<m+2 := by
    simp only [qs,dif_pos ht]
    exact Classical.choose_spec (hex t ht)
  let pay := fun t => if f t=false then qs t else if EndN f 0 t then qa t else t
  apply count_le_of_interval_injection _ _ 0 T pay
  · intro t _ ht hF
    by_cases hS : f t=false
    · obtain ⟨_,hr,hFr,hA,hfree,_⟩ := hqs t ⟨by omega,hF,hS⟩
      simp only [pay,if_pos hS]
      exact ⟨Nat.zero_le _,by omega,hA,hfree,by omega⟩
    · by_cases he : EndN f 0 t
      · obtain ⟨hn,hr,hFr,hA,hfree⟩ := hqa t (Nat.zero_le _) ht hF he
        simp only [pay,if_neg hS,if_pos he]
        exact ⟨hn,by omega,hA,hfree,by omega⟩
      · simp only [pay,if_neg hS,if_neg he]
        exact ⟨Nat.zero_le _,ht,by cases h : f t <;> simp_all,he,by omega⟩
  · intro t u _ htu hu hFt hFu hsame
    have ht : t<T := by omega
    have hu' : u<T := by omega
    by_cases htS : f t=false
    · obtain ⟨htr,_,htrF,_,_,hbetween⟩ := hqs t ⟨ht,hFt,htS⟩
      by_cases huS : f u=false
      · obtain ⟨hur,_,_,_,_,_⟩ := hqs u ⟨hu',hFu,huS⟩
        simp only [pay,if_pos htS,if_pos huS] at hsame
        have hb := hbetween u htu (by omega)
        omega
      · by_cases he : EndN f 0 u
        · have hf := (hqa u (Nat.zero_le _) hu hFu he).2.2.1
          simp only [pay,if_pos htS,if_neg huS,if_pos he] at hsame
          rw [hsame] at htrF
          omega
        · simp only [pay,if_pos htS,if_neg huS,if_neg he] at hsame
          rw [hsame] at htrF
          omega
    · by_cases huS : f u=false
      · have hruF := (hqs u ⟨hu',hFu,huS⟩).2.2.1
        by_cases he : EndN f 0 t
        · have hf := (hqa t (Nat.zero_le _) (by omega) hFt he).2.2.1
          simp only [pay,if_neg htS,if_pos huS,if_pos he] at hsame
          rw [←hsame] at hruF
          omega
        · simp only [pay,if_neg htS,if_pos huS,if_neg he] at hsame
          rw [←hsame] at hruF
          omega
      · by_cases htE : EndN f 0 t
        · by_cases huE : EndN f 0 u
          · simp only [pay,if_neg htS,if_neg huS,if_pos htE,if_pos huE] at hsame
            exact hqaInj t u (Nat.zero_le _) htu hu hFt hFu htE huE hsame
          · have hf := (hqa t (Nat.zero_le _) (by omega) hFt htE).2.2.1
            simp only [pay,if_neg htS,if_neg huS,if_pos htE,if_neg huE] at hsame
            rw [hsame] at hf
            omega
        · by_cases huE : EndN f 0 u
          · have hf := (hqa u (Nat.zero_le _) hu hFu huE).2.2.1
            simp only [pay,if_neg htS,if_neg huS,if_neg htE,if_pos huE] at hsame
            rw [←hsame] at hf
            omega
          · simp only [pay,if_neg htS,if_neg huS,if_neg htE,if_neg huE] at hsame
            omega

end Recaman.FloorVisitFreeCount
