import Recaman.DepthSixGapResidual
import Recaman.FloorSupplyPairCharge

namespace Recaman.DepthSixPairResidual

open Recaman.DepthSixGapResidual Recaman.FloorSupplyPairCharge Recaman.NextHeightSupplyCharge
open Recaman.LowTargetWeightedGap Recaman.GapSquareLowAdditions Recaman.LevelTriangleArea
open Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Classical

private theorem int_count_step (P : Nat → Prop) (n k : Nat) :
    (cN P n (k+1) : Int)=(cN P n k : Int)+(if P (n+k) then 1 else 0) := by
  by_cases h : P (n+k)
  · rw [cN_succ_pos P n k h,if_pos h]
    omega
  · rw [cN_succ_neg P n k h,if_neg h]
    omega

private theorem count_adjusted_weights (f : Nat → Bool) (n K : Nat) (r : Int)
    (P Q R Z : Nat → Prop)
    (h : ∀ t, n≤t → t<n+K → lowAdditionWeight f r t+2*(if Z t then 1 else 0)≤
      7*(if P t then 1 else 0)+3*(if Q t then 1 else 0)+(if R t then 1 else 0)) :
    lowAdditionWeights f n r K+2*(cN Z n K : Int)≤
      7*(cN P n K : Int)+3*(cN Q n K : Int)+(cN R n K : Int) := by
  induction K with
  | zero => simp [cN,lowAdditionWeights]
  | succ k ih =>
    have hp := ih (fun t ht hk => h t ht (by omega))
    have hs := h (n+k) (by omega) (by omega)
    rw [lowAdditionWeights,int_count_step,int_count_step,int_count_step,int_count_step]
    omega

/-- Free additions at the second-lowest level cost two fewer units than
the crude bound, while the two low supplied levels keep separate counts. -/
theorem low_weights_saving_at_second_floor (f : Nat → Bool) (n a K : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hfloor : ∀ i, n≤i → i≤n+K → m≤Fw f i) (hr : r≤m+4) :
    lowAdditionWeights f n r K+
      2*(cN (fun t => Fw f t=m+1 ∧ f t=true) n K : Int)≤
      8*(free f n K : Int)+
      3*(cN (fun t => Fw f t=m+2 ∧ EndN f 0 t) n K : Int) := by
  let P := fun t => f t=true ∧ ¬EndN f 0 t
  let Q := fun t => Fw f t=m+2 ∧ EndN f 0 t
  let R := fun t => Fw f t=m+3 ∧ EndN f 0 t
  let Z := fun t => Fw f t=m+1 ∧ f t=true
  have hW := count_adjusted_weights f n K r P Q R Z (by
    intro t hnt htK
    have hlo := hfloor t hnt (by omega)
    have hNo (hl : Fw f t≤m+1) := block_prefix_low_clock_not_endable f n a t hw hpre hnt m
      (fun i hi hj => hfloor i hi (by omega)) hl
    by_cases hz : Z t
    · have hf := hz.1
      have he := hNo (by omega)
      rw [if_pos hz,if_pos (show P t from ⟨hz.2,he⟩),
        if_neg (fun hq : Q t => he hq.2),if_neg (fun hR : R t => he hR.2)]
      by_cases hA : f t=true ∧ Fw f t<r
      · rw [lowAdditionWeight,if_pos hA]
        omega
      · rw [lowAdditionWeight,if_neg hA]
        omega
    · rw [if_neg hz]
      by_cases hA : f t=true ∧ Fw f t<r
      · rw [lowAdditionWeight,if_pos hA]
        by_cases he : EndN f 0 t
        · have hHi : m+2≤Fw f t := by
            by_cases h : m+2≤Fw f t
            · exact h
            · exact (hNo (by omega) he).elim
          rw [if_neg (fun hp : P t => hp.2 he)]
          by_cases h2 : Fw f t=m+2
          · rw [if_pos (show Q t from ⟨h2,he⟩),if_neg (fun hR : R t => by have := hR.1; omega)]
            omega
          · have h3 : Fw f t=m+3 := by have := hA.2; omega
            rw [if_neg (fun hQ : Q t => h2 hQ.1),if_pos (show R t from ⟨h3,he⟩)]
            omega
        · rw [if_pos (show P t from ⟨hA.1,he⟩),if_neg (fun hq : Q t => he hq.2),
            if_neg (fun hR : R t => he hR.2)]
          omega
      · rw [lowAdditionWeight,if_neg hA]
        by_cases hp : P t <;> by_cases hq : Q t <;> by_cases hR : R t <;> simp [hp,hq,hR])
  have h3 := next_height_supply_count f n a K m hw hpre hfloor
  have hf : cN (fun t => Fw f t≤m+1 ∧ f t=true ∧ ¬EndN f 0 t) n K≤free f n K := by
    apply cN_mono
    intro t _ _ h
    exact h.2
  dsimp only [Q,Z] at hW
  change cN R n K≤_ at h3
  change lowAdditionWeights f n r K+2*(cN (fun t => Fw f t=m+1 ∧ f t=true) n K : Int)≤
    7*(free f n K : Int)+3*(cN (fun t => Fw f t=m+2 ∧ EndN f 0 t) n K : Int)+(cN R n K : Int) at hW
  omega

/-- The depth-six counter band narrows to gap four through six after the
two distinct floor payments and one compulsory second-floor addition. -/
theorem positive_depth_six_counter_gap_le_six (f : Nat → Bool) (n a b j : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j))
    (hcounter : free f n (b-n)≤j) :
    j≤6 := by
  obtain ⟨hf,h4,h8,ht,_⟩ := positive_depth_six_counter_profile f n a b j hw hpre
    hnb hfloor hpos hS he hcounter
  let m := Fw f n-6
  have hFloor (i : Nat) (hi : n≤i) (hib : i≤n+(b-n)) : m≤Fw f i :=
    hfloor i hi (by omega)
  have hit : ∃ q, n≤q ∧ q≤b ∧ Fw f q=m := by
    by_cases h : ∃ q, n≤q ∧ q≤b ∧ Fw f q=m
    · exact h
    · have hg := positive_full_depth_five_free_gap f n a b j hw hpre hnb (by
        intro i hi hib
        have hh := hfloor i hi hib
        by_cases hEq : Fw f i=m
        · exact (h ⟨i,hi,hib,hEq⟩).elim
        · dsimp [m] at hEq
          omega) hpos hS he
      omega
  obtain ⟨q,hqn,hqb,hqF⟩ := hit
  have hdown := fw_false_run f b j hS
  have hb : m+2≤Fw f b := by dsimp [m]; omega
  obtain ⟨z,hqz,hzb,hzF,hzA⟩ := ivt f b (m+2) hb (b-q) q (by omega) (by omega)
  have hzCount : 1≤cN (fun t => Fw f t=m+1 ∧ f t=true) n (b-n) := by
    by_cases h : 1≤cN (fun t => Fw f t=m+1 ∧ f t=true) n (b-n)
    · exact h
    · exact (not_of_cN_zero (fun t => Fw f t=m+1 ∧ f t=true) n (b-n)
        (by omega) z (by omega) (by omega) ⟨by omega,hzA⟩).elim
  have h2 := floor_supply_pair_charge f n a (b-n) m hw hpre hFloor
  have h3 : cN (fun t => Fw f t≤m+1 ∧ f t=true ∧ ¬EndN f 0 t) n (b-n)≤
      free f n (b-n) := by
    apply cN_mono
    intro t _ _ ht
    exact ht.2
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hW := low_weights_saving_at_second_floor f n a (b-n) m (Fw f (b+j)-1) hw hpre
    hFloor (by dsimp [m]; omega)
  by_cases h : j≤6
  · exact h
  · rcases (show j=7 ∨ j=8 by omega) with rfl | rfl
    · change (64 : Int) ≤ _ at hs
      omega
    · change (81 : Int) ≤ _ at hs
      omega

end Recaman.DepthSixPairResidual
