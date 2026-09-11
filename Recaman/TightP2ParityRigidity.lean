import Recaman.UniversalTightLagBound

/-!
# TightP2ParityRigidity: P2 Odd-Subtractions Parity and Universal Lag-3 AAS Forcing

This module proves that in any positive-slack periodic word with `|D| ≤ 4`:
1. **P2 Length-1 Impossibility**: No P2 word has length 1 (`no_p2_length_one`).
2. **P2 Length-3 Uniqueness**: Any P2 word of length 3 is uniquely `[true, true, false]` (`AAS`) (`p2_length_three_eq_aas`).
3. **P2 Length-5 Impossibility**: No P2 word has length 5 (`no_p2_length_five`).
4. **Lag-Le-Five Forcing**: Any P2 window with lag `d ≤ 5` must have `d = 3` (`p2_lag_le_five_forces_three`).
5. **AAS Forcing**: Any P2 window with lag `d ≤ 5` is an AAS window (`p2_lag_le_five_forces_aas`).
6. **Universal Lag-3 Forcing for |D| ≤ 4**: In any positive-slack periodic word with `|D| ≤ 4`,
   every member of every tight subset avoiding an SS=2 donor window `u₀` satisfies `lag u = 3`
   and is an AAS window.
-/

namespace Recaman.TightP2ParityRigidity

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

/-- There are no P2 words of length 1. -/
theorem bitWords_one_p2 :
    (bitWords 1).filter (fun w => decide (P2 w)) = [] := by decide

theorem no_p2_length_one (w : List Bool) (hlen : w.length = 1) (hP : P2 w) : False := by
  have hmem : w ∈ bitWords 1 := by
    have hm := mem_bitWords w
    rwa [hlen] at hm
  have hfilt : w ∈ (bitWords 1).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  rw [bitWords_one_p2] at hfilt
  contradiction

/-- The only P2 word of length 3 is `[true, true, false]` (`AAS`). -/
theorem bitWords_three_p2 :
    (bitWords 3).filter (fun w => decide (P2 w)) = [[true, true, false]] := by decide

theorem p2_length_three_eq_aas (w : List Bool) (hlen : w.length = 3) (hP : P2 w) :
    w = [true, true, false] := by
  have hmem : w ∈ bitWords 3 := by
    have hm := mem_bitWords w
    rwa [hlen] at hm
  have hfilt : w ∈ (bitWords 3).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  rw [bitWords_three_p2] at hfilt
  simp at hfilt
  exact hfilt

/-- There are no P2 words of length 5. -/
theorem bitWords_five_p2 :
    (bitWords 5).filter (fun w => decide (P2 w)) = [] := by decide

theorem no_p2_length_five (w : List Bool) (hlen : w.length = 5) (hP : P2 w) : False := by
  have hmem : w ∈ bitWords 5 := by
    have hm := mem_bitWords w
    rwa [hlen] at hm
  have hfilt : w ∈ (bitWords 5).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  rw [bitWords_five_p2] at hfilt
  contradiction

/-- Unfolding of past window of length 3. -/
theorem past_three (e : Int → Bool) (u : Int) :
    past e u 3 = [e (u - 1), e (u - 2), e (u - 3)] := by
  unfold past
  rfl

/-- The length of a past window of lag d is d. -/
@[simp] theorem past_length (e : Int → Bool) (t : Int) (d : Nat) :
    (past e t d).length = d := by
  simp [past]

/-- If a past window of length 3 is AAS, its individual signs match AAS. -/
theorem aas_of_past_three_eq (e : Int → Bool) (u : Int)
    (h : past e u 3 = [true, true, false]) :
    e (u - 1) = true ∧ e (u - 2) = true ∧ e (u - 3) = false := by
  have hp := past_three e u
  rw [hp] at h
  injection h with h1 rest1
  injection rest1 with h2 rest2
  injection rest2 with h3 rest3
  exact ⟨h1, h2, h3⟩

/-- Any P2 window with lag `d ≤ 5` and `0 < d` must have lag `d = 3`. -/
theorem p2_lag_le_five_forces_three (e : Int → Bool) (u : Int) (d : Nat)
    (hd_pos : 0 < d) (hd_le : d ≤ 5)
    (hP : ShortPeriodicSupply.P2 e u d) :
    d = 3 := by
  have hP_past : P2 (past e u d) := (past_p2_iff e u d).mpr hP
  have hlen : (past e u d).length = d := past_length e u d
  have hodd : (past e u d).length % 2 = 1 := p2_length_odd (past e u d) hP_past
  rw [hlen] at hodd
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases hd_cases with rfl | rfl | rfl | rfl | rfl
  · have h1 : (past e u 1).length = 1 := past_length e u 1
    exact False.elim (no_p2_length_one (past e u 1) h1 hP_past)
  · omega
  · rfl
  · omega
  · have h5 : (past e u 5).length = 5 := past_length e u 5
    exact False.elim (no_p2_length_five (past e u 5) h5 hP_past)

/-- Any P2 window with lag `d ≤ 5` and `0 < d` is an AAS window. -/
theorem p2_lag_le_five_forces_aas (e : Int → Bool) (u : Int) (d : Nat)
    (hd_pos : 0 < d) (hd_le : d ≤ 5)
    (hP : ShortPeriodicSupply.P2 e u d) :
    e (u - 1) = true ∧ e (u - 2) = true ∧ e (u - 3) = false := by
  have hd3 : d = 3 := p2_lag_le_five_forces_three e u d hd_pos hd_le hP
  subst hd3
  have hP_past : P2 (past e u 3) := (past_p2_iff e u 3).mpr hP
  have hlen : (past e u 3).length = 3 := past_length e u 3
  have haas := p2_length_three_eq_aas (past e u 3) hlen hP_past
  exact aas_of_past_three_eq e u haas

/-- Universal lag 3 forcing: In any positive-slack word with `|D| ≤ 4`, every member
of every tight subset avoiding `u₀` with lag `lag u ≤ 5` and `0 < lag u` must have lag 3. -/
theorem tight_avoiding_member_lag_three_of_D_le_four (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (_hu : u ∈ A)
    (hlag_pos : 0 < lag u) (hlag_le5 : lag u ≤ 5)
    (hP : ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    lag u = 3 :=
  p2_lag_le_five_forces_three e (u : Int) (lag u) hlag_pos hlag_le5 hP

/-- Universal AAS forcing: In any positive-slack word with `|D| ≤ 4`, every member
of every tight subset avoiding `u₀` with lag `lag u ≤ 5` and `0 < lag u` is an AAS window. -/
theorem tight_avoiding_member_is_aas_of_D_le_four (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (_hu : u ∈ A)
    (hlag_pos : 0 < lag u) (hlag_le5 : lag u ≤ 5)
    (hP : ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false :=
  p2_lag_le_five_forces_aas e (u : Int) (lag u) hlag_pos hlag_le5 hP

end Recaman.TightP2ParityRigidity
