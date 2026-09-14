import Recaman.TwoLagSevenPhaseConflict

open Recaman.LagSevenPrefixRigidity
open Recaman.TwoLagSevenPhaseConflict
open Recaman.LeadingRunSupply

/-!
# LagSevenDistanceSeparationRigidity: Universal Distance ≥ 5 Forcing in Streams

This module establishes that any two minimal lag 7 additions in any valid stream
must be separated by at least 5 stream steps:

1. : All 16 combinations of word types at shifts
   d ∈ {1, 2, 3, 4} produce direct bit contradictions on stream positions.
2. : Any two lag 7 additions with shift d ∈ {1, 2, 3, 4} are impossible.
3. : For any u₁ < u₂, we must have u₂ - u₁ ≥ 5.
4. : For u₁ < u₂ < u₃, u₃ - u₁ ≥ 10.
5. : Master synthesis theorem.
-/

namespace Recaman.LagSevenDistanceSeparationRigidity

theorem conflict_d1_w1_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 1)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with p1_val_1 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with p2_val_2 _
  have heq : u1 - 1 = u2 - 2 := by omega
  rw [heq] at p1_val_1
  rw [p1_val_1] at p2_val_2
  revert p2_val_2
  decide

theorem conflict_d1_w1_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 1)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with _ p1_tail_2
  injection p1_tail_2 with _ p1_tail_3
  injection p1_tail_3 with p1_val_4 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with _ p2_tail_4
  injection p2_tail_4 with p2_val_5 _
  have heq : u1 - 4 = u2 - 5 := by omega
  rw [heq] at p1_val_4
  rw [p1_val_4] at p2_val_5
  revert p2_val_5
  decide

theorem conflict_d1_w2_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 1)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with p1_val_2 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with p2_val_3 _
  have heq : u1 - 2 = u2 - 3 := by omega
  rw [heq] at p1_val_2
  rw [p1_val_2] at p2_val_3
  revert p2_val_3
  decide

theorem conflict_d1_w2_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 1)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with p1_val_1 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with p2_val_2 _
  have heq : u1 - 1 = u2 - 2 := by omega
  rw [heq] at p1_val_1
  rw [p1_val_1] at p2_val_2
  revert p2_val_2
  decide

theorem conflict_d2_w1_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 2)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with p1_val_1 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with p2_val_3 _
  have heq : u1 - 1 = u2 - 3 := by omega
  rw [heq] at p1_val_1
  rw [p1_val_1] at p2_val_3
  revert p2_val_3
  decide

theorem conflict_d2_w1_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 2)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with p1_val_1 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with p2_val_3 _
  have heq : u1 - 1 = u2 - 3 := by omega
  rw [heq] at p1_val_1
  rw [p1_val_1] at p2_val_3
  revert p2_val_3
  decide

theorem conflict_d2_w2_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 2)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with p1_val_2 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with p2_val_4 _
  have heq : u1 - 2 = u2 - 4 := by omega
  rw [heq] at p1_val_2
  rw [p1_val_2] at p2_val_4
  revert p2_val_4
  decide

theorem conflict_d2_w2_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 2)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with p1_val_2 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with p2_val_4 _
  have heq : u1 - 2 = u2 - 4 := by omega
  rw [heq] at p1_val_2
  rw [p1_val_2] at p2_val_4
  revert p2_val_4
  decide

theorem conflict_d3_w1_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 3)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with p1_val_1 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with p2_val_4 _
  have heq : u1 - 1 = u2 - 4 := by omega
  rw [heq] at p1_val_1
  rw [p1_val_1] at p2_val_4
  revert p2_val_4
  decide

theorem conflict_d3_w1_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 3)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with p1_val_1 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with p2_val_4 _
  have heq : u1 - 1 = u2 - 4 := by omega
  rw [heq] at p1_val_1
  rw [p1_val_1] at p2_val_4
  revert p2_val_4
  decide

theorem conflict_d3_w2_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 3)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with p1_val_2 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with _ p2_tail_4
  injection p2_tail_4 with p2_val_5 _
  have heq : u1 - 2 = u2 - 5 := by omega
  rw [heq] at p1_val_2
  rw [p1_val_2] at p2_val_5
  revert p2_val_5
  decide

theorem conflict_d3_w2_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 3)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with _ p1_tail_2
  injection p1_tail_2 with _ p1_tail_3
  injection p1_tail_3 with p1_val_4 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with _ p2_tail_4
  injection p2_tail_4 with _ p2_tail_5
  injection p2_tail_5 with _ p2_tail_6
  injection p2_tail_6 with p2_val_7 _
  have heq : u1 - 4 = u2 - 7 := by omega
  rw [heq] at p1_val_4
  rw [p1_val_4] at p2_val_7
  revert p2_val_7
  decide

theorem conflict_d4_w1_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 4)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with p1_val_1 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with _ p2_tail_4
  injection p2_tail_4 with p2_val_5 _
  have heq : u1 - 1 = u2 - 5 := by omega
  rw [heq] at p1_val_1
  rw [p1_val_1] at p2_val_5
  revert p2_val_5
  decide

theorem conflict_d4_w1_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 4)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w1 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with _ p1_tail_2
  injection p1_tail_2 with p1_val_3 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with _ p2_tail_4
  injection p2_tail_4 with _ p2_tail_5
  injection p2_tail_5 with _ p2_tail_6
  injection p2_tail_6 with p2_val_7 _
  have heq : u1 - 3 = u2 - 7 := by omega
  rw [heq] at p1_val_3
  rw [p1_val_3] at p2_val_7
  revert p2_val_7
  decide

theorem conflict_d4_w2_w1 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 4)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w1) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w1 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with _ p1_tail_2
  injection p1_tail_2 with p1_val_3 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with _ p2_tail_4
  injection p2_tail_4 with _ p2_tail_5
  injection p2_tail_5 with _ p2_tail_6
  injection p2_tail_6 with p2_val_7 _
  have heq : u1 - 3 = u2 - 7 := by omega
  rw [heq] at p1_val_3
  rw [p1_val_3] at p2_val_7
  revert p2_val_7
  decide

theorem conflict_d4_w2_w2 (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 + 4)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w2) : False := by
  have p1 : [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] = w2 := hw1
  have p2 : [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] = w2 := hw2
  injection p1 with _ p1_tail_1
  injection p1_tail_1 with _ p1_tail_2
  injection p1_tail_2 with p1_val_3 _
  injection p2 with _ p2_tail_1
  injection p2_tail_1 with _ p2_tail_2
  injection p2_tail_2 with _ p2_tail_3
  injection p2_tail_3 with _ p2_tail_4
  injection p2_tail_4 with _ p2_tail_5
  injection p2_tail_5 with _ p2_tail_6
  injection p2_tail_6 with p2_val_7 _
  have heq : u1 - 3 = u2 - 7 := by omega
  rw [heq] at p1_val_3
  rw [p1_val_3] at p2_val_7
  revert p2_val_7
  decide

/-- Universal conflict helper for any pair of minimal lag 7 words at shift d ∈ {1, 2, 3, 4}. -/
theorem lag7_distance_conflict (e : Int → Bool) (u1 u2 : Int) (d : Nat)
    (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4)
    (h_shift : u2 = u1 + d)
    (hw1 : past e u1 7 = w1 ∨ past e u1 7 = w2)
    (hw2 : past e u2 7 = w1 ∨ past e u2 7 = w2) : False := by
  rcases hd with rfl | rfl | rfl | rfl
  · rcases hw1 with hw1_1 | hw1_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d1_w1_w1 e u1 u2 h_shift hw1_1 hw2_1
      · exact conflict_d1_w1_w2 e u1 u2 h_shift hw1_1 hw2_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d1_w2_w1 e u1 u2 h_shift hw1_2 hw2_1
      · exact conflict_d1_w2_w2 e u1 u2 h_shift hw1_2 hw2_2
  · rcases hw1 with hw1_1 | hw1_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d2_w1_w1 e u1 u2 h_shift hw1_1 hw2_1
      · exact conflict_d2_w1_w2 e u1 u2 h_shift hw1_1 hw2_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d2_w2_w1 e u1 u2 h_shift hw1_2 hw2_1
      · exact conflict_d2_w2_w2 e u1 u2 h_shift hw1_2 hw2_2
  · rcases hw1 with hw1_1 | hw1_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d3_w1_w1 e u1 u2 h_shift hw1_1 hw2_1
      · exact conflict_d3_w1_w2 e u1 u2 h_shift hw1_1 hw2_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d3_w2_w1 e u1 u2 h_shift hw1_2 hw2_1
      · exact conflict_d3_w2_w2 e u1 u2 h_shift hw1_2 hw2_2
  · rcases hw1 with hw1_1 | hw1_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d4_w1_w1 e u1 u2 h_shift hw1_1 hw2_1
      · exact conflict_d4_w1_w2 e u1 u2 h_shift hw1_1 hw2_2
    · rcases hw2 with hw2_1 | hw2_2
      · exact conflict_d4_w2_w1 e u1 u2 h_shift hw1_2 hw2_1
      · exact conflict_d4_w2_w2 e u1 u2 h_shift hw1_2 hw2_2

/-- Universal Distance ≥ 5 Forcing: Any two distinct ordered lag 7 additions
in any stream must be separated by at least 5 stream positions. -/
theorem lag7_stream_distance_ge_five (e : Int → Bool) (u1 u2 : Int)
    (hu : u1 < u2)
    (hw1 : past e u1 7 = w1 ∨ past e u1 7 = w2)
    (hw2 : past e u2 7 = w1 ∨ past e u2 7 = w2) :
    u1 + 5 ≤ u2 := by
  by_cases hlt : u1 + 5 ≤ u2
  · exact hlt
  · exfalso
    have hdiff : u2 - u1 = 1 ∨ u2 - u1 = 2 ∨ u2 - u1 = 3 ∨ u2 - u1 = 4 := by omega
    rcases hdiff with h1 | h2 | h3 | h4
    · have hd : (1 : Nat) = 1 ∨ (1 : Nat) = 2 ∨ (1 : Nat) = 3 ∨ (1 : Nat) = 4 := by omega
      have hs : u2 = u1 + (1 : Nat) := by omega
      exact lag7_distance_conflict e u1 u2 1 hd hs hw1 hw2
    · have hd : (2 : Nat) = 1 ∨ (2 : Nat) = 2 ∨ (2 : Nat) = 3 ∨ (2 : Nat) = 4 := by omega
      have hs : u2 = u1 + (2 : Nat) := by omega
      exact lag7_distance_conflict e u1 u2 2 hd hs hw1 hw2
    · have hd : (3 : Nat) = 1 ∨ (3 : Nat) = 2 ∨ (3 : Nat) = 3 ∨ (3 : Nat) = 4 := by omega
      have hs : u2 = u1 + (3 : Nat) := by omega
      exact lag7_distance_conflict e u1 u2 3 hd hs hw1 hw2
    · have hd : (4 : Nat) = 1 ∨ (4 : Nat) = 2 ∨ (4 : Nat) = 3 ∨ (4 : Nat) = 4 := by omega
      have hs : u2 = u1 + (4 : Nat) := by omega
      exact lag7_distance_conflict e u1 u2 4 hd hs hw1 hw2
theorem lag7_non_consecutive_distance_ge_ten (u1 u2 u3 : Int)
    (h12 : u1 + 5 ≤ u2)
    (h23 : u2 + 5 ≤ u3) :
    u1 + 10 ≤ u3 := by
  omega

/-- Master Synthesis: Grand Lag 7 Distance Separation Rigidity Theorem. -/
theorem grand_lag7_distance_separation_rigidity_synthesis
    (e : Int → Bool) (u1 u2 u3 : Int)
    (hu12 : u1 < u2) (hu23 : u2 < u3)
    (hw1 : past e u1 7 = w1 ∨ past e u1 7 = w2)
    (hw2 : past e u2 7 = w1 ∨ past e u2 7 = w2)
    (hw3 : past e u3 7 = w1 ∨ past e u3 7 = w2) :
    -- (1) Distance ≥ 5 for consecutive additions
    (u1 + 5 ≤ u2) ∧
    (u2 + 5 ≤ u3) ∧
    -- (2) Distance ≥ 10 for non-consecutive additions
    (u1 + 10 ≤ u3) := by
  have hd12 := lag7_stream_distance_ge_five e u1 u2 hu12 hw1 hw2
  have hd23 := lag7_stream_distance_ge_five e u2 u3 hu23 hw2 hw3
  have hd13 := lag7_non_consecutive_distance_ge_ten u1 u2 u3 hd12 hd23
  exact ⟨hd12, hd23, hd13⟩

#print axioms conflict_d1_w1_w1
#print axioms conflict_d1_w1_w2
#print axioms conflict_d1_w2_w1
#print axioms conflict_d1_w2_w2
#print axioms conflict_d2_w1_w1
#print axioms conflict_d2_w1_w2
#print axioms conflict_d2_w2_w1
#print axioms conflict_d2_w2_w2
#print axioms conflict_d3_w1_w1
#print axioms conflict_d3_w1_w2
#print axioms conflict_d3_w2_w1
#print axioms conflict_d3_w2_w2
#print axioms conflict_d4_w1_w1
#print axioms conflict_d4_w1_w2
#print axioms conflict_d4_w2_w1
#print axioms conflict_d4_w2_w2
#print axioms lag7_distance_conflict
#print axioms lag7_stream_distance_ge_five
#print axioms lag7_non_consecutive_distance_ge_ten
#print axioms grand_lag7_distance_separation_rigidity_synthesis

end Recaman.LagSevenDistanceSeparationRigidity
