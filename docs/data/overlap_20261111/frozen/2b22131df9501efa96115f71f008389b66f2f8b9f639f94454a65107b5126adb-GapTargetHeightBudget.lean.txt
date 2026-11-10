import Recaman.AdditionRankSlack

namespace Recaman.GapTargetHeightBudget

open Recaman.BlockSuffixPositivity Recaman.CapacityEqualityInduction
open Recaman.SingleWindowEquality Recaman.BlockOldRay Recaman.AdditionRankSlack

/-- A final run of subtractions to a supplied target stays at least two
levels above any lower bound for the preceding tail. -/
theorem supplied_gap_target_above_floor (f : Nat → Bool) (n a b j : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n≤b) (hfloor : ∀ i, n≤i → i≤b → m≤Fw f i)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j)) :
    m+2≤Fw f (b+j) ∧ (j : Int)+m+2≤Fw f b := by
  have hlast := fw_false_run f b j hS
  let L := min m (Fw f (b+j))
  have hl (i : Nat) (hni : n≤i) (hic : i≤b+j) : L≤Fw f i := by
    by_cases hi : i≤b
    · exact Int.le_trans (Int.min_le_left _ _) (hfloor i hni hi)
    · have hwalk := fw_false_run f b (i-b) (fun t ht hti => hS t ht (by omega))
      rw [show b+(i-b)=i by omega] at hwalk
      have hle : Fw f (b+j)≤Fw f i := by omega
      exact Int.le_trans (Int.min_le_right _ _) hle
  have htop : L+2≤Fw f (b+j) := by
    by_cases h : L+2≤Fw f (b+j)
    · exact h
    · exact (block_prefix_low_clock_not_endable f n a (b+j) hw hpre (by omega) L hl
        (by omega) he).elim
  have hm : m≤Fw f (b+j) := by
    by_cases h : m≤Fw f (b+j)
    · exact h
    · dsimp [L] at htop
      rw [Int.min_eq_right (by omega)] at htop
      omega
  dsimp [L] at htop
  rw [Int.min_eq_left hm] at htop
  exact ⟨htop,by omega⟩

/-- The full positive free gap holds for any number of runs in a strip
of width five. The final target bounds the gap before the low-free input. -/
theorem positive_width_five_free_gap (f : Nat → Bool) (n a b j : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → m≤Fw f i)
    (hceiling : Fw f b≤m+5)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j)) :
    j+1≤free f n (b-n) := by
  have hJ := (supplied_gap_target_above_floor f n a b j m hw hpre (by omega) hfloor hS he).2
  by_cases hfree : free f n (b-n)≤3
  · apply positive_r3_free_gap f n a (b-n) j hw hpre (by omega) hpos hfree
    · rw [show n+(b-n)=b by omega]
      exact hS
    · rwa [show n+(b-n)=b by omega]
  · omega

end Recaman.GapTargetHeightBudget
