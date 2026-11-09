import Recaman.FifthAdditionPrefixShape
import Recaman.ThresholdPrefixFreeCount

namespace Recaman.RankThreeEarlyFree

open Recaman.AdditionRankSlack Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic Recaman.CapacityEqualityInduction

private theorem rank_slack_divisible (f : Nat → Bool) (n r K : Nat) :
    rankSlack f n r K%4=0 := by
  induction K with
  | zero => rw [rankSlack_zero]; decide
  | succ K ih =>
    cases h : f (n+K) with
    | false => rwa [rankSlack_step_S f n r K h]
    | true => rw [rankSlack_step_A f n r K h]; omega

private theorem early_four_free (f : Nat → Bool) (n k : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hk : 8≤k)
    (h : (seg f n k).take 6=[false,true,true,false,true,true] ∨
      (seg f n k).take 8=[false,true,false,true,true,true,false,true] ∨
      (seg f n k).take 7=[false,true,true,false,true,false,true]) : 4≤free f n k := by
  rcases h with h6|h8|h7
  · rw [seg_take f n k 6 (by omega)] at h6
    have hf:=Recaman.ThresholdPrefixFreeCount.four_free_short_prefixes f n 6 w hw hpre (Or.inl ⟨rfl,h6⟩)
    exact Nat.le_trans hf (free_prefix_mono f n 6 k (by omega))
  · rw [seg_take f n k 8 hk] at h8
    have hf:=Recaman.ThresholdPrefixFreeCount.four_free_short_prefixes f n 8 w hw hpre (Or.inr (Or.inl ⟨rfl,h8⟩))
    exact Nat.le_trans hf (free_prefix_mono f n 8 k hk)
  · rw [seg_take f n k 7 (by omega)] at h7
    have hf:=Recaman.ThresholdPrefixFreeCount.four_free_short_prefixes f n 7 w hw hpre (Or.inr (Or.inr ⟨rfl,h7⟩))
    exact Nat.le_trans hf (free_prefix_mono f n 7 k (by omega))

/-- At the third free rank, five additions have at least three extra
S-before-A pairs above the ordinary rank floor. -/
theorem rank_three_slack_at_five (f : Nat → Bool) (n K : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n K≤3) (ha : 5≤additions f n K) :
    12≤rankSlack f n 3 K := by
  by_cases h : 12≤rankSlack f n 3 K
  · exact h
  · have hd:=rank_slack_divisible f n 3 K
    have h8 : rankSlack f n 3 K≤8 := by omega
    obtain ⟨k,hk,h5,hl,he⟩:=Recaman.RankThreeFifthWindow.fifth_window_at_small_slack f n K hp hf ha h8
    have hk8 : 8≤k := by rcases he with ⟨h,_⟩|⟨h,_⟩ <;> omega
    have hS:=Recaman.EarlySubtractionFloor.first_subtraction f n K (by omega) hp
    have hhead : (seg f n k).head?=some false := by
      have he (xs : List Bool) : xs.head?=xs[0]? := by cases xs <;> rfl
      rw [he,seg_get f n k 0 (by omega),Nat.add_zero,hS]
    have hA4 : additions f n 4≤2 := by
      by_cases h0 : 3≤additions f n 4
      · have hs:=Recaman.EarlySubtractionFloor.two_subtractions_of_three_additions f n 4
          (fun t ht ht4=>hp t ht (by omega)) h0
        have ht : additions f n 4+subtractions f n 4=4 := (cN_walk f n 4).2
        omega
      · omega
    have hcap : ones ((seg f n k).take 4)≤2 := by
      rw [seg_take f n k 4 (by omega),ones_seg_eq_count]
      change (additions f n 4 : Int)≤2
      omega
    have hOne : ones (seg f n k)=5 := by rw [ones_seg_eq_count]; exact_mod_cast h5
    have hlast : (seg f n k)[k-1]?=some true := by
      rw [seg_get f n k (k-1) (by omega),hl]
    have hf4 : 4≤free f n k := by
      rcases he with ⟨rfl,hkey⟩|⟨rfl,hkey⟩
      · apply early_four_free f n 8 w hw hpre (by decide)
        exact Recaman.FifthAdditionPrefixShape.eight_fifth_prefix _ (seg_length _ _ _) hhead hlast hOne hkey hcap
      · apply early_four_free f n 9 w hw hpre (by decide)
        exact Recaman.FifthAdditionPrefixShape.nine_fifth_prefix _ (seg_length _ _ _) hhead hlast hOne hkey hcap
    have hm:=free_prefix_mono f n k K hk
    omega

end Recaman.RankThreeEarlyFree
