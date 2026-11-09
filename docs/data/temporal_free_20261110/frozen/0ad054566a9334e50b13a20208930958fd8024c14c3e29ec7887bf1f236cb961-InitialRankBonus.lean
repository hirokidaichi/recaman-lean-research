import Recaman.EarlySubtractionFloor

namespace Recaman.InitialRankBonus

open Recaman.AdditionRankSlack Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private def rankBonus (r a : Nat) : Int := 4*((min (a-2) (r-2) : Nat) : Int)

private theorem rankBonus_step (r a : Nat) :
    rankBonus r (a+1)=rankBonus r a+(if 2≤a ∧ a<r then 4 else 0) := by
  unfold rankBonus
  simp only [Nat.min_def]
  split <;> split <;> split <;> omega

/-- The third through the r-th addition all pay for the second S when
their ordinary rank floor is still one. This charge holds at every rank. -/
theorem initial_two_subtraction_bonus (f : Nat → Bool) (n r K : Nat)
    (hp : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤subtractions f n k)
    (hf : free f n K≤r) :
    4*((min (additions f n K-2) (r-2) : Nat) : Int)≤rankSlack f n r K := by
  change rankBonus r (additions f n K)≤rankSlack f n r K
  suffices h : ∀ k, k≤K → rankBonus r (additions f n k)≤rankSlack f n r k from h K (Nat.le_refl _)
  intro k hk
  induction k with
  | zero =>
    rw [rankSlack_zero]
    simp [rankBonus,additions,cN]
  | succ k ih =>
    have h0:=ih (by omega)
    cases hs : f (n+k) with
    | false =>
      have ha : additions f n (k+1)=additions f n k := cN_succ_neg _ n k (by rw [hs]; decide)
      rw [ha,rankSlack_step_S f n r k hs]
      exact h0
    | true =>
      have ha : additions f n (k+1)=additions f n k+1 := cN_succ_pos _ n k hs
      rw [ha,rankBonus_step]
      by_cases hc : 2≤additions f n k ∧ additions f n k<r
      · have hS:=Recaman.EarlySubtractionFloor.two_subtractions_of_three_additions f n (k+1)
          (fun t ht htk=>hp t ht (by omega)) (by omega)
        have hsc : subtractions f n (k+1)=subtractions f n k :=
          cN_succ_neg _ n k (by rw [hs]; decide)
        rw [if_pos hc,rankSlack_step_A f n r k hs,ha]
        omega
      · have hm:=rankSlack_mono f n r K hp hf k (k+1) (by omega) hk
        rw [if_neg hc]
        omega

end Recaman.InitialRankBonus
