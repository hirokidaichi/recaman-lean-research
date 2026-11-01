import Recaman.RecoveryFrontier

namespace Recaman

/-- The finite negative epoch has a sharp frontier: within `⌊r/2⌋` steps it
reaches a one-borrow transition which strictly raises the potential, and its
endpoint either is nonnegative or has quotient at least four. -/
theorem eventually_oneBorrow_frontier {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hnegative : potential q r < 0) :
    ∃ t q' r' s k,
      n ≤ t ∧ t ≤ n + r / 2 ∧
      CoordinatesAt t q' r' ∧ BorrowData t q' r' 1 s ∧
      CoordinatesAt (t + 1) k s ∧
      potential q' r' < potential k s ∧
      (0 ≤ potential k s ∨ 4 ≤ k) := by
  rcases eventually_oneBorrow_of_negative_halfRemainder hcoord hnegative with
    ⟨t, q', r', s, hnt, htbound, htcoord, htborrow⟩
  by_cases hcan : CanSubtract (t + 1) (stateAt t)
  · have hpositive : t + 1 < a t := by simpa [a] using hcan.1
    have hbq : 1 + 1 ≤ q' :=
      htborrow.add_one_le_q_of_positive htcoord hpositive
    have hnext := coordinates_sub_borrowData htcoord htborrow hbq hcan
    have hrise :=
      coordinates_sub_oneBorrow_potential_lt htcoord htborrow rfl hcan
    have hfrontier :
        0 ≤ potential (q' - 1 - 1) s ∨ 4 ≤ q' - 1 - 1 := by
      by_cases hlow : q' - 1 - 1 ≤ 3
      · exact Or.inl
          (coordinates_sub_oneBorrow_lowQuotient_nonnegative
            htcoord htborrow rfl hcan hlow)
      · exact Or.inr (by omega)
    exact ⟨t, q', r', s, q' - 1 - 1, hnt, htbound,
      htcoord, htborrow, hnext.1, hrise, hfrontier⟩
  · have hbq : 1 ≤ q' + 1 := by omega
    have hnext := coordinates_add_borrowData htcoord htborrow hbq hcan
    have hrise := coordinates_add_oneBorrow_potential_lt htcoord htborrow rfl
    have hfrontier :
        0 ≤ potential (q' + 1 - 1) s ∨ 4 ≤ q' + 1 - 1 := by
      by_cases hlow : q' ≤ 3
      · exact Or.inl
          (coordinates_add_oneBorrow_lowQuotient_nonnegative
            htcoord htborrow rfl hlow hcan)
      · exact Or.inr (by omega)
    exact ⟨t, q', r', s, q' + 1 - 1, hnt, htbound,
      htcoord, htborrow, hnext.1, hrise, hfrontier⟩

/-- Every negative epoch therefore reaches an actual one-borrow step whose
endpoint potential is strictly larger than its pre-state potential. -/
theorem eventually_oneBorrow_potential_rise {n q r : Nat}
    (hcoord : CoordinatesAt n q r) (hnegative : potential q r < 0) :
    ∃ t q' r' s k,
      n ≤ t ∧ t ≤ n + r / 2 ∧
      CoordinatesAt t q' r' ∧ BorrowData t q' r' 1 s ∧
      CoordinatesAt (t + 1) k s ∧
      potential q' r' < potential k s := by
  rcases eventually_oneBorrow_frontier hcoord hnegative with
    ⟨t, q', r', s, k, hnt, htbound, htcoord, htborrow,
      hnext, hrise, _⟩
  exact ⟨t, q', r', s, k, hnt, htbound, htcoord, htborrow, hnext, hrise⟩

end Recaman
