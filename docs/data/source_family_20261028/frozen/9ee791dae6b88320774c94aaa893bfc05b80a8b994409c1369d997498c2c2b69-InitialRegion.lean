import Recaman.CoordinateDynamics

namespace Recaman

/-- Every target `m ≥ 2` has, at time `m-1` or `m`, an actual state whose
value is at least `m` and whose time already satisfies the epoch precondition
`m ≤ n+1`.  The state is returned with canonical coordinates and a first
occurrence of its current value.

If `a (m-1)` is below the target, step `m` cannot subtract and therefore
forces an addition past the target.  This gives a target-uniform entry into
the region used by the sign-epoch lemmas, without enumerating small targets. -/
theorem exists_targetReady_state {m : Nat} (hm : 2 ≤ m) :
    ∃ n q r f,
      (n = m - 1 ∨ n = m) ∧
      m ≤ n + 1 ∧
      m ≤ a n ∧
      CoordinatesAt n q r ∧
      f ≤ n ∧ FirstAt a (a n) f := by
  by_cases habove : m ≤ a (m - 1)
  · have hnpos : 0 < m - 1 := by omega
    rcases exists_coordinatesAt (n := m - 1) hnpos with
      ⟨q, r, hcoord⟩
    rcases history_member_has_firstAt
        (current_mem_valuesThrough (m - 1)) with
      ⟨f, hf, hfirst⟩
    exact ⟨m - 1, q, r, f, Or.inl rfl, by omega, habove,
      hcoord, hf, hfirst⟩
  · have hbelow : a (m - 1) < m := Nat.lt_of_not_ge habove
    have hnot : ¬ CanSubtract m (stateAt (m - 1)) := by
      intro hcan
      have hpositive : m < a (m - 1) := by
        simpa [a] using hcan.1
      omega
    have htime : (m - 1) + 1 = m := by omega
    have hnot' : ¬ CanSubtract ((m - 1) + 1) (stateAt (m - 1)) := by
      simpa [htime] using hnot
    have hstep := a_succ_of_not_canSubtract hnot'
    have hvalue : a m = a (m - 1) + m := by
      simpa [htime] using hstep
    have hmvalue : m ≤ a m := by omega
    rcases exists_coordinatesAt (n := m) (by omega) with
      ⟨q, r, hcoord⟩
    rcases history_member_has_firstAt
        (current_mem_valuesThrough m) with
      ⟨f, hf, hfirst⟩
    exact ⟨m, q, r, f, Or.inr rfl, by omega, hmvalue,
      hcoord, hf, hfirst⟩

/-- Positive-target form of `exists_targetReady_state`.  The only additional
case is `m=1`, witnessed directly at time one. -/
theorem exists_targetReady_state_of_pos {m : Nat} (hm : 0 < m) :
    ∃ n q r f,
      (n = m - 1 ∨ n = m) ∧
      m ≤ n + 1 ∧
      m ≤ a n ∧
      CoordinatesAt n q r ∧
      f ≤ n ∧ FirstAt a (a n) f := by
  by_cases htwo : 2 ≤ m
  · exact exists_targetReady_state htwo
  · have hmone : m = 1 := by omega
    subst m
    rcases exists_coordinatesAt (n := 1) (by omega) with
      ⟨q, r, hcoord⟩
    rcases history_member_has_firstAt
        (current_mem_valuesThrough 1) with
      ⟨f, hf, hfirst⟩
    exact ⟨1, q, r, f, Or.inr rfl, by omega, by decide,
      hcoord, hf, hfirst⟩

end Recaman
