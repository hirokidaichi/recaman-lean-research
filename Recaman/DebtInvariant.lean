import Recaman.PhaseSearch

namespace Recaman

/-- Semantic data carried by a debt node.

The strict value bound is essential: on a forced-addition final transition,
the predecessor is smaller than `value`, and hence is a valid strictly smaller
anchor for returning to normal search. -/
structure DebtInvariant (target : Nat) (node : PhaseSearchNode)
    (value firstTime : Nat) : Prop where
  phase_eq : node.phase = .debt
  local_eq : node.localMeasure = firstTime
  target_le : target ≤ value
  first : FirstAt a value firstTime
  firstTime_lt_horizon : firstTime < node.horizon
  value_lt_anchor : value < node.anchorParent

/-- At time zero the only possible first-occurrence value is zero. -/
theorem firstAt_time_zero_value {value : Nat}
    (hfirst : FirstAt a value 0) : value = 0 := by
  simpa [FirstAt, a, stateAt, initial] using hfirst.1.symm

/-- A first occurrence at positive time is produced by exactly the actual
Recamán transition taken at its final step. -/
theorem firstAt_succ_transition {value n : Nat}
    (hfirst : FirstAt a value (n + 1)) :
    (CanSubtract (n + 1) (stateAt n) ∧
        value = a n - (n + 1)) ∨
      (¬ CanSubtract (n + 1) (stateAt n) ∧
        value = a n + (n + 1)) := by
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · left
    exact ⟨hcan, hfirst.1.symm.trans (a_succ_of_canSubtract hcan)⟩
  · right
    have hstep := a_succ_of_not_canSubtract hcan
    exact ⟨hcan, hfirst.1.symm.trans hstep⟩

/-- Failure of subtraction has precisely the two causes visible in the
definition: the candidate is nonpositive, or it is already in history. -/
theorem not_canSubtract_cases {n : Nat}
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    a n ≤ n + 1 ∨ a n - (n + 1) ∈ valuesThrough n := by
  by_cases hpositive : n + 1 < a n
  · right
    by_cases hseen : a n - (n + 1) ∈ valuesThrough n
    · exact hseen
    · exact False.elim
        (hnot ⟨by simpa [a] using hpositive, hseen⟩)
  · left
    exact Nat.le_of_not_gt hpositive

/-- Complete three-way classification of the final transition of a first
occurrence: the initial value, a legal subtraction, or a forced addition.
The forced-addition branch records why subtraction was unavailable. -/
theorem firstAt_final_transition {value firstTime : Nat}
    (hfirst : FirstAt a value firstTime) :
    (firstTime = 0 ∧ value = 0) ∨
      (∃ n, firstTime = n + 1 ∧
        CanSubtract (n + 1) (stateAt n) ∧
        value = a n - (n + 1)) ∨
      (∃ n, firstTime = n + 1 ∧
        ¬ CanSubtract (n + 1) (stateAt n) ∧
        value = a n + (n + 1) ∧
        (a n ≤ n + 1 ∨ a n - (n + 1) ∈ valuesThrough n)) := by
  cases firstTime with
  | zero =>
      exact Or.inl ⟨rfl, firstAt_time_zero_value hfirst⟩
  | succ n =>
      rcases firstAt_succ_transition hfirst with
        ⟨hcan, hvalue⟩ | ⟨hnot, hvalue⟩
      · exact Or.inr (Or.inl ⟨n, rfl, hcan, hvalue⟩)
      · exact Or.inr (Or.inr
          ⟨n, rfl, hnot, hvalue, not_canSubtract_cases hnot⟩)

/-- A first occurrence at `n+1` is absent from the complete earlier history.
This is useful on both sides of the final-transition classification. -/
theorem firstAt_succ_not_mem_history {value n : Nat}
    (hfirst : FirstAt a value (n + 1)) :
    value ∉ valuesThrough n := by
  intro hmem
  rcases mem_valuesThrough_iff.mp hmem with ⟨t, ht, hvalue⟩
  exact hfirst.2 t (by omega) hvalue

/-- Positive targets rule out the time-zero branch for a valid debt node. -/
theorem debt_firstTime_pos
    {target value firstTime : Nat} {node : PhaseSearchNode}
    (htarget : 0 < target)
    (hinv : DebtInvariant target node value firstTime) :
    0 < firstTime := by
  by_cases hzero : firstTime = 0
  · subst firstTime
    have hvalue := firstAt_time_zero_value hinv.first
    have htargetle := hinv.target_le
    omega
  · omega

/-- Any node satisfying the strong debt invariant can return to normal mode
at its own first-occurring value: the target lower bound is preserved and the
stored value is already strictly below the anchor.  Thus the hard global
problem is not local debt totality, but constructing this strong invariant by
a rank-decreasing step from the preceding normal node. -/
theorem debtInvariant_exitNormal_at_value
    {target horizon anchor value firstTime : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, firstTime⟩ value firstTime) :
    target ≤ value ∧ FirstAt a value firstTime ∧
      PhaseSearchProgress target
        ⟨horizon, value, .normal, value⟩
        ⟨horizon, anchor, .debt, firstTime⟩ := by
  exact ⟨hinv.target_le, hinv.first,
    phaseSearch_exitDebt_of_anchorDrop hinv.value_lt_anchor⟩

/-- On the legal-subtraction branch, the predecessor has an earlier first
occurrence and is strictly larger than the debt value.  This always decreases
the rank's debt-time component, even though the predecessor need not remain
below the fixed anchor. -/
theorem debt_legalSubtraction_earlierPredecessor
    {target horizon anchor value n : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    ∃ predecessorTime,
      FirstAt a (a n) predecessorTime ∧
      predecessorTime < n + 1 ∧
      value < a n ∧
      PhaseSearchProgress target
        ⟨horizon, anchor, .debt, predecessorTime⟩
        ⟨horizon, anchor, .debt, n + 1⟩ := by
  have hstep := a_succ_of_canSubtract hcan
  have hvalue : value = a n - (n + 1) :=
    hinv.first.1.symm.trans hstep
  have hpositive : n + 1 < a n := by
    simpa [a] using hcan.1
  rcases history_member_has_firstAt (current_mem_valuesThrough n) with
    ⟨predecessorTime, htime, hfirst⟩
  refine ⟨predecessorTime, hfirst, by omega, ?_,
    phaseSearch_debtTimeDrop (by omega)⟩
  omega

/-- The legal-subtraction predecessor is again a semantically valid debt node
exactly when one additionally knows that it remains below the fixed anchor. -/
theorem debt_legalSubtraction_preservesInvariant
    {target horizon anchor value n predecessorTime : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hcan : CanSubtract (n + 1) (stateAt n))
    (hfirstPredecessor : FirstAt a (a n) predecessorTime)
    (htime : predecessorTime < n + 1)
    (hanchor : a n < anchor) :
    DebtInvariant target
      ⟨horizon, anchor, .debt, predecessorTime⟩
      (a n) predecessorTime ∧
    PhaseSearchProgress target
      ⟨horizon, anchor, .debt, predecessorTime⟩
      ⟨horizon, anchor, .debt, n + 1⟩ := by
  have hpositive : n + 1 < a n := by
    simpa [a] using hcan.1
  have hstep := a_succ_of_canSubtract hcan
  have hvalue : value = a n - (n + 1) :=
    hinv.first.1.symm.trans hstep
  constructor
  · refine {
      phase_eq := rfl
      local_eq := rfl
      target_le := ?_
      first := hfirstPredecessor
      firstTime_lt_horizon := ?_
      value_lt_anchor := hanchor
    }
    · have : value < a n := by omega
      exact Nat.le_trans hinv.target_le (Nat.le_of_lt this)
    · exact Nat.lt_trans htime hinv.firstTime_lt_horizon
  · exact phaseSearch_debtTimeDrop htime

/-- On the forced-addition branch of a valid debt node, the predecessor is
strictly below the fixed anchor and has an earlier first occurrence.  The
remaining arithmetic split says whether it is still above the target. -/
theorem debt_forcedAddition_predecessor
    {target horizon anchor value n : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    ∃ predecessorTime,
      FirstAt a (a n) predecessorTime ∧
      predecessorTime < n + 1 ∧
      a n < anchor ∧
      (a n < target ∨ target ≤ a n) := by
  have hstep := a_succ_of_not_canSubtract hnot
  have hvalue : value = a n + (n + 1) :=
    hinv.first.1.symm.trans hstep
  have hmem : a n ∈ valuesThrough n := current_mem_valuesThrough n
  rcases history_member_has_firstAt hmem with
    ⟨predecessorTime, htime, hfirst⟩
  refine ⟨predecessorTime, hfirst, by omega, ?_, ?_⟩
  · have : a n < value := by omega
    exact Nat.lt_trans this hinv.value_lt_anchor
  · exact Nat.lt_or_ge (a n) target

/-- If the forced-addition predecessor remains above the target, changing
back to normal phase strictly lowers the phase-search rank via the anchor. -/
theorem debt_forcedAddition_exitProgress
    {target horizon anchor value n predecessorTime : Nat}
    (hinv : DebtInvariant target
      ⟨horizon, anchor, .debt, n + 1⟩ value (n + 1))
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (hfirstPredecessor : FirstAt a (a n) predecessorTime)
    (htarget : target ≤ a n) :
    target ≤ a n ∧ FirstAt a (a n) predecessorTime ∧
      PhaseSearchProgress target
        ⟨horizon, a n, .normal, a n⟩
        ⟨horizon, anchor, .debt, n + 1⟩ := by
  have hstep := a_succ_of_not_canSubtract hnot
  have hvalue : value = a n + (n + 1) :=
    hinv.first.1.symm.trans hstep
  have hanchor : a n < anchor := by
    exact Nat.lt_trans (by omega : a n < value) hinv.value_lt_anchor
  exact ⟨htarget, hfirstPredecessor,
    phaseSearch_exitDebt_of_anchorDrop hanchor⟩

/-- The diagonal maximal-tail theorem enters debt with all semantic
invariants, provided the anchor is chosen to be the tail's starting value. -/
theorem diagonal_successor_or_validDebt {n normalLocal : Nat}
    (hdiagonal : a (n + 2) = n + 2) :
    (∃ u, a u = n + 3) ∨
      ∃ start y fy,
        DebtInvariant (n + 3)
          ⟨n + 2, a start, .debt, fy⟩ y fy ∧
        PhaseSearchProgress (n + 3)
          ⟨n + 2, a start, .debt, fy⟩
          ⟨n + 2, a start, .normal, normalLocal⟩ := by
  rcases diagonal_successor_occurs_or_longDescent hdiagonal with
    hoccurs | ⟨hpenultimate, _, _⟩
  · exact Or.inl hoccurs
  · rcases diagonal_longDescent_exposes_blocker
        hdiagonal hpenultimate with
      ⟨start, length, y, fy, hend, hlength, _, _, _,
        hyLower, hfirst, hyStart, hfyStart⟩
    refine Or.inr ⟨start, y, fy, ?_, phaseSearch_enterDebt⟩
    refine {
      phase_eq := rfl
      local_eq := rfl
      target_le := hyLower
      first := hfirst
      firstTime_lt_horizon := ?_
      value_lt_anchor := hyStart
    }
    change fy < n + 2
    omega

end Recaman
