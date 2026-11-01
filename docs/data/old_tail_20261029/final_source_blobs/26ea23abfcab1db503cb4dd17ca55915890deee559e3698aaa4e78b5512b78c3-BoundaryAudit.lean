import Recaman.CrossingGap
import Recaman.NormalClosure

namespace Recaman

/-! # Boundary audit

Small interface lemmas and concrete counterexamples for the residual crossing
and negative-normal obligations.  This module intentionally does not change
the production invariants: it records exactly which conclusions follow from
their current fields.
-/

/-- A diagonal catch-up may advance one step beyond the stored horizon, but
that step cannot change the below-target history budget: its new value is at
least the target.  A child using catch-up history must therefore use horizon
`catchTime`, rather than silently reading that history at the old horizon. -/
theorem diagonalCrossingCatchup_budget_eq_horizon
    {horizon anchor catchTime quotient remainder firstTime : Nat}
    (hcatch : CrossingCatchup (horizon + 1) horizon anchor catchTime
      quotient remainder firstTime) :
    missingBelowCount (horizon + 1) catchTime =
      missingBelowCount (horizon + 1) horizon := by
  rcases hcatch.time_eq with htime | htime
  · have : catchTime = horizon := by omega
    subst catchTime
    rfl
  · have : catchTime = horizon + 1 := by omega
    subst catchTime
    exact missingBelowCount_succ_of_new_ge hcatch.target_le_value

/-- The quotient-one debt alternative returned by the rank-only epoch API is
impossible for a full `NormalPhaseInvariantAt`.  In its exceptional branch
one has `n=t`, `target=t+1`, and `a t=t`, contradicting the invariant's
otherwise-unused lower bound `target ≤ a n`. -/
theorem normalPhase_qOneDebt_already_occurs
    {target activeParent n q r t remainder landing : Nat}
    (hinv : NormalPhaseInvariantAt target
      ⟨n, activeParent, .normal, a n⟩ n q r)
    (hnt : n ≤ t)
    (htvalue : a t ≤ a n)
    (htcoord : CoordinatesAt t 1 remainder)
    (htborrow : BorrowData t 1 remainder 1 landing)
    (hnonnegative : 0 ≤ potential 1 landing)
    (hbelow : potential 1 landing < Int.ofNat target) :
    ∃ u, a u = target := by
  rcases qOneDebt_target_or_diagonalSuccessor
      hinv.time_ready hnt htcoord htborrow hnonnegative hbelow with
    hoccurs | ⟨hntEq, htargetEq, hdiagonal⟩
  · exact hoccurs
  · subst n
    subst target
    have htarget := hinv.target_le_value
    omega

private theorem firstAt_three_two_boundaryAudit : FirstAt a 3 2 := by
  constructor
  · decide
  · intro u hu
    have hcases : u = 0 ∨ u = 1 := by omega
    rcases hcases with h | h <;> subst u <;> decide

private def boundaryAuditParent : PhaseSearchNode :=
  ⟨3, 7, .normal, a 3⟩

private def boundaryAuditDropChild : PhaseSearchNode :=
  ⟨4, 3, .normal, a 4⟩

private def boundaryAuditEpochChild : PhaseSearchNode :=
  ⟨4, 7, .normal, a 4⟩

private theorem boundaryAuditParent_valid :
    NormalPhaseInvariantAt 3 boundaryAuditParent 3 2 0 := by
  constructor
  · rfl
  · decide
  · decide
  · decide
  · exact ⟨by decide, by decide⟩
  · decide

private theorem boundaryAuditDrop_progress :
    PhaseSearchProgress 3 boundaryAuditDropChild boundaryAuditParent := by
  apply Prod.Lex.left
  change missingBelowCount 3 4 < missingBelowCount 3 3
  decide

private theorem boundaryAuditEpoch_progress :
    PhaseSearchProgress 3 boundaryAuditEpochChild boundaryAuditParent := by
  apply Prod.Lex.left
  change missingBelowCount 3 4 < missingBelowCount 3 3
  decide

private theorem boundaryAuditDrop_evidence :
    NormalParentDropEvidence 3 4 3 2 boundaryAuditParent
      boundaryAuditDropChild := by
  constructor
  · rfl
  · decide
  · exact firstAt_three_two_boundaryAudit
  · decide
  · exact boundaryAuditDrop_progress

private theorem boundaryAuditEpoch_evidence :
    NormalEpochExitEvidence 3 4 0 2 boundaryAuditParent
      boundaryAuditEpochChild := by
  constructor
  · rfl
  · decide
  · decide
  · exact ⟨by decide, by decide⟩
  · exact boundaryAuditEpoch_progress

private theorem boundaryAuditDrop_not_closed :
    ¬ NormalPhaseInvariant 3 boundaryAuditDropChild := by
  rintro ⟨n, q, r, hinv⟩
  have hn : n = 4 := by
    simpa [boundaryAuditDropChild] using
      (congrArg PhaseSearchNode.horizon hinv.node_eq).symm
  subst n
  exact (by decide : ¬ 3 ≤ a 4) hinv.target_le_value

private theorem boundaryAuditEpoch_not_closed :
    ¬ NormalPhaseInvariant 3 boundaryAuditEpochChild := by
  rintro ⟨n, q, r, hinv⟩
  have hn : n = 4 := by
    simpa [boundaryAuditEpochChild] using
      (congrArg PhaseSearchNode.horizon hinv.node_eq).symm
  subst n
  exact (by decide : ¬ 3 ≤ a 4) hinv.target_le_value

/-- `NormalParentDropEvidence` does not by itself reconstruct the strong
negative-normal invariant, even when the parent is valid.  On the real orbit,
the history-budget drop from time three to four permits a rank step whose new
orbit value is `a 4 = 2 < 3`. -/
theorem normalParentDropEvidence_not_sufficient :
    NormalPhaseInvariantAt 3 boundaryAuditParent 3 2 0 ∧
      NormalParentDropEvidence 3 4 3 2 boundaryAuditParent
        boundaryAuditDropChild ∧
      ¬ NormalPhaseInvariant 3 boundaryAuditDropChild := by
  exact ⟨boundaryAuditParent_valid, boundaryAuditDrop_evidence,
    boundaryAuditDrop_not_closed⟩

/-- `NormalEpochExitEvidence` likewise does not imply the strong invariant.
The same actual transition `a 3 = 6` to `a 4 = 2` is forward and rank
decreasing, but loses the target lower bound. -/
theorem normalEpochExitEvidence_not_sufficient :
    NormalPhaseInvariantAt 3 boundaryAuditParent 3 2 0 ∧
      NormalEpochExitEvidence 3 4 0 2 boundaryAuditParent
        boundaryAuditEpochChild ∧
      ¬ NormalPhaseInvariant 3 boundaryAuditEpochChild := by
  exact ⟨boundaryAuditParent_valid, boundaryAuditEpoch_evidence,
    boundaryAuditEpoch_not_closed⟩

/-- If an orbit segment starts at or above a target and finishes below it,
then it either hits the target on that segment or consumes a previously
missing below-target value.  At the first downward crossing, forced addition
is arithmetically impossible; legal subtraction makes its endpoint fresh in
the preceding history. -/
theorem orbit_downcrossing_occurs_or_budgetDrop
    {target start finish : Nat}
    (htime : start ≤ finish)
    (hstart : target ≤ a start)
    (hfinish : a finish < target) :
    (∃ u, start ≤ u ∧ u ≤ finish ∧ a u = target) ∨
      missingBelowCount target finish <
        missingBelowCount target start := by
  have aux : ∀ d : Nat, a (start + d) < target →
      (∃ u, start ≤ u ∧ u ≤ start + d ∧ a u = target) ∨
        missingBelowCount target (start + d) <
          missingBelowCount target start := by
    intro d
    induction d with
    | zero =>
        intro hbelow
        simp only [Nat.add_zero] at hbelow
        omega
    | succ d ih =>
        intro hbelow
        simp only [Nat.add_succ] at hbelow ⊢
        by_cases heq : a (start + d) = target
        · exact Or.inl ⟨start + d, by omega, by omega, heq⟩
        · by_cases hpreviousBelow : a (start + d) < target
          · rcases ih hpreviousBelow with hoccurs | hdrop
            · rcases hoccurs with ⟨u, hstartU, huFinish, hu⟩
              exact Or.inl ⟨u, hstartU, by omega, hu⟩
            · exact Or.inr (Nat.lt_of_le_of_lt
                (missingBelowCount_antitone (m := target)
                  (show start + d ≤ start + d + 1 by omega)) hdrop)
          · have hpreviousAbove : target < a (start + d) := by omega
            by_cases hcan :
                CanSubtract (start + d + 1) (stateAt (start + d))
            · have hsub := a_succ_of_canSubtract hcan
              have hnew :
                  a (start + d + 1) ∉ valuesThrough (start + d) := by
                rw [hsub]
                exact hcan.2
              have hstrict :
                  missingBelowCount target (start + d + 1) <
                    missingBelowCount target (start + d) :=
                missingBelowCount_strict_of_new hbelow (by omega) hnew
                  (current_mem_valuesThrough (start + d + 1))
              have hbase := missingBelowCount_antitone
                (m := target) (show start ≤ start + d by omega)
              exact Or.inr (Nat.lt_of_lt_of_le hstrict hbase)
            · have hadd := a_succ_of_not_canSubtract hcan
              have hadd' :
                  a (start + d).succ =
                    a (start + d) + (start + d + 1) := by
                simpa using hadd
              omega
  have hfinishEq : start + (finish - start) = finish := by omega
  have hresult := aux (finish - start)
  rw [hfinishEq] at hresult
  exact hresult hfinish

/-- The sharp epoch-exit case is not a residual failure.  Along its forward
orbit segment, a below-target endpoint would force either target occurrence
or a strict budget drop; the latter contradicts the obstruction's budget
equality. -/
theorem NormalEpochSharpObstruction.target_occurs
    {target start activeParent finish : Nat}
    (h : NormalEpochSharpObstruction target start activeParent finish)
    (htime : start ≤ finish) :
    ∃ u, a u = target := by
  rcases orbit_downcrossing_occurs_or_budgetDrop htime
      (Nat.le_of_lt h.old_value_above_target)
      h.new_value_below_target with
    hoccurs | hdrop
  · rcases hoccurs with ⟨u, _, _, hu⟩
    exact ⟨u, hu⟩
  · rw [h.budget_unchanged] at hdrop
    omega

end Recaman
