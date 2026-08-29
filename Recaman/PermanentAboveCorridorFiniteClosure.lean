import Recaman.PermanentAboveCorridorReplayBoundary

namespace Recaman

noncomputable section

/-! # Arithmetic elimination of the finite insufficient window

The final numeric residual is in fact impossible.  At the last internal
forced step, the insufficient predecessor bound implies that the preceding
orbit value is at most one.  The all-forced trace transports this bound back
to the fresh terminal endpoint.  Its positive first-occurrence time then
forces the endpoint to be exactly time one with value one.

Any longer suffix would add at least clock two and violate the same bound, so
the return time is exactly two.  The strict crossing is therefore
`a 2 = 3 < target < a 3 = 6`, leaving targets four and five.  Both already
occur in the actual orbit (`a 131 = 4`, `a 129 = 5`), contradicting the
missing-target field.  Thus the entire finite branch, including exact replay,
is eliminated without an additional hypothesis.
-/

theorem forcedClockSum_firstClock_le
    {start steps : Nat} (hsteps : 0 < steps) :
    start + 1 ≤ forcedClockSum start steps := by
  cases steps with
  | zero => omega
  | succ steps =>
      rw [forcedClockSum]
      omega

/-- The insufficient all-forced window has only the initial small shape. -/
theorem TerminalFiniteReturnWindowCertificate.endpoint_return_eq
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    terminalEndpoint = 1 ∧ source.returnTime = 2 := by
  let lastTime := source.returnTime - 1
  have hendpointPositive : 0 < terminalEndpoint := by
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ source.downTime)
      finite.origin_le
  have hendpointBefore := finite.window.certificate.endpoint_before_return
  have hendpointLeLast : terminalEndpoint ≤ lastTime := by
    dsimp [lastTime]
    omega
  have hlastBefore : lastTime < source.returnTime := by
    dsimp [lastTime]
    omega
  have hlastForced := finite.window.certificate.all_forced lastTime
    hendpointLeLast hlastBefore
  have hlastEquation := a_succ_of_not_canSubtract hlastForced
  have hlastSucc : lastTime + 1 = source.returnTime := by
    dsimp [lastTime]
    omega
  rw [hlastSucc] at hlastEquation
  have hlastSmall : a lastTime ≤ 1 := by
    have hpredecessor := finite.insufficient.predecessor_le_clock
    omega
  have htrace :=
    finite.window.certificate.all_forced.value_eq_add_forcedClockSum
      (steps := lastTime - terminalEndpoint) (by omega)
  have htraceTime : terminalEndpoint + (lastTime - terminalEndpoint) =
      lastTime := by omega
  rw [htraceTime] at htrace
  have hendpointSmall : a terminalEndpoint ≤ 1 := by omega
  have hendpointValue : a terminalEndpoint = 1 := by
    have hcases : a terminalEndpoint = 0 ∨ a terminalEndpoint = 1 := by
      omega
    rcases hcases with hzero | hone
    · have hsame : a 0 = a terminalEndpoint := by
        rw [hzero]
        rfl
      exact False.elim
        ((finite.window.certificate.suffix.endpoint_first.2 0
          hendpointPositive) hsame)
    · exact hone
  have hendpointEq : terminalEndpoint = 1 := by
    by_cases heq : terminalEndpoint = 1
    · exact heq
    · have honeBefore : 1 < terminalEndpoint := by omega
      have hsame : a 1 = a terminalEndpoint := by
        rw [hendpointValue]
        decide
      exact False.elim
        ((finite.window.certificate.suffix.endpoint_first.2 1 honeBefore)
          hsame)
  have hreturnLe : source.returnTime ≤ 2 := by
    by_cases hle : source.returnTime ≤ 2
    · exact hle
    · have hsteps : 0 < lastTime - terminalEndpoint := by
        dsimp [lastTime]
        omega
      have hsum := forcedClockSum_firstClock_le
        (start := terminalEndpoint) hsteps
      omega
  have hreturnEq : source.returnTime = 2 := by omega
  exact ⟨hendpointEq, hreturnEq⟩

theorem TerminalFiniteReturnWindowCertificate.target_eq_four_or_five
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    target = 4 ∨ target = 5 := by
  have hreturn := finite.endpoint_return_eq.2
  have hbelow := finite.window.predecessor_below
  have habove := finite.window.endpoint_above
  rw [hreturn] at hbelow habove
  have haTwo : a 2 = 3 := by decide
  have haThree : a 3 = 6 := by decide
  have hbelow' : 3 < target := by
    simpa [haTwo] using hbelow
  have habove' : target < 6 := by
    simpa [haThree] using habove
  omega

/-- Both arithmetically possible targets already occur in the actual orbit. -/
theorem TerminalFiniteReturnWindowCertificate.target_occurs
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    ∃ witness, a witness = target := by
  rcases finite.target_eq_four_or_five with rfl | rfl
  · exact ⟨131, by
      set_option maxRecDepth 100000 in
        decide⟩
  · exact ⟨129, by
      set_option maxRecDepth 100000 in
        decide⟩

/-- Hence no finite insufficient terminal certificate can inhabit a missing
permanent-tail counterexample. -/
theorem TerminalFiniteReturnWindowCertificate.false
    {target start : Nat} {parent : PhaseSearchNode}
    {source : PermanentTailDischargeReturnCertificate target start parent}
    {terminalEndpoint : Nat}
    (finite : TerminalFiniteReturnWindowCertificate source terminalEndpoint) :
    False :=
  finite.window.certificate.target_missing finite.target_occurs

/-- The formerly open replay resolver is now unconditional and vacuous. -/
theorem terminalExactCanonicalReplayResolver
    (target : Nat) : TerminalExactCanonicalReplayResolver target := by
  intro start parent source state terminalEndpoint finite residual
  exact False.elim finite.false

/-- Terminal classification with the impossible finite branch removed. -/
inductive PermanentTailTerminalFiniteClosedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    Prop
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      PermanentTailTerminalFiniteClosedOutcome source
  | immediate_semantic
      (valley : ImmediateHistoricalValleyCertificate target source.downTime
        source.returnTime)
      (insufficient : TerminalInsufficientValueCertificate target
        source.returnTime)
      (outcome : ImmediateTerminalSemanticOutcome target source.downTime
        source.returnTime) :
      PermanentTailTerminalFiniteClosedOutcome source
  | historical_complete
      (freshEndpoint candidate firstTime : Nat)
      (historical : TerminalOuterHistoricalBlockerCertificate source
        freshEndpoint candidate firstTime)
      (outcome : TerminalOuterHistoricalCompleteStepOutcome historical) :
      PermanentTailTerminalFiniteClosedOutcome source

theorem PermanentTailDischargeReturnCertificate.terminalFiniteClosedOutcome
    {target start : Nat} {parent : PhaseSearchNode}
    (source : PermanentTailDischargeReturnCertificate target start parent) :
    PermanentTailTerminalFiniteClosedOutcome source := by
  cases source.terminalSemanticallyClosedOutcome with
  | history_progress childTime parentTime progress =>
      exact .history_progress childTime parentTime progress
  | finite_return_candidate terminalEndpoint finite =>
      exact False.elim finite.false
  | immediate_semantic valley insufficient outcome =>
      exact .immediate_semantic valley insufficient outcome
  | historical_complete freshEndpoint candidate firstTime historical
      outcome =>
      exact .historical_complete freshEndpoint candidate firstTime historical
        outcome

end

end Recaman
