import Recaman.CoverageTimeBound
import Recaman.RefinedSuccessorRank
import Recaman.RefinedHistoryLanding
import Recaman.RefinedLandingMount

namespace Recaman

noncomputable section

/-! # Canonical discharge at the least permanent-above tail

The historical discharge certificate used to choose an arbitrary valid tail
start below the combined obstruction's start.  Every tail condition is upward
closed, so that choice carries no upper-bound information.  This module makes
the repair local: it wraps the existing discharge certificate together with a
proof that its `tailStart` is the least valid strict-above tail start.

No downstream certificate needs to be rewritten.  The construction below
runs the existing finite historical descent from the least tail.  The descent
may syntactically return an even earlier valid tail, but leastness forces that
tail to be the one we started with.  Thus all of the existing return,
crossing, and replay machinery is available through `discharge`, while the
missing upper-bound payload is retained by `tail_minimal`.
-/

/-! ## Uniform lower bound for a missing target and its coverage time -/

/-- Every target below nineteen already occurs in the kernel-range orbit. -/
theorem nineteen_le_of_target_missing {target : Nat}
    (hmissing : ¬ ∃ time, a time = target) : 19 ≤ target := by
  by_cases hsmall : target < 19
  · have hcases : target = 0 ∨ target = 1 ∨ target = 2 ∨ target = 3 ∨
        target = 4 ∨ target = 5 ∨ target = 6 ∨ target = 7 ∨ target = 8 ∨
        target = 9 ∨ target = 10 ∨ target = 11 ∨ target = 12 ∨ target = 13 ∨
        target = 14 ∨ target = 15 ∨ target = 16 ∨ target = 17 ∨
        target = 18 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hmissing ⟨0, by decide⟩)
    · exact False.elim (hmissing ⟨1, by decide⟩)
    · exact False.elim (hmissing ⟨4, by decide⟩)
    · exact False.elim (hmissing ⟨2, by decide⟩)
    · exact False.elim (hmissing ⟨131, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨129, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨3, by decide⟩)
    · exact False.elim (hmissing ⟨5, by decide⟩)
    · exact False.elim (hmissing ⟨16, by decide⟩)
    · exact False.elim (hmissing ⟨14, by decide⟩)
    · exact False.elim (hmissing ⟨12, by decide⟩)
    · exact False.elim (hmissing ⟨10, by decide⟩)
    · exact False.elim (hmissing ⟨8, by decide⟩)
    · exact False.elim (hmissing ⟨6, by decide⟩)
    · exact False.elim (hmissing ⟨31, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨29, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨27, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨25, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨23, by
        set_option maxRecDepth 100000 in decide⟩)
  · omega

/-- The late first occurrence used to pin low coverage boundaries. -/
theorem firstAt_four_131 : FirstAt a 4 131 := by
  have hunseen : 4 ∉ valuesThrough 130 := by
    set_option maxRecDepth 100000 in decide
  refine ⟨by
      set_option maxRecDepth 100000 in decide, ?_⟩
  intro earlier hearlier hvalueEarlier
  exact hunseen (mem_valuesThrough_iff.mpr
    ⟨earlier, by omega, hvalueEarlier⟩)

/-- All values below nineteen are present by clock 131. -/
theorem coversBelow_nineteen_131 : CoversBelow 19 131 := by
  intro value hvalue
  have hcases : value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
      value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7 ∨ value = 8 ∨
      value = 9 ∨ value = 10 ∨ value = 11 ∨ value = 12 ∨ value = 13 ∨
      value = 14 ∨ value = 15 ∨ value = 16 ∨ value = 17 ∨
      value = 18 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_valuesThrough_iff.mpr ⟨0, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨1, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨4, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨2, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨131, by omega, by
      set_option maxRecDepth 100000 in decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨129, by omega, by
      set_option maxRecDepth 100000 in decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨3, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨5, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨16, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨14, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨12, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨10, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨8, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨6, by omega, by decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨31, by omega, by
      set_option maxRecDepth 100000 in decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨29, by omega, by
      set_option maxRecDepth 100000 in decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨27, by omega, by
      set_option maxRecDepth 100000 in decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨25, by omega, by
      set_option maxRecDepth 100000 in decide⟩
  · exact mem_valuesThrough_iff.mpr ⟨23, by omega, by
      set_option maxRecDepth 100000 in decide⟩

/-- From target nineteen onward, a full coverage time is at least the target.
For targets at least twenty-five this is the existing revisit pigeonhole.
For nineteen through twenty-four, coverage includes value four, whose first
occurrence is the late clock 131. -/
theorem target_le_coversBelow_of_nineteen {target coverage : Nat}
    (hcov : CoversBelow target coverage) (hlarge : 19 ≤ target) :
    target ≤ coverage := by
  by_cases htwentyfive : 25 ≤ target
  · exact target_le_coversBelow hcov htwentyfive
  · have hfour : (4 : Nat) < target := by omega
    rcases mem_valuesThrough_iff.mp (hcov 4 hfour) with
      ⟨time, htime, hvalue⟩
    have hfirst : FirstAt a 4 131 := firstAt_four_131
    have hclock : 131 ≤ time := by
      by_cases hbefore : time < 131
      · exact False.elim ((hfirst.2 time hbefore) hvalue)
      · omega
    omega

/-- A discharge/return certificate whose tail start is the canonical least
valid permanent-above start. -/
structure LeastTailDischargeReturnCertificate
    (target start : Nat) (parent : PhaseSearchNode) where
  discharge : PermanentTailDischargeReturnCertificate target start parent
  tail_minimal : ∀ s, MissingStrictAboveTail target s →
    discharge.tailStart ≤ s

namespace LeastTailDischargeReturnCertificate

variable {target start : Nat} {parent : PhaseSearchNode}

/-- The canonical tail start lies below the original combined tail start. -/
theorem tailStart_le_start
    (source : LeastTailDischargeReturnCertificate target start parent) :
    source.discharge.tailStart ≤ start :=
  source.discharge.tailStart_le_start

/-- Any valid tail start bounds the canonical one, including the arbitrary
tail carried by another discharge certificate. -/
theorem tailStart_le_discharge
    (source : LeastTailDischargeReturnCertificate target start parent)
    (other : PermanentTailDischargeReturnCertificate target start parent) :
    source.discharge.tailStart ≤ other.tailStart :=
  source.tail_minimal _ other.historical_tail

/-- Reuse the canonical historical descent and return data while replacing
only the combined parent and its old crossing witness.  This keeps the least
tail, historical minimum, and downcross endpoint literally stable across
installed successors. -/
def rebase
    (source : LeastTailDischargeReturnCertificate target start parent)
    {newParent : PhaseSearchNode}
    (other : PermanentTailDischargeReturnCertificate target start newParent) :
    LeastTailDischargeReturnCertificate target start newParent := {
  discharge := {
    combinedMinimumTime := other.combinedMinimumTime
    combinedPredecessorFirstTime := other.combinedPredecessorFirstTime
    combined := other.combined
    tailStart := source.discharge.tailStart
    historicalMinimumTime := source.discharge.historicalMinimumTime
    historicalFirstTime := source.discharge.historicalFirstTime
    downTime := source.discharge.downTime
    returnTime := source.discharge.returnTime
    oldCrossingTime := other.oldCrossingTime
    tailStart_le_start := source.discharge.tailStart_le_start
    historical_tail := source.discharge.historical_tail
    historical_minimum := source.discharge.historical_minimum
    downcross := source.discharge.downcross
    endpoint_first := source.discharge.endpoint_first
    endpoint_before_tail := source.discharge.endpoint_before_tail
    return_crossing := source.discharge.return_crossing
    return_before_tail := source.discharge.return_before_tail
    old_crossing := other.old_crossing
    old_crossing_before_horizon := other.old_crossing_before_horizon
    parent_anchor_eq := other.parent_anchor_eq
  }
  tail_minimal := source.tail_minimal
}

@[simp] theorem rebase_iterationRank
    (source : LeastTailDischargeReturnCertificate target start parent)
    {newParent : PhaseSearchNode}
    (other : PermanentTailDischargeReturnCertificate target start newParent) :
    terminalDischargeIterationRank target (source.rebase other).discharge =
      terminalDischargeIterationRank target other := by
  rfl

@[simp] theorem rebase_downTime
    (source : LeastTailDischargeReturnCertificate target start parent)
    {newParent : PhaseSearchNode}
    (other : PermanentTailDischargeReturnCertificate target start newParent) :
    (source.rebase other).discharge.downTime = source.discharge.downTime := by
  rfl

/-- The canonical tail is pinned one step after any late full-coverage bound.
This is the upper-bound interface that arbitrary discharge certificates lack. -/
theorem tailStart_le_coverage_succ
    (source : LeastTailDischargeReturnCertificate target start parent)
    {bound : Nat} (hcov : CoversBelow target bound)
    (hlate : target ≤ bound) :
    source.discharge.tailStart ≤ bound + 1 :=
  least_tailStart_le_of_coverage_bound hcov source.discharge.historical_tail
    source.tail_minimal hlate

end LeastTailDischargeReturnCertificate

/-- Build the least-tail discharge while retaining a specified old crossing
witness.  This is the transport form used by canonical successor iteration. -/
theorem PermanentTailCombinedCertificate.exists_leastTailDischargeReturnCertificate_withOldCrossing
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime)
    (oldCrossingTime : Nat)
    (holdCrossing : WeakUpcrossingStep target 0 oldCrossingTime)
    (holdBefore : oldCrossingTime + 1 < parent.horizon)
    (hparentAnchor : parent.anchorParent = a oldCrossingTime) :
    ∃ source : LeastTailDischargeReturnCertificate target start parent,
      source.discharge.oldCrossingTime = oldCrossingTime := by
  have hex : ∃ s, MissingStrictAboveTail target s :=
    ⟨start, h.tail.toStrictAboveTail⟩
  rcases exists_least_missingStrictAboveTail hex with
    ⟨least, hleastTail, hleast⟩
  rcases hleastTail.exists_historicalDowncrossCertificate with
    ⟨tailStart, historicalMinimumTime, historicalFirstTime, downTime,
      htailStartLe, hhistoricalTail, hhistoricalMinimum, hdown,
      hendpointFirst, hendpointBefore, _hbudgetDrop⟩
  have hleastLe : least ≤ tailStart := hleast _ hhistoricalTail
  have htailEq : tailStart = least := by omega
  subst tailStart
  rcases exists_firstWeakUpcrossingStep_from_below h.tail.target_positive
      hdown.endpoint_below with ⟨returnTime, hreturn⟩
  have htailAbove := hhistoricalTail.strictly_above least (Nat.le_refl _)
  rcases exists_weakUpcrossingStep_between
      (Nat.le_of_lt hendpointBefore) hdown.endpoint_below
      (Nat.le_of_lt htailAbove) with
    ⟨witnessTime, hwitness, hwitnessBefore⟩
  have hreturnBefore := hreturn.endpoint_le_of_witness hwitness hwitnessBefore
  have hleastStart : least ≤ start :=
    hleast _ h.tail.toStrictAboveTail
  let discharge : PermanentTailDischargeReturnCertificate target start parent := {
    combinedMinimumTime := minimumTime
    combinedPredecessorFirstTime := predecessorFirstTime
    combined := h
    tailStart := least
    historicalMinimumTime := historicalMinimumTime
    historicalFirstTime := historicalFirstTime
    downTime := downTime
    returnTime := returnTime
    oldCrossingTime := oldCrossingTime
    tailStart_le_start := hleastStart
    historical_tail := hhistoricalTail
    historical_minimum := hhistoricalMinimum
    downcross := hdown
    endpoint_first := hendpointFirst
    endpoint_before_tail := hendpointBefore
    return_crossing := hreturn
    return_before_tail := hreturnBefore
    old_crossing := holdCrossing
    old_crossing_before_horizon := holdBefore
    parent_anchor_eq := hparentAnchor
  }
  refine ⟨{
      discharge := discharge
      tail_minimal := by
        intro s hs
        exact hleast s hs
    }, ?_⟩
  rfl

/-- Build the historical discharge at the least valid strict-above tail.
This removes the spurious upward freedom in `tailStart` without changing the
existing discharge certificate or any of its consumers. -/
theorem PermanentTailCombinedCertificate.exists_leastTailDischargeReturnCertificate
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    Nonempty (LeastTailDischargeReturnCertificate target start parent) := by
  rcases h.crossing.ready_crossing.crossing with
    ⟨oldAnchor, oldCrossingTime, quotient, remainder, hold⟩
  have holdCrossing : WeakUpcrossingStep target 0 oldCrossingTime := {
    start_le := Nat.zero_le _
    below := hold.recovery.crossing.1
    endpoint_ge := Nat.le_of_lt hold.recovery.crossing.2.1
    forced_addition := hold.recovery.forced_addition
  }
  have hparentAnchor : parent.anchorParent = a oldCrossingTime := by
    simpa using congrArg PhaseSearchNode.anchorParent hold.node_eq
  rcases h.exists_leastTailDischargeReturnCertificate_withOldCrossing
      oldCrossingTime holdCrossing hold.recovery.crossing_before_horizon
      hparentAnchor with ⟨source, _⟩
  exact ⟨source⟩

namespace LeastTailDischargeReturnCertificate

variable {target start : Nat} {parent : PhaseSearchNode}

/-- The tail start stored by every canonical discharge is exactly one past
the least coverage time.  The completed permanent tail supplies existence of
coverage; the missing-target lower bound makes the coverage time late enough
for the least-tail determination theorem. -/
theorem tailStart_eq_coverage_succ
    (source : LeastTailDischargeReturnCertificate target start parent) :
    ∃ coverage, CoversBelow target coverage ∧
      (∀ n, CoversBelow target n → coverage ≤ n) ∧
      target ≤ coverage ∧
      source.discharge.tailStart = coverage + 1 := by
  have hex : ∃ coverage, CoversBelow target coverage :=
    ⟨start, source.discharge.combined.tail.below_covered⟩
  rcases exists_least_coversBelow hex with
    ⟨coverage, hcoverage, hcoverageMinimal⟩
  have hnineteen : 19 ≤ target :=
    nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
  have htargetCoverage :=
    target_le_coversBelow_of_nineteen hcoverage hnineteen
  exact ⟨coverage, hcoverage, hcoverageMinimal,
    htargetCoverage,
    least_tailStart_eq_coverage_succ hcoverage hcoverageMinimal
      source.discharge.historical_tail source.tail_minimal htargetCoverage⟩

/-- Exact-replay compatibility wrapper for the general determination above. -/
theorem exactReplay_tailStart_eq_coverage_succ
    (source : LeastTailDischargeReturnCertificate target start parent)
    (_r : TerminalExactDischargeReplayCertificate source.discharge) :
    ∃ coverage, CoversBelow target coverage ∧
      (∀ n, CoversBelow target n → coverage ≤ n) ∧
      target ≤ coverage ∧
      source.discharge.tailStart = coverage + 1 :=
  source.tailStart_eq_coverage_succ

/-- Local normal form at the canonical tail boundary of an exact replay.
The last coverage time is a fresh below-target value, and the next step is a
numerically forced addition which starts the permanent-above tail. -/
structure BoundaryCertificate
    (source : LeastTailDischargeReturnCertificate target start parent) where
  coverage : Nat
  covers : CoversBelow target coverage
  coverage_minimal : ∀ n, CoversBelow target n → coverage ≤ n
  target_le_coverage : target ≤ coverage
  tailStart_eq : source.discharge.tailStart = coverage + 1
  predecessor_below : a coverage < target
  predecessor_first : FirstAt a (a coverage) coverage
  predecessor_le_clock : a coverage ≤ coverage
  forced_addition : ¬ CanSubtract (coverage + 1) (stateAt coverage)
  boundary_value : a (coverage + 1) = a coverage + (coverage + 1)

/-- Every canonical discharge has the fresh-addition boundary normal form. -/
theorem boundaryCertificate
    (source : LeastTailDischargeReturnCertificate target start parent) :
    Nonempty (BoundaryCertificate source) := by
  rcases source.tailStart_eq_coverage_succ with
    ⟨coverage, hcoverage, hcoverageMinimal, htargetCoverage, htail⟩
  have hcoveragePos : 0 < coverage := by
    have hlarge := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    omega
  have hfirst := least_coversBelow_firstAt hcoverage hcoverageMinimal
    hcoveragePos
  have hle : a coverage ≤ coverage := by omega
  have hforced : ¬ CanSubtract (coverage + 1) (stateAt coverage) := by
    intro hcan
    have hlarge : coverage + 1 < a coverage := hcan.1
    omega
  have hvalue := a_succ_of_not_canSubtract hforced
  exact ⟨{
    coverage := coverage
    covers := hcoverage
    coverage_minimal := hcoverageMinimal
    target_le_coverage := htargetCoverage
    tailStart_eq := htail
    predecessor_below := hfirst.1
    predecessor_first := hfirst.2
    predecessor_le_clock := hle
    forced_addition := hforced
    boundary_value := hvalue
  }⟩

/-- Exact-replay compatibility wrapper for the general boundary theorem. -/
theorem exactReplay_boundaryCertificate
    (source : LeastTailDischargeReturnCertificate target start parent)
    (_r : TerminalExactDischargeReplayCertificate source.discharge) :
    Nonempty (BoundaryCertificate source) :=
  source.boundaryCertificate

namespace BoundaryCertificate

variable {source : LeastTailDischargeReturnCertificate target start parent}

/-- The last newly covered value is positive: zero already occurred at time
zero, strictly before the positive coverage clock. -/
theorem predecessor_positive (b : BoundaryCertificate source) :
    0 < a b.coverage := by
  by_cases hzero : a b.coverage = 0
  · have hcoveragePos : 0 < b.coverage := by
      have htarget := nineteen_le_of_target_missing
        source.discharge.historical_tail.target_missing
      have htargetCoverage := b.target_le_coverage
      omega
    have hne := b.predecessor_first.2 0 hcoveragePos
    exact False.elim (hne (by rw [hzero]; rfl))
  · omega

/-- The last newly covered value is either the exceptional late low value
four at clock 131, or is itself at least nineteen. -/
theorem predecessor_four_or_nineteen (b : BoundaryCertificate source) :
    (b.coverage = 131 ∧ a b.coverage = 4) ∨
      19 ≤ a b.coverage := by
  by_cases hlarge : 19 ≤ a b.coverage
  · exact Or.inr hlarge
  · left
    have hsmall : a b.coverage < 19 := by omega
    have hseen131 := coversBelow_nineteen_131 (a b.coverage) hsmall
    rcases mem_valuesThrough_iff.mp hseen131 with
      ⟨time, htime, hvalue⟩
    have hcoverageLe : b.coverage ≤ time := by
      by_cases hearlier : time < b.coverage
      · exact False.elim
          ((b.predecessor_first.2 time hearlier) hvalue)
      · omega
    have h131Le : 131 ≤ b.coverage := by
      have hfourBelow : (4 : Nat) < target := by
        have htarget := nineteen_le_of_target_missing
          source.discharge.historical_tail.target_missing
        omega
      rcases mem_valuesThrough_iff.mp (b.covers 4 hfourBelow) with
        ⟨fourTime, hfourTime, hfourValue⟩
      have hfirst := firstAt_four_131
      have hle : 131 ≤ fourTime := by
        by_cases hearlier : fourTime < 131
        · exact False.elim ((hfirst.2 fourTime hearlier) hfourValue)
        · omega
      omega
    have hcoverageEq : b.coverage = 131 := by omega
    refine ⟨hcoverageEq, ?_⟩
    rw [hcoverageEq]
    set_option maxRecDepth 100000 in decide

/-- The transition into the last coverage value must be a legal subtraction.
A forced addition would make the fresh value at least its clock, contradicting
`a coverage < target ≤ coverage`. -/
theorem incoming_subtraction (b : BoundaryCertificate source) :
    CanSubtract b.coverage (stateAt (b.coverage - 1)) := by
  have hcoveragePos : 0 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  by_cases hcan : CanSubtract b.coverage (stateAt (b.coverage - 1))
  · exact hcan
  · have hclock : b.coverage - 1 + 1 = b.coverage := by omega
    have hcan' : ¬ CanSubtract (b.coverage - 1 + 1)
        (stateAt (b.coverage - 1)) := by
      rwa [hclock]
    have hadd := a_succ_of_not_canSubtract hcan'
    rw [hclock] at hadd
    have hbelow := b.predecessor_below
    have htargetCoverage := b.target_le_coverage
    omega

/-- Numeric form of the incoming legal subtraction. -/
theorem incoming_value (b : BoundaryCertificate source) :
    a (b.coverage - 1) = a b.coverage + b.coverage := by
  have hcoveragePos : 0 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  have hclock : b.coverage - 1 + 1 = b.coverage := by omega
  have hcan : CanSubtract (b.coverage - 1 + 1)
      (stateAt (b.coverage - 1)) := by
    rw [hclock]
    exact b.incoming_subtraction
  have hstep := a_succ_of_canSubtract hcan
  rw [hclock] at hstep
  have hpositive := hcan.1
  change b.coverage - 1 + 1 < a (b.coverage - 1) at hpositive
  omega

/-- The predecessor of the last low value is already strictly above the
missing target. -/
theorem incoming_above (b : BoundaryCertificate source) :
    target < a (b.coverage - 1) := by
  have hpositive := b.predecessor_positive
  have hvalue := b.incoming_value
  have htargetCoverage := b.target_le_coverage
  omega

/-- The exceptional low boundary at clock 131 confines the missing target to
the finite interval ending at 134. -/
theorem target_le_134_of_coverage_eq_131 (b : BoundaryCertificate source)
    (hcoverage : b.coverage = 131) : target ≤ 134 := by
  have habove := b.incoming_above
  rw [hcoverage] at habove
  have hvalue : a (131 - 1) = 135 := by
    set_option maxRecDepth 100000 in decide
  rw [hvalue] at habove
  omega

/-- Canonical one-step valley equation: legal subtraction into the last new
low value followed by the forced boundary addition raises the old high value
by exactly one. -/
theorem valley_equation (b : BoundaryCertificate source) :
    a (b.coverage + 1) = a (b.coverage - 1) + 1 := by
  rw [b.boundary_value, b.incoming_value]
  omega

/-- Coverage exhausts the missing-below budget at the boundary. -/
theorem budget_at_coverage (b : BoundaryCertificate source) :
    missingBelowCount target b.coverage = 0 :=
  missingBelowCount_eq_zero_of_belowCovered b.covers

/-- Immediately before the boundary exactly one lower value is missing. -/
theorem budget_before_coverage (b : BoundaryCertificate source) :
    missingBelowCount target (b.coverage - 1) = 1 := by
  have hcoveragePos : 0 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  have hclock : b.coverage - 1 + 1 = b.coverage := by omega
  have hnotCovered : ¬ CoversBelow target (b.coverage - 1) := by
    intro hcovered
    have hminimal := b.coverage_minimal _ hcovered
    omega
  have hpositive : 0 < missingBelowCount target (b.coverage - 1) := by
    by_cases hzero : missingBelowCount target (b.coverage - 1) = 0
    · exact False.elim
        (hnotCovered (missingBelowCount_zero_covered target hzero))
    · omega
  have hfull : coveredBelowCount target b.coverage = target :=
    coveredBelowCount_eq_of_covered target b.covers
  have hstep := coveredBelowCount_step_le (b.coverage - 1) target
  rw [hclock] at hstep
  have hpartition := coveredBelowCount_add_missingBelowCount
    (b.coverage - 1) target
  omega

/-- Exact identity of the last missing lower level. -/
theorem missing_before_iff (b : BoundaryCertificate source)
    {value : Nat} (hvalue : value < target) :
    value ∉ valuesThrough (b.coverage - 1) ↔ value = a b.coverage := by
  have hcoveragePos : 0 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  have hclock : b.coverage - 1 + 1 = b.coverage := by omega
  constructor
  · intro hmissing
    have hseen := b.covers value hvalue
    rw [← hclock, valuesThrough_succ] at hseen
    rcases List.mem_cons.mp hseen with heq | hbefore
    · rw [hclock] at heq
      exact heq
    · exact False.elim (hmissing hbefore)
  · intro heq hseen
    subst value
    exact firstAt_not_mem_valuesThrough_before b.predecessor_first
      (by omega) hseen

/-- The subtraction candidate one step into the tail is the predecessor of
the last missing low value. -/
theorem second_candidate (b : BoundaryCertificate source) :
    a (b.coverage + 1) - (b.coverage + 2) = a b.coverage - 1 := by
  rw [b.boundary_value]
  have hpositive := b.predecessor_positive
  omega

/-- The second tail step is forced: its candidate is the lower neighbour of
the last missing value and was therefore already covered before the valley. -/
theorem second_forced_addition (b : BoundaryCertificate source) :
    ¬ CanSubtract (b.coverage + 2) (stateAt (b.coverage + 1)) := by
  have hlower : a b.coverage - 1 < target := by
    have hbelow := b.predecessor_below
    omega
  have hne : a b.coverage - 1 ≠ a b.coverage := by
    have hpositive := b.predecessor_positive
    omega
  have hseenBefore : a b.coverage - 1 ∈
      valuesThrough (b.coverage - 1) := by
    by_cases hseen : a b.coverage - 1 ∈ valuesThrough (b.coverage - 1)
    · exact hseen
    · have heq := (b.missing_before_iff hlower).mp hseen
      exact False.elim (hne heq)
  have hseen : a (b.coverage + 1) - (b.coverage + 2) ∈
      valuesThrough (b.coverage + 1) := by
    rw [b.second_candidate]
    exact valuesThrough_mono (by omega) hseenBefore
  intro hcan
  exact hcan.2 hseen

/-- Closed value after the second forced addition. -/
theorem second_value (b : BoundaryCertificate source) :
    a (b.coverage + 2) = a b.coverage + 2 * b.coverage + 3 := by
  have hstep : a (b.coverage + 2) =
      a (b.coverage + 1) + (b.coverage + 2) := by
    simpa [Nat.add_assoc] using
      (a_succ_of_not_canSubtract b.second_forced_addition)
  rw [b.boundary_value] at hstep
  omega

/-- The third tail-step candidate returns exactly to the high side of the
canonical valley. -/
theorem third_candidate (b : BoundaryCertificate source) :
    a (b.coverage + 2) - (b.coverage + 3) =
      a (b.coverage - 1) := by
  rw [b.second_value, b.incoming_value]
  have hpositive := b.predecessor_positive
  omega

/-- The third tail step is forced because that high candidate occurred two
steps before the tail began. -/
theorem third_forced_addition (b : BoundaryCertificate source) :
    ¬ CanSubtract (b.coverage + 3) (stateAt (b.coverage + 2)) := by
  have hseenBefore : a (b.coverage - 1) ∈
      valuesThrough (b.coverage - 1) :=
    current_mem_valuesThrough (b.coverage - 1)
  have hseen : a (b.coverage + 2) - (b.coverage + 3) ∈
      valuesThrough (b.coverage + 2) := by
    rw [b.third_candidate]
    exact valuesThrough_mono (by omega) hseenBefore
  intro hcan
  exact hcan.2 hseen

/-- Closed value after the third forced addition. -/
theorem third_value (b : BoundaryCertificate source) :
    a (b.coverage + 3) = a b.coverage + 3 * b.coverage + 6 := by
  have hstep : a (b.coverage + 3) =
      a (b.coverage + 2) + (b.coverage + 3) := by
    simpa [Nat.add_assoc] using
      (a_succ_of_not_canSubtract b.third_forced_addition)
  rw [b.second_value] at hstep
  omega

/-- The fresh boundary value immediately performs the canonical first weak
upcrossing into the permanent tail. -/
theorem first_upcrossing (b : BoundaryCertificate source) :
    FirstWeakUpcrossingStep target b.coverage b.coverage := by
  have htailAbove : target < a (b.coverage + 1) := by
    have hstart := source.discharge.historical_tail.strictly_above
      source.discharge.tailStart (Nat.le_refl _)
    rw [b.tailStart_eq] at hstart
    exact hstart
  exact {
    crossing := {
      start_le := Nat.le_refl _
      below := b.predecessor_below
      endpoint_ge := Nat.le_of_lt htailAbove
      forced_addition := b.forced_addition
    }
    first := by
      intro earlier hearlier hcrossing
      have := hcrossing.start_le
      omega
  }

/-- The boundary crossing finishes strictly inside the shared parent
horizon, rather than merely before the arbitrary combined start. -/
theorem crossing_before_horizon (b : BoundaryCertificate source) :
    b.coverage + 1 < parent.horizon := by
  rw [← b.tailStart_eq]
  exact Nat.lt_of_le_of_lt source.discharge.tailStart_le_start
    source.discharge.combined.crossing.tail_strictly_before_horizon

/-- Hence the canonical boundary is a ready crossing in the refined domain. -/
theorem ready_crossing (b : BoundaryCertificate source) :
    ReadyCrossingSearchInvariant target
      (terminalPredecessorCrossingNode parent b.coverage) :=
  source.discharge.combined.landingReadyCrossing b.first_upcrossing
    b.crossing_before_horizon

/-- Source-preserving cursor for the canonical boundary landing. -/
theorem terminalHistoryCursor (b : BoundaryCertificate source) :
    TerminalHistoryCursor target b.coverage := by
  have hcoverage : 0 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  refine ⟨b.coverage - 1, b.coverage + 1, b.coverage + 1,
    by omega, b.incoming_above, b.valley_equation.symm,
    Nat.le_refl _, ?_⟩
  intro witness hlow
  by_cases hbefore : witness < b.coverage + 1
  · exact hbefore
  · have htail : source.discharge.tailStart ≤ witness := by
      rw [b.tailStart_eq]
      omega
    have habove := source.discharge.historical_tail.strictly_above
      witness htail
    omega

/-- Source-preserving strict chronology edge at the boundary. -/
theorem chronologyHistoryProgress (b : BoundaryCertificate source) :
    TerminalChronologyHistoryProgress target b.coverage
      (b.coverage - 1) := by
  have hcoverage : 0 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  constructor
  · unfold TerminalHistoryBudgetDrop
    rw [b.budget_at_coverage, b.budget_before_coverage]
    omega
  · have hclock : b.coverage - 1 + 1 = b.coverage := by omega
    rw [hclock]
    exact b.terminalHistoryCursor

/-- The canonical history landing mounted directly at its original combined
parent, preserving the ready crossing and chronology payload. -/
theorem refinedMountedOutcome (b : BoundaryCertificate source) :
    RefinedTerminalMountedOutcome target start parent := by
  have hcoverage : 0 < b.coverage := by
    have htarget := nineteen_le_of_target_missing
      source.discharge.historical_tail.target_missing
    have htargetCoverage := b.target_le_coverage
    omega
  have hcrossStart : b.coverage + 1 ≤ start := by
    rw [← b.tailStart_eq]
    exact source.discharge.tailStart_le_start
  exact .landing_crossing b.coverage (b.coverage - 1)
    b.chronologyHistoryProgress (a b.coverage) b.coverage b.coverage
    b.predecessor_below (by omega) b.predecessor_first b.first_upcrossing
    hcrossStart b.crossing_before_horizon b.ready_crossing
    (Nat.le_refl _) b.terminalHistoryCursor

/-- The boundary upcrossing viewed from the global origin, as required by a
discharge's stored old-crossing field. -/
theorem zeroBased_crossing (b : BoundaryCertificate source) :
    WeakUpcrossingStep target 0 b.coverage := {
  start_le := Nat.zero_le _
  below := b.first_upcrossing.crossing.below
  endpoint_ge := b.first_upcrossing.crossing.endpoint_ge
  forced_addition := b.first_upcrossing.crossing.forced_addition
}

/-- Install the boundary crossing while reusing all canonical historical
data literally. -/
def installedSource (b : BoundaryCertificate source) :
    LeastTailDischargeReturnCertificate target start
      (terminalPredecessorCrossingNode parent b.coverage) := {
  discharge := {
    combinedMinimumTime := source.discharge.combinedMinimumTime
    combinedPredecessorFirstTime :=
      source.discharge.combinedPredecessorFirstTime
    combined := source.discharge.combined.installReadyCrossing b.ready_crossing
    tailStart := source.discharge.tailStart
    historicalMinimumTime := source.discharge.historicalMinimumTime
    historicalFirstTime := source.discharge.historicalFirstTime
    downTime := source.discharge.downTime
    returnTime := source.discharge.returnTime
    oldCrossingTime := b.coverage
    tailStart_le_start := source.discharge.tailStart_le_start
    historical_tail := source.discharge.historical_tail
    historical_minimum := source.discharge.historical_minimum
    downcross := source.discharge.downcross
    endpoint_first := source.discharge.endpoint_first
    endpoint_before_tail := source.discharge.endpoint_before_tail
    return_crossing := source.discharge.return_crossing
    return_before_tail := source.discharge.return_before_tail
    old_crossing := b.zeroBased_crossing
    old_crossing_before_horizon := by
      simpa [terminalPredecessorCrossingNode] using b.crossing_before_horizon
    parent_anchor_eq := rfl
  }
  tail_minimal := source.tail_minimal
}

@[simp] theorem installedSource_downTime (b : BoundaryCertificate source) :
    b.installedSource.discharge.downTime = source.discharge.downTime := by
  rfl

end BoundaryCertificate

/-- Progress classification exposed specifically by the fresh boundary of a
canonical exact replay.  Anchor drop gives the certificate-tied semantic
edge.  Anchor growth installs another *canonical* discharge and strictly
decreases the existing discharge iteration rank.  Equality pins the old
crossing time to the coverage boundary exactly. -/
inductive BoundaryRankOutcome
    (source : LeastTailDischargeReturnCertificate target start parent)
    (boundary : BoundaryCertificate source) : Prop
  | semantic
      (edge : RefinedSemanticEdge target start) :
      BoundaryRankOutcome source boundary
  | iteration_progress
      (child : LeastTailDischargeReturnCertificate target start
        (terminalPredecessorCrossingNode parent boundary.coverage))
      (progress : TerminalDischargeIterationProgress target child.discharge
        source.discharge) :
      BoundaryRankOutcome source boundary
  | fixed_point
      (anchor_eq : a boundary.coverage = parent.anchorParent)
      (oldCrossingTime_eq : source.discharge.oldCrossingTime =
        boundary.coverage)
      (node_eq : terminalPredecessorCrossingNode parent boundary.coverage =
        parent) :
      BoundaryRankOutcome source boundary

/-- Complete rank analysis of the canonical exact-replay boundary. -/
theorem BoundaryCertificate.rankOutcome
    {source : LeastTailDischargeReturnCertificate target start parent}
    (boundary : BoundaryCertificate source) :
    BoundaryRankOutcome source boundary := by
  let ready := boundary.ready_crossing
  by_cases hdrop : a boundary.coverage < parent.anchorParent
  · cases source.discharge.combined.mountedLandingRankOutcome
        boundary.coverage with
    | phase_exit progress =>
        exact .semantic (.mounted_crossing parent
          source.discharge.combinedMinimumTime
          source.discharge.combinedPredecessorFirstTime boundary.coverage
          source.discharge.combined ready progress)
    | anchor_nondecreasing hanchor =>
        exact False.elim (by omega)
  · have hnondecreasing : parent.anchorParent ≤ a boundary.coverage :=
      Nat.le_of_not_gt hdrop
    by_cases hgrowth : parent.anchorParent < a boundary.coverage
    · let child := boundary.installedSource
      have hprogress : TerminalDischargeIterationProgress target
          child.discharge source.discharge :=
        terminalDischargeIterationProgress_of_anchorGrowth rfl
          boundary.predecessor_below hgrowth
      exact .iteration_progress child hprogress
    · have hsame : a boundary.coverage = parent.anchorParent := by omega
      rcases source.discharge.combined.crossing.ready_crossing.crossing with
        ⟨oldAnchor, oldTime, quotient, remainder, hold⟩
      have holdAnchor : parent.anchorParent = a oldTime := by
        simpa using congrArg PhaseSearchNode.anchorParent hold.node_eq
      have holdBefore : source.discharge.oldCrossingTime <
          source.discharge.tailStart := by
        by_cases hbefore : source.discharge.oldCrossingTime <
            source.discharge.tailStart
        · exact hbefore
        · have habove := source.discharge.historical_tail.strictly_above
            source.discharge.oldCrossingTime (by omega)
          have hbelow := source.discharge.old_crossing.below
          omega
      have holdLe : source.discharge.oldCrossingTime ≤
          boundary.coverage := by
        rw [boundary.tailStart_eq] at holdBefore
        omega
      have hcoverageLe : boundary.coverage ≤
          source.discharge.oldCrossingTime := by
        by_cases hearlier : source.discharge.oldCrossingTime <
            boundary.coverage
        · have hne := boundary.predecessor_first.2
            source.discharge.oldCrossingTime hearlier
          exfalso
          apply hne
          exact source.discharge.parent_anchor_eq.symm.trans hsame.symm
        · omega
      have htime : source.discharge.oldCrossingTime = boundary.coverage := by
        omega
      have hnode : terminalPredecessorCrossingNode parent
          boundary.coverage = parent := by
        show (⟨parent.horizon, a boundary.coverage, .normal,
          a boundary.coverage⟩ : PhaseSearchNode) = parent
        rw [hsame, holdAnchor]
        exact hold.node_eq.symm
      exact .fixed_point hsame htime hnode

/-- The source-preserving mounted landing and its canonical rank
classification are available together on the same boundary certificate. -/
theorem BoundaryCertificate.refinedMountedRankOutcome
    {source : LeastTailDischargeReturnCertificate target start parent}
    (boundary : BoundaryCertificate source) :
    RefinedTerminalMountedOutcome target start parent ∧
      BoundaryRankOutcome source boundary :=
  ⟨boundary.refinedMountedOutcome, boundary.rankOutcome⟩

/-- The apparent equality branch of the boundary rank analysis contradicts
the exact replay itself.  Replay pinning says its crossing value strictly
exceeds the next clock, whereas the least-coverage boundary value is at most
its own clock.  Thus a canonical exact replay always produces real progress. -/
inductive ExactReplayBoundaryProgressOutcome
    (source : LeastTailDischargeReturnCertificate target start parent) : Prop
  | semantic
      (edge : RefinedSemanticEdge target start) :
      ExactReplayBoundaryProgressOutcome source
  | iteration_progress
      (childParent : PhaseSearchNode)
      (child : LeastTailDischargeReturnCertificate target start childParent)
      (progress : TerminalDischargeIterationProgress target child.discharge
        source.discharge) :
      ExactReplayBoundaryProgressOutcome source

theorem exactReplay_boundaryProgressOutcome
    (source : LeastTailDischargeReturnCertificate target start parent)
    (r : TerminalExactDischargeReplayCertificate source.discharge) :
    ExactReplayBoundaryProgressOutcome source := by
  rcases source.exactReplay_boundaryCertificate r with ⟨boundary⟩
  cases boundary.rankOutcome with
  | semantic edge =>
      exact .semantic edge
  | iteration_progress child progress =>
      exact .iteration_progress _ child progress
  | fixed_point anchor_eq oldCrossingTime_eq node_eq =>
      have htime : r.crossingTime = boundary.coverage := by
        rw [r.time_eq, oldCrossingTime_eq]
      have hclock := r.clock_lt_crossingValue
      rw [htime] at hclock
      have hle := boundary.predecessor_le_clock
      exact False.elim (by omega)

/-! ## Replay-free canonical discharge iteration -/

/-- Once every successor discharge is rebuilt at the least tail start, the
exact-replay constructor disappears.  The iteration can finish only at an
actual occurrence, an established chronology edge, or a certificate-tied
refined semantic edge. -/
inductive ClosedOutcome (target start : Nat) : Prop
  | target_occurs
      (witness : Nat) (value_eq : a witness = target) :
      ClosedOutcome target start
  | history_progress
      (childTime parentTime : Nat)
      (progress : TerminalChronologyHistoryProgress target childTime
        parentTime) :
      ClosedOutcome target start
  | refined_semantic
      (edge : RefinedSemanticEdge target start) :
      ClosedOutcome target start

/-- Well-founded closure of canonical discharge iteration.  Ordinary
installed successors are rebuilt at the least tail while retaining their old
crossing cursor.  Exact replays are converted by the fresh boundary theorem
above into either a semantic edge or another strict canonical successor. -/
theorem closedOutcome
    (source : LeastTailDischargeReturnCertificate target start parent) :
    ClosedOutcome target start := by
  have main : ∀ rank : Nat × (Nat × Nat),
      ∀ (parentNode : PhaseSearchNode)
        (node : LeastTailDischargeReturnCertificate target start parentNode),
        terminalDischargeIterationRank target node.discharge = rank →
        ClosedOutcome target start := by
    intro rank
    induction natTripleLex_wellFounded.apply rank with
    | intro rank _ ih =>
        intro parentNode node hrank
        cases node.discharge.refinedTerminalIterationOutcome with
        | target_occurs witness value_eq =>
            exact .target_occurs witness value_eq
        | history_progress childTime parentTime progress =>
            exact .history_progress childTime parentTime progress
        | refined_semantic step =>
            exact .refined_semantic
              (.discharge_step parentNode node.discharge step)
        | iteration_progress crossingTime next next_old_eq iteration =>
            let child := node.rebase next
            have hrelation : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
                (terminalDischargeIterationRank target child.discharge)
                rank := by
              rw [rebase_iterationRank, ← hrank]
              exact iteration
            exact ih (terminalDischargeIterationRank target child.discharge)
              hrelation _ child rfl
        | exact_replay replay =>
            cases node.exactReplay_boundaryProgressOutcome replay with
            | semantic edge =>
                exact .refined_semantic edge
            | iteration_progress childParent child progress =>
                have hrelation : Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)
                    (terminalDischargeIterationRank target child.discharge)
                    rank := by
                  rw [← hrank]
                  exact progress
                exact ih
                  (terminalDischargeIterationRank target child.discharge)
                  hrelation childParent child rfl
  exact main (terminalDischargeIterationRank target source.discharge) parent
    source rfl

end LeastTailDischargeReturnCertificate

/-- The least-missing-target summit can choose its discharge at the canonical
least tail start.  This is the replacement entry point for downstream summit
arguments that need a genuine tail-start upper bound. -/
theorem LeastMissingTarget.exists_leastTailDischargeReturnCertificate
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ (start : Nat) (parent : PhaseSearchNode),
      Nonempty (LeastTailDischargeReturnCertificate target start parent) := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨parent, minimumTime, predecessorFirstTime, hcombined⟩
  rcases hcombined.exists_leastTailDischargeReturnCertificate with ⟨source⟩
  exact ⟨start, parent, ⟨source⟩⟩

/-- The refined discharge outcome is available from the canonical summit
certificate, so choosing the least tail loses none of the semantic analysis. -/
theorem LeastMissingTarget.exists_leastTailRefinedSuccessorOutcome
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ (start : Nat) (parent : PhaseSearchNode)
      (source : LeastTailDischargeReturnCertificate target start parent),
      PermanentTailRefinedSuccessorOutcome source.discharge := by
  rcases h.exists_leastTailDischargeReturnCertificate with
    ⟨start, parent, ⟨source⟩⟩
  exact ⟨start, parent, source, source.discharge.refinedSuccessorOutcome⟩

/-- Combined-certificate interface after least-tail canonicalisation.  This
is the reusable form of the replay elimination: no fixed-point or numeric
floor branch remains. -/
theorem PermanentTailCombinedCertificate.historyProgress_or_leastTailRefinedSemanticEdge
    {target start : Nat} {parent : PhaseSearchNode}
    {minimumTime predecessorFirstTime : Nat}
    (h : PermanentTailCombinedCertificate target start parent minimumTime
      predecessorFirstTime) :
    (∃ childTime parentTime,
      TerminalChronologyHistoryProgress target childTime parentTime) ∨
      RefinedSemanticEdge target start := by
  rcases h.exists_leastTailDischargeReturnCertificate with ⟨source⟩
  cases source.closedOutcome with
  | target_occurs witness value_eq =>
      exact False.elim (h.tail.target_missing ⟨witness, value_eq⟩)
  | history_progress childTime parentTime progress =>
      exact Or.inl ⟨childTime, parentTime, progress⟩
  | refined_semantic edge =>
      exact Or.inr edge

/-- Replay-free refined summit.  The floored fixed-point branch of the old
summit disappears after canonicalising every discharge at the least tail
start.  A least missing target now yields only one of the two genuine global
recursion edges: chronology history progress or a certificate-tied refined
semantic edge. -/
theorem LeastMissingTarget.historyProgress_or_leastTailRefinedSemanticEdge
    {target : Nat} (h : LeastMissingTarget target) :
    (∃ childTime parentTime,
      TerminalChronologyHistoryProgress target childTime parentTime) ∨
    (∃ start : Nat, MissingPermanentAboveTail target start ∧
      RefinedSemanticEdge target start) := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨parent, minimumTime, predecessorFirstTime, hcombined⟩
  rcases hcombined.historyProgress_or_leastTailRefinedSemanticEdge with
    hhistory | hedge
  · exact Or.inl hhistory
  · exact Or.inr ⟨start, htail, hedge⟩

/-! ## Source-free boundary theorem -/

/-- Pure orbit-level normal form forced by a least missing target.  The last
coverage event is a fresh low value in a one-step valley, and the orbit stays
strictly above the target immediately afterward. -/
structure LeastMissingCoverageValleyCertificate (target : Nat) where
  coverage : Nat
  target_missing : ¬ ∃ time, a time = target
  covers : CoversBelow target coverage
  coverage_minimal : ∀ n, CoversBelow target n → coverage ≤ n
  target_le_coverage : target ≤ coverage
  low_first : a coverage < target ∧ FirstAt a (a coverage) coverage
  low_shape : (coverage = 131 ∧ a coverage = 4) ∨ 19 ≤ a coverage
  exception_target_bound : coverage = 131 → target ≤ 134
  incoming_subtraction : CanSubtract coverage (stateAt (coverage - 1))
  incoming_above : target < a (coverage - 1)
  outgoing_forced : ¬ CanSubtract (coverage + 1) (stateAt coverage)
  valley_equation : a (coverage + 1) = a (coverage - 1) + 1
  second_forced : ¬ CanSubtract (coverage + 2) (stateAt (coverage + 1))
  second_value : a (coverage + 2) = a coverage + 2 * coverage + 3
  third_forced : ¬ CanSubtract (coverage + 3) (stateAt (coverage + 2))
  third_value : a (coverage + 3) = a coverage + 3 * coverage + 6
  budget_before : missingBelowCount target (coverage - 1) = 1
  last_missing : ∀ value, value < target →
    (value ∉ valuesThrough (coverage - 1) ↔ value = a coverage)
  permanent_above : ∀ time, coverage + 1 ≤ time → target < a time

namespace LeastMissingCoverageValleyCertificate

/-- The canonical valley itself supplies the cursor payload required by the
strong chronology relation: its incoming high is the numeric predecessor of
the first permanent-tail value. -/
theorem terminalHistoryCursor {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    TerminalHistoryCursor target h.coverage := by
  have hcoverage : 0 < h.coverage := by
    have htarget := nineteen_le_of_target_missing h.target_missing
    have htargetCoverage := h.target_le_coverage
    omega
  refine ⟨h.coverage - 1, h.coverage + 1, h.coverage + 1,
    by omega, h.incoming_above, ?_, Nat.le_refl _, ?_⟩
  · exact h.valley_equation.symm
  · intro witness hlow
    by_cases hbefore : witness < h.coverage + 1
    · exact hbefore
    · have habove := h.permanent_above witness (by omega)
      omega

/-- The final coverage event is an unconditional strict edge in the full
well-founded chronology relation: the missing budget drops from one to zero,
and the canonical valley supplies the required history cursor. -/
theorem chronologyHistoryProgress {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    TerminalChronologyHistoryProgress target h.coverage
      (h.coverage - 1) := by
  have hcoverage : 0 < h.coverage := by
    have htarget := nineteen_le_of_target_missing h.target_missing
    have htargetCoverage := h.target_le_coverage
    omega
  constructor
  · unfold TerminalHistoryBudgetDrop
    have hzero : missingBelowCount target h.coverage = 0 :=
      missingBelowCount_eq_zero_of_belowCovered h.covers
    rw [hzero, h.budget_before]
    omega
  · have hclock : h.coverage - 1 + 1 = h.coverage := by omega
    rw [hclock]
    exact h.terminalHistoryCursor

/-- The canonical chronology edge lands at history rank zero.  Consequently
it cannot be followed by another edge of the same relation: well-foundedness
certifies termination here, but does not turn the terminal state into a
contradiction. -/
theorem no_historyBudgetDrop_from_coverage {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    ¬ ∃ childTime,
      TerminalHistoryBudgetDrop target childTime h.coverage := by
  rintro ⟨childTime, hdrop⟩
  unfold TerminalHistoryBudgetDrop at hdrop
  have hzero : missingBelowCount target h.coverage = 0 :=
    missingBelowCount_eq_zero_of_belowCovered h.covers
  rw [hzero] at hdrop
  omega

/-- Strong chronology progress has the same terminal obstruction, since its
first component is the history-budget drop above. -/
theorem no_chronologyHistoryProgress_from_coverage {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    ¬ ∃ childTime,
      TerminalChronologyHistoryProgress target childTime h.coverage := by
  rintro ⟨childTime, progress⟩
  exact h.no_historyBudgetDrop_from_coverage ⟨childTime, progress.1⟩

/-- The boundary low crosses immediately into the permanent-above tail, so
this is the canonical first weak upcrossing from that fresh landing. -/
theorem first_upcrossing {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    FirstWeakUpcrossingStep target h.coverage h.coverage := by
  have habove := h.permanent_above (h.coverage + 1) (Nat.le_refl _)
  exact {
    crossing := {
      start_le := Nat.le_refl _
      below := h.low_first.1
      endpoint_ge := Nat.le_of_lt habove
      forced_addition := h.outgoing_forced
    }
    first := by
      intro earlier hearlier hcrossing
      have hstart := hcrossing.start_le
      omega
  }

/-- Fully anchored reading of the canonical history edge.  The abstract
budget drop is accompanied by its exact fresh landing, immediate first
upcrossing, and transported cursor. -/
theorem anchoredOutcome {target start : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    PermanentTailTerminalAnchoredOutcome target start := by
  have hcoverage : 0 < h.coverage := by
    have htarget := nineteen_le_of_target_missing h.target_missing
    have htargetCoverage := h.target_le_coverage
    omega
  exact .fresh_landing h.coverage (h.coverage - 1)
    h.chronologyHistoryProgress (a h.coverage) h.coverage h.coverage
    h.low_first.1 (by omega) (Nat.le_refl _) h.low_first.2
    h.first_upcrossing h.terminalHistoryCursor

/-- The same canonical landing inhabits the certificate-preserving refined
anchored interface directly. -/
theorem refinedAnchoredOutcome {target start : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    RefinedTerminalAnchoredOutcome target start := by
  have hcoverage : 0 < h.coverage := by
    have htarget := nineteen_le_of_target_missing h.target_missing
    have htargetCoverage := h.target_le_coverage
    omega
  exact .fresh_landing h.coverage (h.coverage - 1)
    h.chronologyHistoryProgress (a h.coverage) h.coverage h.coverage
    h.low_first.1 (by omega) (Nat.le_refl _) h.low_first.2
    h.first_upcrossing h.terminalHistoryCursor

end LeastMissingCoverageValleyCertificate

/-- Every hypothetical least missing target has the canonical coverage
valley normal form. -/
theorem LeastMissingTarget.exists_coverageValleyCertificate
    {target : Nat} (h : LeastMissingTarget target) :
    Nonempty (LeastMissingCoverageValleyCertificate target) := by
  rcases h.exists_missingPermanentAboveTail with ⟨start, htail⟩
  rcases htail.exists_combinedCertificate with
    ⟨parent, minimumTime, predecessorFirstTime, hcombined⟩
  rcases hcombined.exists_leastTailDischargeReturnCertificate with ⟨source⟩
  rcases source.boundaryCertificate with ⟨boundary⟩
  exact ⟨{
    coverage := boundary.coverage
    target_missing := h.target_missing
    covers := boundary.covers
    coverage_minimal := boundary.coverage_minimal
    target_le_coverage := boundary.target_le_coverage
    low_first := ⟨boundary.predecessor_below,
      boundary.predecessor_first⟩
    low_shape := boundary.predecessor_four_or_nineteen
    exception_target_bound := boundary.target_le_134_of_coverage_eq_131
    incoming_subtraction := boundary.incoming_subtraction
    incoming_above := boundary.incoming_above
    outgoing_forced := boundary.forced_addition
    valley_equation := boundary.valley_equation
    second_forced := boundary.second_forced_addition
    second_value := boundary.second_value
    third_forced := boundary.third_forced_addition
    third_value := boundary.third_value
    budget_before := boundary.budget_before_coverage
    last_missing := fun value hvalue => boundary.missing_before_iff hvalue
    permanent_above := by
      intro time htime
      have htailTime : source.discharge.tailStart ≤ time := by
        rw [boundary.tailStart_eq]
        exact htime
      exact source.discharge.historical_tail.strictly_above time htailTime
  }⟩

/-- A coverage-valley certificate is not a weaker substitute for a virtual
counterexample: its target-missing field and finite coverage already recover
the complete least-missing-target hypothesis. -/
theorem LeastMissingCoverageValleyCertificate.toLeastMissingTarget
    {target : Nat} (h : LeastMissingCoverageValleyCertificate target) :
    LeastMissingTarget target := by
  refine ⟨h.target_missing, ?_⟩
  intro value hvalue
  rcases mem_valuesThrough_iff.mp (h.covers value hvalue) with
    ⟨time, _htime, value_eq⟩
  exact ⟨time, value_eq⟩

/-- Strategy-gate form: constructing the canonical valley is exactly
equivalent to assuming a least missing target.  Any final proof must use its
additional orbit equations, not merely the existence of the wrapper. -/
theorem leastMissingTarget_iff_nonempty_coverageValleyCertificate
    {target : Nat} :
    LeastMissingTarget target ↔
      Nonempty (LeastMissingCoverageValleyCertificate target) := by
  constructor
  · exact LeastMissingTarget.exists_coverageValleyCertificate
  · rintro ⟨certificate⟩
    exact certificate.toLeastMissingTarget

/-- Every hypothetical least missing target therefore exposes a concrete
strict edge in the already well-founded chronology relation at its canonical
last-coverage boundary. -/
theorem LeastMissingTarget.exists_coverageValleyHistoryProgress
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      TerminalChronologyHistoryProgress target certificate.coverage
        (certificate.coverage - 1) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate, certificate.chronologyHistoryProgress⟩

/-- Summit-facing form: the history side of the former history/semantic
dichotomy is always inhabited at the canonical coverage boundary. -/
theorem LeastMissingTarget.exists_terminalChronologyHistoryProgress
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ childTime parentTime,
      TerminalChronologyHistoryProgress target childTime parentTime := by
  rcases h.exists_coverageValleyHistoryProgress with
    ⟨certificate, progress⟩
  exact ⟨certificate.coverage, certificate.coverage - 1, progress⟩

/-- The canonical edge is already in the anchored outcome language consumed
by the outer landing machinery. -/
theorem LeastMissingTarget.canonicalCoverageAnchoredOutcome
    {target : Nat} (h : LeastMissingTarget target) (start : Nat) :
    PermanentTailTerminalAnchoredOutcome target start := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact certificate.anchoredOutcome

/-- Refined anchored summit at the canonical coverage landing. -/
theorem LeastMissingTarget.canonicalCoverageRefinedAnchoredOutcome
    {target : Nat} (h : LeastMissingTarget target) (start : Nat) :
    RefinedTerminalAnchoredOutcome target start := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact certificate.refinedAnchoredOutcome

/-- Source-preserving summit: the canonical coverage landing is mounted at
the original combined parent and is ready for the existing mounted-iteration
machinery. -/
theorem LeastMissingTarget.exists_leastTailBoundaryRefinedMountedOutcome
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ (start : Nat) (parent : PhaseSearchNode)
      (source : LeastTailDischargeReturnCertificate target start parent)
      (boundary : source.BoundaryCertificate),
      RefinedTerminalMountedOutcome target start parent ∧
        LeastTailDischargeReturnCertificate.BoundaryRankOutcome
          source boundary ∧
        source.discharge.tailStart = boundary.coverage + 1 := by
  rcases h.exists_leastTailDischargeReturnCertificate with
    ⟨start, parent, ⟨source⟩⟩
  rcases source.boundaryCertificate with ⟨boundary⟩
  exact ⟨start, parent, source, boundary,
    boundary.refinedMountedOutcome, boundary.rankOutcome,
    boundary.tailStart_eq⟩

end

end Recaman
