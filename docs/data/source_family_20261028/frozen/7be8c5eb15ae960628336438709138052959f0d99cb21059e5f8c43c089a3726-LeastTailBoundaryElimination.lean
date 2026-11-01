import Recaman.DeepNineteenTraceCertificate
import Recaman.DeepSixtyoneTraceCertificate
import Recaman.DeepSixtyoneMexCertificate
import Recaman.DeepSeventysixFromSixtyone
import Recaman.LeastTailBackwardChain

namespace Recaman

noncomputable section

/-!
# Eliminating the exceptional least-tail boundary

The canonical least-tail boundary has one small exceptional shape:
`coverage = 131` and `a coverage = 4`.  The authenticated deep trace closes
exactly the finite gap needed to rule it out.  It proves the late occurrence
of nineteen; values twenty through forty-six already occur in the small
kernel prefix.  Hence every globally missing target is at least forty-seven.

If the exceptional boundary existed, its permanent-above tail would start at
132.  But the actual orbit returns to forty-seven at clock 222, forcing the
missing target below forty-seven.  The two bounds contradict each other.
-/

/-- Every globally missing target is at least forty-seven.  The only value in
the range `19 ... 46` whose first occurrence is outside the small kernel
prefix is nineteen, supplied by the authenticated 99,734-step trace. -/
theorem fortyseven_le_of_target_missing {target : Nat}
    (hmissing : ¬ ∃ time, a time = target) : 47 ≤ target := by
  have hnineteen : 19 ≤ target := nineteen_le_of_target_missing hmissing
  by_cases hlarge : 47 ≤ target
  · exact hlarge
  · have hcases : target = 19 ∨ target = 20 ∨ target = 21 ∨
        target = 22 ∨ target = 23 ∨ target = 24 ∨ target = 25 ∨
        target = 26 ∨ target = 27 ∨ target = 28 ∨ target = 29 ∨
        target = 30 ∨ target = 31 ∨ target = 32 ∨ target = 33 ∨
        target = 34 ∨ target = 35 ∨ target = 36 ∨ target = 37 ∨
        target = 38 ∨ target = 39 ∨ target = 40 ∨ target = 41 ∨
        target = 42 ∨ target = 43 ∨ target = 44 ∨ target = 45 ∨
        target = 46 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · exact False.elim (hmissing
        ⟨99734, GeneratedBalancedTrace99734.generated_value⟩)
    · exact False.elim (hmissing ⟨7, by decide⟩)
    · exact False.elim (hmissing ⟨9, by decide⟩)
    · exact False.elim (hmissing ⟨11, by decide⟩)
    · exact False.elim (hmissing ⟨13, by decide⟩)
    · exact False.elim (hmissing ⟨15, by decide⟩)
    · exact False.elim (hmissing ⟨17, by decide⟩)
    · exact False.elim (hmissing ⟨64, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨62, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨60, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨58, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨56, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨54, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨52, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨50, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨48, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨46, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨44, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨42, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨40, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨38, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨111, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨22, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨20, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨18, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨28, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨30, by
        set_option maxRecDepth 100000 in decide⟩)
    · exact False.elim (hmissing ⟨32, by
        set_option maxRecDepth 100000 in decide⟩)

/-- The short interval after forty-seven is kept as data so the kernel can
check the whole finite range once, instead of repeating a case split in every
consumer. -/
def twentyThroughSixty : List Nat :=
  (List.range 41).map fun offset => offset + 20

theorem twentyThroughSixty_seen_222 :
    twentyThroughSixty.all
      (fun value => decide (value ∈ valuesThrough 222)) = true := by
  set_option maxRecDepth 100000 in decide

/-- Every value from twenty through sixty has occurred by clock 222. -/
theorem mem_valuesThrough_222_of_twenty_le_of_lt_sixtyone
    {value : Nat} (hlow : 20 ≤ value) (hhigh : value < 61) :
    value ∈ valuesThrough 222 := by
  have hmem : value ∈ twentyThroughSixty := by
    apply List.mem_map.mpr
    refine ⟨value - 20, List.mem_range.mpr (by omega), ?_⟩
    omega
  have hchecked :=
    (List.all_eq_true.mp twentyThroughSixty_seen_222) value hmem
  simpa only [decide_eq_true_eq] using hchecked

/-- The deep nineteen witness plus the clock-222 finite interval raises the
unconditional lower bound for a missing target to sixty-one. -/
theorem sixtyone_le_of_target_missing {target : Nat}
    (hmissing : ¬ ∃ time, a time = target) : 61 ≤ target := by
  have hfortyseven := fortyseven_le_of_target_missing hmissing
  by_cases hlarge : 61 ≤ target
  · exact hlarge
  · have hmem := mem_valuesThrough_222_of_twenty_le_of_lt_sixtyone
        (value := target) (by omega) (by omega)
    rcases mem_valuesThrough_iff.mp hmem with ⟨time, _htime, hvalue⟩
    exact False.elim (hmissing ⟨time, hvalue⟩)

/-- The authenticated clock-181653 endpoint removes sixty-one itself. -/
theorem sixtytwo_le_of_target_missing {target : Nat}
    (hmissing : ¬ ∃ time, a time = target) : 62 ≤ target := by
  have hsixtyone := sixtyone_le_of_target_missing hmissing
  by_cases heq : target = 61
  · subst target
    exact False.elim (hmissing
      ⟨181653, GeneratedBalancedTrace181653.generated_value⟩)
  · omega

/-- The ordinary finite prefix covers every value strictly between the two
deep delayed values 61 and 76. -/
def sixtyTwoThroughSeventyFive : List Nat :=
  (List.range 14).map fun offset => offset + 62

theorem sixtyTwoThroughSeventyFive_seen_99 :
    sixtyTwoThroughSeventyFive.all
      (fun value => decide (value ∈ valuesThrough 99)) = true := by
  set_option maxRecDepth 100000 in decide

theorem mem_valuesThrough_99_of_sixtytwo_le_of_lt_seventysix
    {value : Nat} (hlow : 62 ≤ value) (hhigh : value < 76) :
    value ∈ valuesThrough 99 := by
  have hmem : value ∈ sixtyTwoThroughSeventyFive := by
    apply List.mem_map.mpr
    refine ⟨value - 62, List.mem_range.mpr (by omega), ?_⟩
    omega
  have hchecked :=
    (List.all_eq_true.mp sixtyTwoThroughSeventyFive_seen_99) value hmem
  simpa only [decide_eq_true_eq] using hchecked

/-- All values below the next delayed value 76 have now been covered. -/
theorem seventysix_le_of_target_missing {target : Nat}
    (hmissing : ¬ ∃ time, a time = target) : 76 ≤ target := by
  have hsixtytwo := sixtytwo_le_of_target_missing hmissing
  by_cases hlarge : 76 ≤ target
  · exact hlarge
  · have hmem :=
        mem_valuesThrough_99_of_sixtytwo_le_of_lt_seventysix
          (value := target) hsixtytwo (by omega)
    rcases mem_valuesThrough_iff.mp hmem with ⟨time, _htime, hvalue⟩
    exact False.elim (hmissing ⟨time, hvalue⟩)

/-- The value 76 is recovered from the suffix of the already-authenticated
61 trace, raising the unconditional missing-target lower bound again. -/
theorem seventyseven_le_of_target_missing {target : Nat}
    (hmissing : ¬ ∃ time, a time = target) : 77 ≤ target := by
  have hseventysix := seventysix_le_of_target_missing hmissing
  by_cases heq : target = 76
  · subst target
    exact False.elim (hmissing
      ⟨181643,
        GeneratedBalancedTrace181653.generated_value_seventysix⟩)
  · omega

/-- The authenticated endpoint bitset is stronger than the individual deep
values: it proves that every value below 879 has occurred by clock 181653. -/
theorem eightHundredSeventyNine_le_of_target_missing {target : Nat}
    (hmissing : ¬ ∃ time, a time = target) : 879 ≤ target := by
  by_cases hlarge : 879 ≤ target
  · exact hlarge
  · have hmem :=
      GeneratedBalancedTrace181653.generated_mex879.1 target (by omega)
    rcases mem_valuesThrough_iff.mp hmem with ⟨time, _htime, hvalue⟩
    exact False.elim (hmissing ⟨time, hvalue⟩)

namespace LeastTailDischargeReturnCertificate.BoundaryCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : LeastTailDischargeReturnCertificate target start parent}

/-- The `coverage = 131, low = 4` branch is incompatible with the late
nineteen certificate and the actual return to forty-seven at clock 222. -/
theorem coverage_ne_131 (b : BoundaryCertificate source) :
    b.coverage ≠ 131 := by
  intro hcoverage
  have htarget : 47 ≤ target :=
    fortyseven_le_of_target_missing
      source.discharge.combined.tail.target_missing
  have htailStart : source.discharge.tailStart ≤ 222 := by
    rw [b.tailStart_eq, hcoverage]
    omega
  have habove := source.discharge.historical_tail.strictly_above 222
    htailStart
  have hvalue : a 222 = 47 := by
    set_option maxRecDepth 100000 in decide
  omega

/-- After eliminating the exceptional clock, the last newly covered value is
itself at least nineteen. -/
theorem predecessor_nineteen (b : BoundaryCertificate source) :
    19 ≤ a b.coverage := by
  rcases b.predecessor_four_or_nineteen with hexception | hlarge
  · exact False.elim (b.coverage_ne_131 hexception.1)
  · exact hlarge

/-- Below sixty-one there is now exactly one possible last-coverage event:
the authenticated late nineteen at clock 99,734. -/
theorem predecessor_nineteen_at_99734_or_sixtyone
    (b : BoundaryCertificate source) :
    (b.coverage = 99734 ∧ a b.coverage = 19) ∨
      61 ≤ a b.coverage := by
  by_cases hlarge : 61 ≤ a b.coverage
  · exact Or.inr hlarge
  · have hlow : 19 ≤ a b.coverage := b.predecessor_nineteen
    by_cases hnineteen : a b.coverage = 19
    · have hcoverageLe : b.coverage ≤ 99734 := by
        by_cases hearlier : 99734 < b.coverage
        · exact False.elim
            (b.predecessor_first.2 99734 hearlier
              (GeneratedBalancedTrace99734.generated_value.trans
                hnineteen.symm))
        · omega
      have hcoverageGe : 99734 ≤ b.coverage := by
        by_cases hearlier : b.coverage < 99734
        · have htailTime : source.discharge.tailStart ≤ 99734 := by
            rw [b.tailStart_eq]
            omega
          have habove := source.discharge.historical_tail.strictly_above
            99734 htailTime
          have htarget := sixtyone_le_of_target_missing
            source.discharge.combined.tail.target_missing
          rw [GeneratedBalancedTrace99734.generated_value] at habove
          omega
        · omega
      exact Or.inl ⟨by omega, hnineteen⟩
    · have htwenty : 20 ≤ a b.coverage := by omega
      have hmem := mem_valuesThrough_222_of_twenty_le_of_lt_sixtyone
        htwenty (by omega)
      rcases mem_valuesThrough_iff.mp hmem with
        ⟨witness, hwitness, hvalue⟩
      have hcoverageLe : b.coverage ≤ witness := by
        by_cases hearlier : witness < b.coverage
        · exact False.elim (b.predecessor_first.2 witness hearlier hvalue)
        · omega
      have htailTime : source.discharge.tailStart ≤ 99734 := by
        rw [b.tailStart_eq]
        omega
      have habove := source.discharge.historical_tail.strictly_above
        99734 htailTime
      have htarget := sixtyone_le_of_target_missing
        source.discharge.combined.tail.target_missing
      rw [GeneratedBalancedTrace99734.generated_value] at habove
      exact False.elim (by omega)

/-- The clock-181653 value sixty-one eliminates the remaining late-nineteen
boundary.  Every canonical last-coverage low is therefore at least 61. -/
theorem predecessor_sixtyone (b : BoundaryCertificate source) :
    61 ≤ a b.coverage := by
  rcases b.predecessor_nineteen_at_99734_or_sixtyone with
    ⟨hcoverage, _hvalue⟩ | hlarge
  · have htailTime : source.discharge.tailStart ≤ 181653 := by
      rw [b.tailStart_eq, hcoverage]
      omega
    have habove := source.discharge.historical_tail.strictly_above
      181653 htailTime
    have htarget := sixtytwo_le_of_target_missing
      source.discharge.combined.tail.target_missing
    rw [GeneratedBalancedTrace181653.generated_value] at habove
    exact False.elim (by omega)
  · exact hlarge

/-- Below 76, the only remaining canonical boundary is the authenticated
clock-181653 landing at 61. -/
theorem predecessor_sixtyone_at_181653_or_seventysix
    (b : BoundaryCertificate source) :
    (b.coverage = 181653 ∧ a b.coverage = 61) ∨
      76 ≤ a b.coverage := by
  by_cases hlarge : 76 ≤ a b.coverage
  · exact Or.inr hlarge
  · have hlow := b.predecessor_sixtyone
    by_cases hsixtyone : a b.coverage = 61
    · have hcoverageLe : b.coverage ≤ 181653 := by
        by_cases hearlier : 181653 < b.coverage
        · exact False.elim
            (b.predecessor_first.2 181653 hearlier
              (GeneratedBalancedTrace181653.generated_value.trans
                hsixtyone.symm))
        · omega
      have hcoverageGe : 181653 ≤ b.coverage := by
        by_cases hearlier : b.coverage < 181653
        · have htailTime : source.discharge.tailStart ≤ 181653 := by
            rw [b.tailStart_eq]
            omega
          have habove := source.discharge.historical_tail.strictly_above
            181653 htailTime
          have htarget := seventyseven_le_of_target_missing
            source.discharge.combined.tail.target_missing
          rw [GeneratedBalancedTrace181653.generated_value] at habove
          omega
        · omega
      exact Or.inl ⟨by omega, hsixtyone⟩
    · have hsixtytwo : 62 ≤ a b.coverage := by omega
      have hmem :=
        mem_valuesThrough_99_of_sixtytwo_le_of_lt_seventysix
          hsixtytwo (by omega)
      rcases mem_valuesThrough_iff.mp hmem with
        ⟨witness, hwitness, hvalue⟩
      have hcoverageLe : b.coverage ≤ witness := by
        by_cases hearlier : witness < b.coverage
        · exact False.elim
            (b.predecessor_first.2 witness hearlier hvalue)
        · omega
      have htailTime : source.discharge.tailStart ≤ 181643 := by
        rw [b.tailStart_eq]
        omega
      have habove := source.discharge.historical_tail.strictly_above
        181643 htailTime
      have htarget := seventyseven_le_of_target_missing
        source.discharge.combined.tail.target_missing
      rw [GeneratedBalancedTrace181653.generated_value_seventysix] at habove
      exact False.elim (by omega)

end LeastTailDischargeReturnCertificate.BoundaryCertificate

namespace LeastMissingCoverageValleyCertificate

/-- Source-free form of the exceptional-boundary elimination. -/
theorem coverage_ne_131 {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    h.coverage ≠ 131 := by
  intro hcoverage
  have htarget : 47 ≤ target :=
    fortyseven_le_of_target_missing h.target_missing
  have habove := h.permanent_above 222 (by omega)
  have hvalue : a 222 = 47 := by
    set_option maxRecDepth 100000 in decide
  omega

/-- The source-free boundary low is never the clock-131 value four. -/
theorem low_nineteen {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    19 ≤ a h.coverage := by
  rcases h.low_shape with hexception | hlarge
  · exact False.elim (h.coverage_ne_131 hexception.1)
  · exact hlarge

/-- Source-free form of the sharp low-value split. -/
theorem low_nineteen_at_99734_or_sixtyone {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    (h.coverage = 99734 ∧ a h.coverage = 19) ∨
      61 ≤ a h.coverage := by
  by_cases hlarge : 61 ≤ a h.coverage
  · exact Or.inr hlarge
  · have hlow : 19 ≤ a h.coverage := h.low_nineteen
    by_cases hnineteen : a h.coverage = 19
    · have hcoverageLe : h.coverage ≤ 99734 := by
        by_cases hearlier : 99734 < h.coverage
        · exact False.elim
            (h.low_first.2.2 99734 hearlier
              (GeneratedBalancedTrace99734.generated_value.trans
                hnineteen.symm))
        · omega
      have hcoverageGe : 99734 ≤ h.coverage := by
        by_cases hearlier : h.coverage < 99734
        · have habove := h.permanent_above 99734 (by omega)
          have htarget := sixtyone_le_of_target_missing h.target_missing
          rw [GeneratedBalancedTrace99734.generated_value] at habove
          omega
        · omega
      exact Or.inl ⟨by omega, hnineteen⟩
    · have htwenty : 20 ≤ a h.coverage := by omega
      have hmem := mem_valuesThrough_222_of_twenty_le_of_lt_sixtyone
        htwenty (by omega)
      rcases mem_valuesThrough_iff.mp hmem with
        ⟨witness, hwitness, hvalue⟩
      have hcoverageLe : h.coverage ≤ witness := by
        by_cases hearlier : witness < h.coverage
        · exact False.elim (h.low_first.2.2 witness hearlier hvalue)
        · omega
      have habove := h.permanent_above 99734 (by omega)
      have htarget := sixtyone_le_of_target_missing h.target_missing
      rw [GeneratedBalancedTrace99734.generated_value] at habove
      exact False.elim (by omega)

/-- Source-free final low-value bound after authenticating sixty-one. -/
theorem low_sixtyone {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    61 ≤ a h.coverage := by
  rcases h.low_nineteen_at_99734_or_sixtyone with
    ⟨hcoverage, _hvalue⟩ | hlarge
  · have habove := h.permanent_above 181653 (by omega)
    have htarget := sixtytwo_le_of_target_missing h.target_missing
    rw [GeneratedBalancedTrace181653.generated_value] at habove
    exact False.elim (by omega)
  · exact hlarge

/-- Source-free version of the final low split below 76. -/
theorem low_sixtyone_at_181653_or_seventysix {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    (h.coverage = 181653 ∧ a h.coverage = 61) ∨
      76 ≤ a h.coverage := by
  by_cases hlarge : 76 ≤ a h.coverage
  · exact Or.inr hlarge
  · have hlow := h.low_sixtyone
    by_cases hsixtyone : a h.coverage = 61
    · have hcoverageLe : h.coverage ≤ 181653 := by
        by_cases hearlier : 181653 < h.coverage
        · exact False.elim
            (h.low_first.2.2 181653 hearlier
              (GeneratedBalancedTrace181653.generated_value.trans
                hsixtyone.symm))
        · omega
      have hcoverageGe : 181653 ≤ h.coverage := by
        by_cases hearlier : h.coverage < 181653
        · have habove := h.permanent_above 181653 (by omega)
          have htarget := seventyseven_le_of_target_missing h.target_missing
          rw [GeneratedBalancedTrace181653.generated_value] at habove
          omega
        · omega
      exact Or.inl ⟨by omega, hsixtyone⟩
    · have hsixtytwo : 62 ≤ a h.coverage := by omega
      have hmem :=
        mem_valuesThrough_99_of_sixtytwo_le_of_lt_seventysix
          hsixtytwo (by omega)
      rcases mem_valuesThrough_iff.mp hmem with
        ⟨witness, hwitness, hvalue⟩
      have hcoverageLe : h.coverage ≤ witness := by
        by_cases hearlier : witness < h.coverage
        · exact False.elim (h.low_first.2.2 witness hearlier hvalue)
        · omega
      have habove := h.permanent_above 181643 (by omega)
      have htarget := seventyseven_le_of_target_missing h.target_missing
      rw [GeneratedBalancedTrace181653.generated_value_seventysix] at habove
      exact False.elim (by omega)

/-- The authenticated mex closes the entire interval from 76 through 878.
Any boundary low below 879 has already occurred by clock 181653.  Its
first-occurrence clock cannot be earlier (the permanent-above tail would
then be contradicted by `a 181653 = 61`) and cannot be later, so it is the
exact clock-181653 landing at 61. -/
theorem low_sixtyone_at_181653_or_eightHundredSeventyNine {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    (h.coverage = 181653 ∧ a h.coverage = 61) ∨
      879 ≤ a h.coverage := by
  by_cases hlarge : 879 ≤ a h.coverage
  · exact Or.inr hlarge
  · have hlow : a h.coverage < 879 := by omega
    have hmem :=
      GeneratedBalancedTrace181653.generated_mex879.1
        (a h.coverage) hlow
    rcases mem_valuesThrough_iff.mp hmem with
      ⟨witness, hwitness, hvalue⟩
    have hcoverageLe : h.coverage ≤ witness := by
      by_cases hearlier : witness < h.coverage
      · exact False.elim (h.low_first.2.2 witness hearlier hvalue)
      · omega
    have hcoverageLeDeep : h.coverage ≤ 181653 := by omega
    have hcoverageGeDeep : 181653 ≤ h.coverage := by
      by_cases hearlier : h.coverage < 181653
      · have habove := h.permanent_above 181653 (by omega)
        have htarget :=
          eightHundredSeventyNine_le_of_target_missing h.target_missing
        rw [GeneratedBalancedTrace181653.generated_value] at habove
        omega
      · omega
    have hcoverage : h.coverage = 181653 := by omega
    left
    refine ⟨hcoverage, ?_⟩
    rw [hcoverage]
    exact GeneratedBalancedTrace181653.generated_value

/-- Exact orbit data carried by the sole boundary below 76.  The two steps
ending at clocks 181652 and 181653 are consecutive legal subtractions, and
therefore consecutive first-occurrence landings. -/
structure ExceptionalSixtyoneHighCertificate {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) : Prop where
  target_eq : target = 879
  coverage_eq : h.coverage = 181653
  low_eq : a h.coverage = 61
  previous_value : a (h.coverage - 2) = 363366
  previous_subtraction :
    CanSubtract (h.coverage - 1) (stateAt (h.coverage - 2))
  incoming_high_value : a (h.coverage - 1) = 181714
  incoming_high_first : FirstAt a 181714 (h.coverage - 1)
  low_first : FirstAt a 61 h.coverage

/-- The authenticated endpoint mex pins the missing target of the exceptional
boundary exactly: smaller candidates have occurred, while a larger target
would require 879 to have occurred by the coverage clock. -/
theorem target_eq_879_of_sixtyone_exception {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target)
    (hcoverage : h.coverage = 181653) : target = 879 := by
  have hmex := GeneratedBalancedTrace181653.generated_mex879
  have htargetGe : 879 ≤ target := by
    by_cases hlt : target < 879
    · have hmem := hmex.1 target hlt
      rcases mem_valuesThrough_iff.mp hmem with
        ⟨time, _htime, hvalue⟩
      exact False.elim (h.target_missing ⟨time, hvalue⟩)
    · omega
  have htargetLe : target ≤ 879 := by
    by_cases hlt : 879 < target
    · have hmem := h.covers 879 hlt
      rw [hcoverage] at hmem
      exact False.elim (hmex.2 hmem)
    · omega
  omega

/-- The numerical exception in `low_sixtyone_at_181653_or_seventysix` is
not an unresolved backward case: the authenticated suffix fixes it to the
high-predecessor branch. -/
theorem exceptionalSixtyoneHighCertificate {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target)
    (hcoverage : h.coverage = 181653)
    (hlow : a h.coverage = 61) :
    h.ExceptionalSixtyoneHighCertificate := by
  have htarget := h.target_eq_879_of_sixtyone_exception hcoverage
  have hpreviousValue : a (h.coverage - 2) = 363366 := by
    simpa [hcoverage] using
      GeneratedBalancedTrace181653.generated_value_181651
  have hpreviousSubtraction :
      CanSubtract (h.coverage - 1) (stateAt (h.coverage - 2)) := by
    have hclockOne : h.coverage - 1 = 181652 := by omega
    have hclockTwo : h.coverage - 2 = 181651 := by omega
    rw [hclockOne, hclockTwo]
    exact GeneratedBalancedTrace181653.generated_previous_subtraction
  have hincomingHighValue : a (h.coverage - 1) = 181714 := by
    simpa [hcoverage] using
      GeneratedBalancedTrace181653.generated_value_181652
  have hincomingHighFirst :=
    h.incomingFirst_of_previousSubtraction hpreviousSubtraction
  rw [hincomingHighValue] at hincomingHighFirst
  have hlowFirst : FirstAt a 61 h.coverage := by
    simpa [hlow] using h.low_first.2
  exact {
    target_eq := htarget
    coverage_eq := hcoverage
    low_eq := hlow
    previous_value := hpreviousValue
    previous_subtraction := hpreviousSubtraction
    incoming_high_value := hincomingHighValue
    incoming_high_first := hincomingHighFirst
    low_first := hlowFirst
  }

/-- The exact maximal backward room in the fixed exception. -/
theorem ExceptionalSixtyoneHighCertificate.backwardRoom_eq
    {target : Nat} {h : LeastMissingCoverageValleyCertificate target}
    (certificate : h.ExceptionalSixtyoneHighCertificate) :
    h.backwardRoom = 180835 := by
  unfold backwardRoom
  have htarget := certificate.target_eq
  have hcoverage := certificate.coverage_eq
  have hlow := certificate.low_eq
  omega

/-- In the fixed exception the maximal backward chain stops immediately in
its explicit high-predecessor branch; neither the narrow nor the terminal
ratio branch remains possible. -/
theorem ExceptionalSixtyoneHighCertificate.depthZeroHigh
    {target : Nat} {h : LeastMissingCoverageValleyCertificate target}
    (certificate : h.ExceptionalSixtyoneHighCertificate) :
    ∃ stage : h.BackwardValleyStage 0,
      0 < h.backwardRoom ∧
        CanSubtract (stage.clock - 1) (stateAt (stage.clock - 2)) ∧
        a (stage.clock - 2) =
          a stage.clock + 2 * stage.clock - 1 := by
  let stage := h.initialBackwardValleyStage
  refine ⟨stage, ?_, ?_, ?_⟩
  · rw [certificate.backwardRoom_eq]
    omega
  · change CanSubtract (h.coverage - 1) (stateAt (h.coverage - 2))
    exact certificate.previous_subtraction
  · change a (h.coverage - 2) =
      a h.coverage + 2 * h.coverage - 1
    rw [certificate.previous_value, certificate.low_eq,
      certificate.coverage_eq]

/-- Direct first-branch witness for the maximal structural alternative in
the fixed exception. -/
theorem ExceptionalSixtyoneHighCertificate.maximalStructural_high
    {target : Nat} {h : LeastMissingCoverageValleyCertificate target}
    (certificate : h.ExceptionalSixtyoneHighCertificate) :
    h.MaximalBackwardStructuralAlternative := by
  unfold MaximalBackwardStructuralAlternative
  rcases certificate.depthZeroHigh with ⟨stage, hroom, hsub, hvalue⟩
  exact Or.inl ⟨0, stage, hroom, hsub, hvalue⟩

/-- Sharp source-free boundary split: either the low is already at least 76,
or the exact exceptional orbit segment (including both fresh subtractions)
is available. -/
theorem exceptionalSixtyoneHigh_or_low_seventysix {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    h.ExceptionalSixtyoneHighCertificate ∨ 76 ≤ a h.coverage := by
  rcases h.low_sixtyone_at_181653_or_seventysix with
    hexception | hlarge
  · exact Or.inl
      (h.exceptionalSixtyoneHighCertificate hexception.1 hexception.2)
  · exact Or.inr hlarge

/-- Mex-strengthened split: the exact fixed high branch is the only boundary
whose low lies below 879. -/
theorem exceptionalSixtyoneHigh_or_low_eightHundredSeventyNine
    {target : Nat} (h : LeastMissingCoverageValleyCertificate target) :
    h.ExceptionalSixtyoneHighCertificate ∨ 879 ≤ a h.coverage := by
  rcases h.low_sixtyone_at_181653_or_eightHundredSeventyNine with
    hexception | hlarge
  · exact Or.inl
      (h.exceptionalSixtyoneHighCertificate hexception.1 hexception.2)
  · exact Or.inr hlarge

/-- The exact exceptional certificate is equivalent to the missing target
being 879.  Thus target 879 has no residual boundary choice. -/
theorem exceptionalSixtyoneHigh_iff_target_eq_879 {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target) :
    h.ExceptionalSixtyoneHighCertificate ↔ target = 879 := by
  constructor
  · intro certificate
    exact certificate.target_eq
  · intro htarget
    rcases h.low_sixtyone_at_181653_or_eightHundredSeventyNine with
      hexception | hlarge
    · exact h.exceptionalSixtyoneHighCertificate
        hexception.1 hexception.2
    · have hbelow := h.low_first.1
      omega

/-- Sharp mex boundary dichotomy.  Outside the fixed target-879 exception,
both the target and the boundary low move to their next integer floors. -/
theorem exceptionalSixtyoneHigh_or_eightHundredEightyTargetLow
    {target : Nat} (h : LeastMissingCoverageValleyCertificate target) :
    h.ExceptionalSixtyoneHighCertificate ∨
      (880 ≤ target ∧ 879 ≤ a h.coverage) := by
  rcases h.exceptionalSixtyoneHigh_or_low_eightHundredSeventyNine with
    hexception | hlarge
  · exact Or.inl hexception
  · exact Or.inr ⟨by
      have hbelow := h.low_first.1
      omega, hlarge⟩

/-- Any authenticated occurrence of 879 eliminates the sole sub-76 boundary.
This is the exact non-computational bridge needed by a future
`a 328002 = 879` trace certificate. -/
theorem low_seventysix_of_879_occurs {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target)
    (hoccurs : ∃ time, a time = 879) : 76 ≤ a h.coverage := by
  rcases h.exceptionalSixtyoneHigh_or_low_seventysix with
    hexception | hlarge
  · rcases hoccurs with ⟨time, hvalue⟩
    exact False.elim
      (h.target_missing ⟨time, hvalue.trans hexception.target_eq.symm⟩)
  · exact hlarge

/-- With an occurrence of 879, the fixed exception disappears and the
boundary low is itself at least 879. -/
theorem low_eightHundredSeventyNine_of_879_occurs {target : Nat}
    (h : LeastMissingCoverageValleyCertificate target)
    (hoccurs : ∃ time, a time = 879) : 879 ≤ a h.coverage := by
  rcases h.exceptionalSixtyoneHigh_or_low_eightHundredSeventyNine with
    hexception | hlarge
  · rcases hoccurs with ⟨time, hvalue⟩
    exact False.elim
      (h.target_missing ⟨time, hvalue.trans hexception.target_eq.symm⟩)
  · exact hlarge

end LeastMissingCoverageValleyCertificate

/-- Once 879 itself is authenticated, every globally missing target is at
least 880. -/
theorem eightHundredEighty_le_of_target_missing_of_879_occurs
    {target : Nat} (hoccurs : ∃ time, a time = 879)
    (hmissing : ¬ ∃ time, a time = target) : 880 ≤ target := by
  have hbase := eightHundredSeventyNine_le_of_target_missing hmissing
  by_cases heq : target = 879
  · rcases hoccurs with ⟨time, hvalue⟩
    exact False.elim (hmissing ⟨time, hvalue.trans heq.symm⟩)
  · omega

/-- Strengthened summit-facing valley theorem: the final newly covered low
value is at least nineteen and the exceptional clock 131 is absent. -/
theorem LeastMissingTarget.exists_nonexceptionalCoverageValleyCertificate
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      certificate.coverage ≠ 131 ∧ 19 ≤ a certificate.coverage := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate, certificate.coverage_ne_131,
    certificate.low_nineteen⟩

/-- Sharp summit-facing boundary normal form after the first deep trace. -/
theorem LeastMissingTarget.exists_deepBoundaryValleyCertificate
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      61 ≤ target ∧ certificate.coverage ≠ 131 ∧
        ((certificate.coverage = 99734 ∧
            a certificate.coverage = 19) ∨
          61 ≤ a certificate.coverage) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    sixtyone_le_of_target_missing certificate.target_missing,
    certificate.coverage_ne_131,
    certificate.low_nineteen_at_99734_or_sixtyone⟩

/-- Final boundary normal form reached by the two authenticated deep traces.
The remaining obstruction begins at target 62 and its last covered low value
is at least 61. -/
theorem LeastMissingTarget.exists_sixtyoneBoundaryValleyCertificate
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      62 ≤ target ∧ 61 ≤ a certificate.coverage := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    sixtytwo_le_of_target_missing certificate.target_missing,
    certificate.low_sixtyone⟩

/-- Boundary normal form after reusing the 61 trace suffix to authenticate
76.  The target is at least 77, and low 61 survives only at its exact deep
clock; every other boundary low is at least 76. -/
theorem LeastMissingTarget.exists_seventysixBoundaryValleyCertificate
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      879 ≤ target ∧
        ((certificate.coverage = 181653 ∧
            a certificate.coverage = 61) ∨
          76 ≤ a certificate.coverage) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    eightHundredSeventyNine_le_of_target_missing certificate.target_missing,
    certificate.low_sixtyone_at_181653_or_seventysix⟩

/-- Strongest source-free summit package currently available: both deep
numeric bounds together with the exact backward normal form. -/
theorem LeastMissingTarget.exists_sixtyoneBoundaryBackwardNormalForm
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      62 ≤ target ∧ 61 ≤ a certificate.coverage ∧
        certificate.BackwardNormalForm := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    sixtytwo_le_of_target_missing certificate.target_missing,
    certificate.low_sixtyone,
    certificate.backwardNormalForm⟩

/-- The deep low bound makes sixty-one iterations of the non-numeric
backward-valley mechanism available.  An obstruction occurs at some earlier
depth, or the exact valley/budget certificate reaches depth 61. -/
theorem LeastMissingTarget.exists_sixtyoneStepBackwardValleyChain
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      62 ≤ target ∧ 61 ≤ a certificate.coverage ∧
        certificate.BackwardValleyChainOutcome 61 := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  have hlow := certificate.low_sixtyone
  exact ⟨certificate,
    sixtytwo_le_of_target_missing certificate.target_missing,
    hlow,
    certificate.backwardValleyChainOutcome 61 hlow⟩

/-- Expanded 61-step conclusion.  The narrow branch now appears as the
global quantitative bound `coverage ≤ low + 183`; otherwise there is an
explicit high predecessor or a depth-61 valley certificate. -/
theorem LeastMissingTarget.exists_sixtyoneStepBackwardAlternatives
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      62 ≤ target ∧ 61 ≤ a certificate.coverage ∧
        certificate.ExpandedBackwardValleyChainOutcome 61 := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  have hlow := certificate.low_sixtyone
  exact ⟨certificate,
    sixtytwo_le_of_target_missing certificate.target_missing,
    hlow,
    certificate.expandedBackwardValleyChainOutcome 61 hlow⟩

/-- Strongest current source-free summit: the authenticated lower bounds and
the sharp maximal-room backward trichotomy in one package. -/
theorem LeastMissingTarget.exists_maximalBackwardSharpAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      62 ≤ target ∧ 61 ≤ a certificate.coverage ∧
        certificate.MaximalBackwardSharpAlternative := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    sixtytwo_le_of_target_missing certificate.target_missing,
    certificate.low_sixtyone,
    certificate.maximalBackwardSharpAlternative⟩

/-- Same summit with the terminal ratio branch simplified to
`2 * boundaryLow ≤ target`; since the low is at least 61, that branch alone
raises the hypothetical missing target to at least 122. -/
theorem LeastMissingTarget.exists_maximalBackwardStructuralAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      62 ≤ target ∧ 61 ≤ a certificate.coverage ∧
        certificate.MaximalBackwardStructuralAlternative := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    sixtytwo_le_of_target_missing certificate.target_missing,
    certificate.low_sixtyone,
    certificate.maximalBackwardStructuralAlternative⟩

/-- Strongest combined endpoint of this development round. -/
theorem LeastMissingTarget.exists_deepSuffixBackwardStructuralAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      879 ≤ target ∧
        ((certificate.coverage = 181653 ∧
            a certificate.coverage = 61) ∨
          879 ≤ a certificate.coverage) ∧
        certificate.MaximalBackwardStructuralAlternative := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    eightHundredSeventyNine_le_of_target_missing certificate.target_missing,
    certificate.low_sixtyone_at_181653_or_eightHundredSeventyNine,
    certificate.maximalBackwardStructuralAlternative⟩

/-- The strongest combined endpoint pins the only sub-76 boundary to its
exact authenticated high-predecessor segment, while retaining the maximal
backward-chain structural alternative for every boundary. -/
theorem LeastMissingTarget.exists_deepSuffixPinnedBackwardAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      879 ≤ target ∧
        (certificate.ExceptionalSixtyoneHighCertificate ∨
          879 ≤ a certificate.coverage) ∧
        certificate.MaximalBackwardStructuralAlternative := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    eightHundredSeventyNine_le_of_target_missing certificate.target_missing,
    certificate.exceptionalSixtyoneHigh_or_low_eightHundredSeventyNine,
    certificate.maximalBackwardStructuralAlternative⟩

/-- Sharpest unconditional mex summit: exact target 879 with its fully
pinned depth-zero high branch, or simultaneous next floors for target and
boundary low. -/
theorem LeastMissingTarget.exists_mexPinnedBackwardAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      (certificate.ExceptionalSixtyoneHighCertificate ∨
        (880 ≤ target ∧ 879 ≤ a certificate.coverage)) ∧
        certificate.MaximalBackwardStructuralAlternative := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    certificate.exceptionalSixtyoneHigh_or_eightHundredEightyTargetLow,
    certificate.maximalBackwardStructuralAlternative⟩

/-- The mex-strengthened low floor supplies 879 concrete backward iterations
on the nonexceptional branch; the exceptional branch has already stopped at
depth zero with an explicit high predecessor. -/
theorem LeastMissingTarget.exists_eightHundredSeventyNineStepBackwardChain
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      certificate.ExceptionalSixtyoneHighCertificate ∨
        (880 ≤ target ∧ 879 ≤ a certificate.coverage ∧
          certificate.BackwardValleyChainOutcome 879) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  rcases certificate.exceptionalSixtyoneHigh_or_eightHundredEightyTargetLow
    with hexception | hlarge
  · exact ⟨certificate, Or.inl hexception⟩
  · exact ⟨certificate, Or.inr ⟨hlarge.1, hlarge.2,
      certificate.backwardValleyChainOutcome 879 hlarge.2⟩⟩

/-- Consumer form of the 879-step theorem.  Outside the exact exception,
there is a high predecessor before depth 879, the global narrow bound
`coverage ≤ low + 2637`, or an exact depth-879 valley whose preceding
missing-below budget is 880. -/
theorem LeastMissingTarget.exists_eightHundredSeventyNineStepAlternatives
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      certificate.ExceptionalSixtyoneHighCertificate ∨
        (880 ≤ target ∧ 879 ≤ a certificate.coverage ∧
          certificate.ExpandedBackwardValleyChainOutcome 879) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  rcases certificate.exceptionalSixtyoneHigh_or_eightHundredEightyTargetLow
    with hexception | hlarge
  · exact ⟨certificate, Or.inl hexception⟩
  · exact ⟨certificate, Or.inr ⟨hlarge.1, hlarge.2,
      certificate.expandedBackwardValleyChainOutcome 879 hlarge.2⟩⟩

/-- Numeric reading of the 879-step chain.  Its terminal stage raises the
hypothetical target to at least 1759. -/
theorem LeastMissingTarget.exists_eightHundredSeventyNineStepFloorAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      certificate.ExceptionalSixtyoneHighCertificate ∨
        (880 ≤ target ∧ 879 ≤ a certificate.coverage ∧
          certificate.BackwardValleyChainFloorAlternative 879 879) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  rcases certificate.exceptionalSixtyoneHigh_or_eightHundredEightyTargetLow
    with hexception | hlarge
  · exact ⟨certificate, Or.inl hexception⟩
  · have houtcome :=
      certificate.backwardValleyChainOutcome 879 hlarge.2
    exact ⟨certificate, Or.inr ⟨hlarge.1, hlarge.2,
      houtcome.floorAlternative hlarge.2⟩⟩

/-- History-connected reading of the 879-step chain.  Reaching full depth
produces a strict edge in the already well-founded
`TerminalHistoryBudgetDrop` relation. -/
theorem LeastMissingTarget.exists_eightHundredSeventyNineHistoryAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      certificate.ExceptionalSixtyoneHighCertificate ∨
        (880 ≤ target ∧ 879 ≤ a certificate.coverage ∧
          certificate.BackwardValleyChainHistoryAlternative 879) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  rcases certificate.exceptionalSixtyoneHigh_or_eightHundredEightyTargetLow
    with hexception | hlarge
  · exact ⟨certificate, Or.inl hexception⟩
  · have houtcome :=
      certificate.backwardValleyChainOutcome 879 hlarge.2
    exact ⟨certificate, Or.inr ⟨hlarge.1, hlarge.2,
      houtcome.historyAlternative (by omega)⟩⟩

/-- Maximal-room counterpart of the 879-step theorem.  Its terminal branch
is the absolute target floor `1758 ≤ target`. -/
theorem LeastMissingTarget.exists_eightHundredSeventyNineFloorAlternative
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      certificate.ExceptionalSixtyoneHighCertificate ∨
        (880 ≤ target ∧ 879 ≤ a certificate.coverage ∧
          certificate.MaximalBackwardFloorAlternative 879) := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  rcases certificate.exceptionalSixtyoneHigh_or_eightHundredEightyTargetLow
    with hexception | hlarge
  · exact ⟨certificate, Or.inl hexception⟩
  · exact ⟨certificate, Or.inr ⟨hlarge.1, hlarge.2,
      certificate.maximalBackwardFloorAlternative hlarge.2⟩⟩

/-- Conditional next-stage summit.  An authenticated occurrence of 879
removes the fixed deep exception without changing any structural argument. -/
theorem LeastMissingTarget.exists_eightHundredEightyBoundaryAlternative
    {target : Nat} (hoccurs : ∃ time, a time = 879)
    (h : LeastMissingTarget target) :
    ∃ certificate : LeastMissingCoverageValleyCertificate target,
      880 ≤ target ∧ 879 ≤ a certificate.coverage ∧
        certificate.MaximalBackwardStructuralAlternative := by
  rcases h.exists_coverageValleyCertificate with ⟨certificate⟩
  exact ⟨certificate,
    eightHundredEighty_le_of_target_missing_of_879_occurs
      hoccurs certificate.target_missing,
    certificate.low_eightHundredSeventyNine_of_879_occurs hoccurs,
    certificate.maximalBackwardStructuralAlternative⟩

end

end Recaman
