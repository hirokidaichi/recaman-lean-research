import Recaman.RecoveryFrontier

namespace Recaman

/-- A forced zero-borrow addition from negative potential exposes a positive
history blocker at least as large as the next time.  Hence it resolves every
target `m≤n+1` by the value-decreasing branch of `CoverageStep`. -/
theorem coordinates_add_zeroBorrow_negative_gives_coverageStep
    {m n q r b s : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hborrow : BorrowData n q r b s)
    (hb : b = 0)
    (hnegative : potential q r < 0)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    CoverageStep m (a n) n := by
  have hq : 2 ≤ q :=
    two_le_quotient_of_negative_zeroBorrow hborrow hb hnegative
  have hregular : q ≤ r := by
    have hbal := hborrow.balance
    subst b
    simp at hbal
    omega
  have heq := hcoord.eqn
  let y := a n - (n + 1)
  have hpositive : n + 1 < a n := by
    have hmul : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
    omega
  have hnextTime_le : n + 1 ≤ y := by
    have hmul : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
    simp only [y]
    omega
  have hylt : y < a n := by
    simp only [y]
    omega
  have hseen : y ∈ valuesThrough n := by
    by_cases hySeen : y ∈ valuesThrough n
    · exact hySeen
    · have hcan : CanSubtract (n + 1) (stateAt n) := by
        constructor
        · simpa [a] using hpositive
        · change a n - (n + 1) ∉ valuesThrough n
          simpa only [y] using hySeen
      exact False.elim (hnot hcan)
  rcases history_member_has_firstAt hseen with ⟨fy, _, hfirstY⟩
  exact Or.inr
    ⟨y, fy, Nat.le_trans hm hnextTime_le, hfirstY, hylt⟩

/-- A legal subtraction whose endpoint potential is at least the fixed target
already lands on a new smaller value above that target. -/
theorem coordinates_sub_potential_aboveTarget_gives_coverageStep
    {m n q r b s : Nat}
    (hcoord : CoordinatesAt n q r)
    (hborrow : BorrowData n q r b s)
    (hcan : CanSubtract (n + 1) (stateAt n))
    (habove : Int.ofNat m ≤ potential (q - 1 - b) s) :
    CoverageStep m (a n) n := by
  have hpositive : n + 1 < a n := by simpa [a] using hcan.1
  have hbq : b + 1 ≤ q :=
    hborrow.add_one_le_q_of_positive hcoord hpositive
  have hnext := coordinates_sub_borrowData hcoord hborrow hbq hcan
  have hs : upperTri (q - 1 - b) + m ≤ s :=
    (ofNat_le_potential_iff (q - 1 - b) s m).mp habove
  have hvalueNext := hnext.1.eqn
  have hmnext : m ≤ a (n + 1) := by omega
  exact subtraction_gives_coverageStep hcan hmnext

/-- A one-borrow forced addition whose endpoint potential reaches at least
`m` also gives a pre-state `CoverageStep`.  We apply the borrow-target chart
at the exact attained level and then lower that target to `m`. -/
theorem coordinates_add_oneBorrow_potential_aboveTarget_gives_coverageStep
    {m n q r b s : Nat}
    (hcoord : CoordinatesAt n q r)
    (hborrow : BorrowData n q r b s)
    (hb : b = 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n))
    (habove : Int.ofNat m ≤ potential (q + 1 - b) s) :
    CoverageStep m (a n) n := by
  let k := q + 1 - b
  have hsLower : upperTri k + m ≤ s :=
    (ofNat_le_potential_iff k s m).mp (by simpa only [k] using habove)
  let M := s - upperTri k
  have hkTri : upperTri k ≤ s := by omega
  have htarget : potential k s = Int.ofNat M := by
    apply (potential_eq_ofNat_iff k s M).mpr
    simp only [M]
    omega
  have hmM : m ≤ M := by
    simp only [M]
    omega
  have hcoverageM : CoverageStep M (a n) n := by
    exact coordinates_add_target_prestate_gives_coverageStep
      hcoord hborrow hnot (by simpa only [k] using htarget)
  have hqpos : 0 < q := by
    have hchamber := hborrow.eq_one_iff.mp hb
    omega
  have hkpos : 0 < k := by
    subst b
    simp only [k, Nat.add_sub_cancel]
    exact hqpos
  have hbq : b ≤ q + 1 := hborrow.le_q_add_one
  have hquotient : q + 1 = b + k :=
    (add_borrowQuotient_eq_iff hbq).mp rfl
  have hpreimage : BorrowTargetPreimage n q r b k M :=
    (potential_eq_iff_borrowTargetPreimage hborrow).mp htarget
  have hvalue := add_borrowTarget_prestate_value
    hcoord hborrow hkpos hquotient hpreimage
  have htriPos := upperTri_pos hkpos
  have hMlt : M < a n := by omega
  exact hcoverageM.lower_target hmM hMlt

/-- Main finite negative-epoch theorem.  For every target below the next time,
within `⌊r/2⌋` steps the actual orbit either supplies a `CoverageStep` from
the original value or exits into the finite undershoot strip `0≤G<m`.
Legal zero-borrow subtractions recurse on the smaller remainder and transport
the value-decreasing certificate back to the original parent; forced
additions are discharged by their history blocker. -/
theorem negative_epoch_undershoot_or_coverage_with_value
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnegative : potential q r < 0) :
    ∃ t q' r' b s k,
      n ≤ t ∧ t ≤ n + r / 2 ∧
      a t ≤ a n ∧ (t = n ∨ a t < a n) ∧
      CoordinatesAt t q' r' ∧ BorrowData t q' r' b s ∧
      CoordinatesAt (t + 1) k s ∧
      ((b = 1 ∧
          0 ≤ potential k s ∧ potential k s < Int.ofNat m ∧
          ((CanSubtract (t + 1) (stateAt t) ∧ k = q' - 1 - b) ∨
            (¬ CanSubtract (t + 1) (stateAt t) ∧
              k = q' + 1 - b))) ∨
        CoverageStep m (a n) n) := by
  induction r using Nat.strongRecOn generalizing n q with
  | ind r ih =>
      rcases exists_borrowData hcoord.remainder_lt with ⟨b, s, hborrow⟩
      rcases hborrow.eq_zero_or_one_of_coordinatesAt hcoord with hb | hb
      · have hsdrop := zeroBorrow_remainder_drop hborrow hb hnegative
        have hslt : s < r := by omega
        by_cases hcan : CanSubtract (n + 1) (stateAt n)
        · have hpositive : n + 1 < a n := by simpa [a] using hcan.1
          have hbq : b + 1 ≤ q :=
            hborrow.add_one_le_q_of_positive hcoord hpositive
          have hnext :=
            coordinates_sub_borrowData hcoord hborrow hbq hcan
          have hnextNegative :=
            sub_zeroBorrow_preserves_negative hborrow hb hbq hnegative
          have hmnext : m ≤ n + 1 + 1 := by omega
          rcases ih s hslt hmnext hnext.1 hnextNegative with
            ⟨t, q', r', b', u, k, hnt, htbound, htvalue, _, htcoord,
              htborrow, hkcoord, hfrontier⟩
          have hvalueNext := a_succ_of_canSubtract hcan
          have hvalueDrop : a (n + 1) < a n := by omega
          have hlifted :
              ((b' = 1 ∧
                  0 ≤ potential k u ∧
                  potential k u < Int.ofNat m ∧
                  ((CanSubtract (t + 1) (stateAt t) ∧
                      k = q' - 1 - b') ∨
                    (¬ CanSubtract (t + 1) (stateAt t) ∧
                      k = q' + 1 - b'))) ∨
                CoverageStep m (a n) n) := by
            rcases hfrontier with hundershoot | hcoverage
            · exact Or.inl hundershoot
            · exact Or.inr (hcoverage.mono_parent hvalueDrop)
          exact ⟨t, q', r', b', u, k, by omega, by omega,
            by omega, Or.inr (by omega),
            htcoord, htborrow, hkcoord, hlifted⟩
        · have hbq : b ≤ q + 1 := hborrow.le_q_add_one
          have hnext :=
            coordinates_add_borrowData hcoord hborrow hbq hcan
          have hcoverage :=
            coordinates_add_zeroBorrow_negative_gives_coverageStep
              hm hcoord hborrow hb hnegative hcan
          exact ⟨n, q, r, b, s, q + 1 - b, by omega, by omega,
            by omega, Or.inl rfl,
            hcoord, hborrow, hnext.1, Or.inr hcoverage⟩
      · by_cases hcan : CanSubtract (n + 1) (stateAt n)
        · have hpositive : n + 1 < a n := by simpa [a] using hcan.1
          have hbq : b + 1 ≤ q :=
            hborrow.add_one_le_q_of_positive hcoord hpositive
          have hnext :=
            coordinates_sub_borrowData hcoord hborrow hbq hcan
          let k := q - 1 - b
          have hkcoord : CoordinatesAt (n + 1) k s := by
            simpa only [k] using hnext.1
          by_cases hnonnegative : 0 ≤ potential k s
          · by_cases habove : Int.ofNat m ≤ potential k s
            · have hcoverage : CoverageStep m (a n) n :=
                coordinates_sub_potential_aboveTarget_gives_coverageStep
                  hcoord hborrow hcan (by simpa only [k] using habove)
              exact ⟨n, q, r, b, s, k, by omega, by omega,
                by omega, Or.inl rfl,
                hcoord, hborrow, hkcoord, Or.inr hcoverage⟩
            · have hbelow : potential k s < Int.ofNat m := by omega
              exact ⟨n, q, r, b, s, k, by omega, by omega,
                by omega, Or.inl rfl,
                hcoord, hborrow, hkcoord,
                Or.inl ⟨hb, hnonnegative, hbelow,
                  Or.inl ⟨hcan, rfl⟩⟩⟩
          · have hknegative : potential k s < 0 := by omega
            have hkhigh : 4 ≤ k := by
              simpa only [k] using
                (coordinates_sub_oneBorrow_negative_highQuotient
                  hcoord hborrow hb hcan hknegative)
            have hvalueNext := hkcoord.eqn
            have hmnext : m ≤ a (n + 1) := by
              have hmul : (n + 1) * 1 ≤ (n + 1) * k :=
                Nat.mul_le_mul_left (n + 1) (by omega)
              omega
            have hcoverage : CoverageStep m (a n) n :=
              subtraction_gives_coverageStep hcan hmnext
            exact ⟨n, q, r, b, s, k, by omega, by omega,
              by omega, Or.inl rfl,
              hcoord, hborrow, hkcoord, Or.inr hcoverage⟩
        · have hbq : b ≤ q + 1 := hborrow.le_q_add_one
          have hnext :=
            coordinates_add_borrowData hcoord hborrow hbq hcan
          let k := q + 1 - b
          have hkcoord : CoordinatesAt (n + 1) k s := by
            simpa only [k] using hnext.1
          by_cases hnonnegative : 0 ≤ potential k s
          · by_cases habove : Int.ofNat m ≤ potential k s
            · have hcoverage : CoverageStep m (a n) n :=
                coordinates_add_oneBorrow_potential_aboveTarget_gives_coverageStep
                  hcoord hborrow hb hcan (by simpa only [k] using habove)
              exact ⟨n, q, r, b, s, k, by omega, by omega,
                by omega, Or.inl rfl,
                hcoord, hborrow, hkcoord, Or.inr hcoverage⟩
            · have hbelow : potential k s < Int.ofNat m := by omega
              exact ⟨n, q, r, b, s, k, by omega, by omega,
                by omega, Or.inl rfl,
                hcoord, hborrow, hkcoord,
                Or.inl ⟨hb, hnonnegative, hbelow,
                  Or.inr ⟨hcan, rfl⟩⟩⟩
          · have hknegative : potential k s < 0 := by omega
            have hmDouble : m ≤ 2 * (n + 1) := by omega
            have hcoverage : CoverageStep m (a n) n :=
              coordinates_add_oneBorrow_negative_gives_coverageStep_below_doubleTime
                hmDouble hcoord hborrow hb hcan hknegative
            exact ⟨n, q, r, b, s, k, by omega, by omega,
              by omega, Or.inl rfl,
              hcoord, hborrow, hkcoord, Or.inr hcoverage⟩

/-- Backward-compatible projection of the strengthened negative-epoch
frontier. -/
theorem negative_epoch_undershoot_or_coverage
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnegative : potential q r < 0) :
    ∃ t q' r' b s k,
      n ≤ t ∧ t ≤ n + r / 2 ∧
      CoordinatesAt t q' r' ∧ BorrowData t q' r' b s ∧
      CoordinatesAt (t + 1) k s ∧
      ((0 ≤ potential k s ∧ potential k s < Int.ofNat m) ∨
        CoverageStep m (a n) n) := by
  rcases negative_epoch_undershoot_or_coverage_with_value
      hm hcoord hnegative with
    ⟨t, q', r', b, s, k, hnt, htbound, _, _, htcoord,
      htborrow, hkcoord, hfrontier⟩
  have hprojected :
      ((0 ≤ potential k s ∧ potential k s < Int.ofNat m) ∨
        CoverageStep m (a n) n) := by
    rcases hfrontier with ⟨_, hnonnegative, hbelow, _⟩ | hcoverage
    · exact Or.inl ⟨hnonnegative, hbelow⟩
    · exact Or.inr hcoverage
  exact ⟨t, q', r', b, s, k, hnt, htbound,
    htcoord, htborrow, hkcoord, hprojected⟩

end Recaman
