import Recaman.NegativeEpoch
import Recaman.HistoryBudget

namespace Recaman

/-- A forced addition in the nonnegative regular chamber with quotient at
least two exposes a previously seen subtraction candidate at least as large
as the next time.  Hence it resolves every target below that time. -/
theorem coordinates_add_regular_gives_coverageStep_below_nextTime
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hq : 2 ≤ q)
    (hregular : q ≤ r)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    CoverageStep m (a n) n := by
  have heq := hcoord.eqn
  have hmul : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
  let y := a n - (n + 1)
  have hpositive : n + 1 < a n := by
    omega
  have hnextTime_le : n + 1 ≤ y := by
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

/-- Strengthened low-quotient funnel.  Besides preserving the potential, its
endpoint never exceeds the starting value; this extra inequality lets later
history-aware progress be transported back through the subtraction prefix. -/
theorem nonnegative_epoch_lowQuotient_or_coverage_with_value
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnonnegative : 0 ≤ potential q r) :
    ∃ t k s,
      n ≤ t ∧ t ≤ n + q ∧
      a t ≤ a n ∧
      (t = n ∨ a t < a n) ∧
      (t = n → k = q) ∧
      CoordinatesAt t k s ∧
      potential k s = potential q r ∧
      (k ≤ 1 ∨ CoverageStep m (a n) n) := by
  induction q using Nat.strongRecOn generalizing n r with
  | ind q ih =>
      by_cases hlow : q ≤ 1
      · exact ⟨n, q, r, by omega, by omega, by omega, Or.inl rfl,
          fun _ => rfl,
          hcoord, rfl, Or.inl hlow⟩
      · have hq : 2 ≤ q := by omega
        have htri : q ≤ upperTri q := by
          rw [upperTri_eq_lowerTri_add]
          omega
        have hrtri : upperTri q ≤ r :=
          (potential_nonnegative_iff q r).mp hnonnegative
        have hregular : q ≤ r := Nat.le_trans htri hrtri
        by_cases hcan : CanSubtract (n + 1) (stateAt n)
        · have hnext := coordinates_sub_regular hcoord (by omega) hregular hcan
          have hnextNonnegative :
              0 ≤ potential (q - 1) (r - q) := by
            rw [hnext.2]
            exact hnonnegative
          have hmnext : m ≤ n + 1 + 1 := by omega
          rcases ih (q - 1) (by omega) hmnext hnext.1 hnextNonnegative with
            ⟨t, k, s, hnt, htbound, htvalue, _, _, htcoord,
              htpotential, hresult⟩
          have hpotential : potential k s = potential q r := by
            rw [htpotential, hnext.2]
          have hvalueNext := a_succ_of_canSubtract hcan
          have hvalueDrop : a (n + 1) < a n := by
            have hpositive : n + 1 < a n := by simpa [a] using hcan.1
            omega
          have hlifted : k ≤ 1 ∨ CoverageStep m (a n) n := by
            rcases hresult with hklow | hcoverage
            · exact Or.inl hklow
            · exact Or.inr (hcoverage.mono_parent hvalueDrop)
          exact ⟨t, k, s, by omega, by omega, by omega, Or.inr (by omega),
            fun h => by omega,
            htcoord, hpotential, hlifted⟩
        · have hcoverage : CoverageStep m (a n) n :=
            coordinates_add_regular_gives_coverageStep_below_nextTime
              hm hcoord hq hregular hcan
          exact ⟨n, q, r, by omega, by omega, by omega, Or.inl rfl,
            fun _ => rfl,
            hcoord, rfl, Or.inr hcoverage⟩

/-- Every actual nonnegative-potential state reaches, within at most its
current quotient many steps, either a low quotient `k≤1` at the same
potential level or a `CoverageStep` for every target `m≤n+1`.

Legal regular subtractions preserve `G` and lower the quotient.  A forced
addition before the quotient becomes low is discharged by the history
blocker above. -/
theorem nonnegative_epoch_lowQuotient_or_coverage
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnonnegative : 0 ≤ potential q r) :
    ∃ t k s,
      n ≤ t ∧ t ≤ n + q ∧
      CoordinatesAt t k s ∧
      potential k s = potential q r ∧
      (k ≤ 1 ∨ CoverageStep m (a n) n) := by
  rcases nonnegative_epoch_lowQuotient_or_coverage_with_value
      hm hcoord hnonnegative with
    ⟨t, k, s, hnt, htbound, _, _, _, htcoord, htpotential, hresult⟩
  exact ⟨t, k, s, hnt, htbound, htcoord, htpotential, hresult⟩

/-- Quotient zero is numerically too small to subtract the next time.  The
forced addition moves to quotient one and lowers the potential by exactly
one. -/
theorem coordinates_zeroQuotient_next {n r : Nat}
    (hcoord : CoordinatesAt n 0 r) :
    ¬ CanSubtract (n + 1) (stateAt n) ∧
      CoordinatesAt (n + 1) 1 r ∧
      potential 1 r = potential 0 r - 1 := by
  have heq := hcoord.eqn
  have hrlt := hcoord.remainder_lt
  have hnot : ¬ CanSubtract (n + 1) (stateAt n) := by
    intro hcan
    have hpositive : n + 1 < a n := by simpa [a] using hcan.1
    omega
  have hnext := coordinates_add_regular hcoord (by omega) hnot
  refine ⟨hnot, ?_, ?_⟩
  · simpa using hnext.1
  · simp [potential, upperTri]

/-- Once the nonnegative regular descent reaches quotient zero or one, the
actual orbit strictly lowers `G` within at most two further steps.

At quotient zero the next step is a forced addition and lowers `G` by one.
At quotient one, a forced addition lowers it by three; a legal subtraction
first moves to quotient zero and the following forced addition lowers it by
one. -/
theorem lowQuotient_nonnegative_potential_drop
    {n q r : Nat}
    (hcoord : CoordinatesAt n q r)
    (hlow : q ≤ 1)
    (hnonnegative : 0 ≤ potential q r) :
    ∃ t k s,
      n < t ∧ t ≤ n + 2 ∧
      a n < a t ∧
      (a t = a n + (n + 1) ∨ a t = a n + 1) ∧
      CoordinatesAt t k s ∧
      (potential k s = potential q r - 1 ∨
        potential k s = potential q r - 3) ∧
      potential k s < potential q r := by
  have hcases : q = 0 ∨ q = 1 := by omega
  rcases hcases with hzero | hone
  · subst q
    rcases coordinates_zeroQuotient_next hcoord with
      ⟨hnot, hnext, hpotential⟩
    have hvalue := a_succ_of_not_canSubtract hnot
    exact ⟨n + 1, 1, r, by omega, by omega, by omega,
      Or.inl hvalue, hnext, Or.inl hpotential, by omega⟩
  · subst q
    have hrtri : upperTri 1 ≤ r :=
      (potential_nonnegative_iff 1 r).mp hnonnegative
    have hregular : 1 ≤ r := by
      simpa [upperTri] using hrtri
    by_cases hcan : CanSubtract (n + 1) (stateAt n)
    · have hsub := coordinates_sub_regular hcoord (by omega) hregular hcan
      have hzeroCoord : CoordinatesAt (n + 1) 0 (r - 1) := by
        simpa using hsub.1
      rcases coordinates_zeroQuotient_next hzeroCoord with
        ⟨hnotNext, hnext, hdrop⟩
      have hsubValue := a_succ_of_canSubtract hcan
      have haddValue := a_succ_of_not_canSubtract hnotNext
      have haddValue' : a (n + 2) = a (n + 1) + (n + 2) := by
        simpa [Nat.add_assoc] using haddValue
      have hpositive : n + 1 < a n := by simpa [a] using hcan.1
      have hpreserve : potential 0 (r - 1) = potential 1 r := by
        simpa using hsub.2
      have hexactDrop :
          potential 1 (r - 1) = potential 1 r - 1 := by
        omega
      have hpotential : potential 1 (r - 1) < potential 1 r := by
        omega
      exact ⟨n + 2, 1, r - 1, by omega, by omega,
        by omega, Or.inr (by omega),
        by simpa [Nat.add_assoc] using hnext,
        Or.inl hexactDrop, hpotential⟩
    · have hadd := coordinates_add_regular hcoord hregular hcan
      have hvalue := a_succ_of_not_canSubtract hcan
      have heq : potential 2 (r - 1) =
          potential 1 r - Int.ofNat 3 := by
        simpa using hadd.2
      have hpotential : potential 2 (r - 1) < potential 1 r := by
        have hthree : (0 : Int) < Int.ofNat 3 := by decide
        omega
      exact ⟨n + 1, 2, r - 1, by omega, by omega,
        by omega, Or.inl hvalue, by simpa using hadd.1,
        Or.inr heq, hpotential⟩

/-- A low-quotient state on level `G=g` records the level value `g` in the
actual history no later than the following time.  At quotient zero it is the
current value.  At quotient one it is either the legal subtraction endpoint
or the already-seen candidate which forces addition. -/
theorem lowQuotient_level_seen_next
    {n q r g : Nat}
    (hcoord : CoordinatesAt n q r)
    (hlow : q ≤ 1)
    (hpotential : potential q r = Int.ofNat g) :
    g ∈ valuesThrough (n + 1) := by
  have hcases : q = 0 ∨ q = 1 := by omega
  rcases hcases with hzero | hone
  · subst q
    have hr : r = g := by
      simpa [upperTri] using
        (potential_eq_ofNat_iff 0 r g).mp hpotential
    have heq := hcoord.eqn
    have hvalue : a n = g := by
      omega
    have hmem : g ∈ valuesThrough n := by
      rw [← hvalue]
      exact current_mem_valuesThrough n
    exact valuesThrough_persist hmem
  · subst q
    have hr : r = 1 + g := by
      simpa [upperTri] using
        (potential_eq_ofNat_iff 1 r g).mp hpotential
    have heq := hcoord.eqn
    have hcandidate : a n - (n + 1) = g := by
      omega
    by_cases hcan : CanSubtract (n + 1) (stateAt n)
    · have hnext := a_succ_of_canSubtract hcan
      have hvalue : a (n + 1) = g := by omega
      rw [← hvalue]
      exact current_mem_valuesThrough (n + 1)
    · by_cases hseen : g ∈ valuesThrough n
      · exact valuesThrough_persist hseen
      · have hzeroSeen : 0 ∈ valuesThrough n :=
          mem_valuesThrough_iff.mpr ⟨0, Nat.zero_le n, rfl⟩
        have hgpos : 0 < g := by
          by_cases hgzero : g = 0
          · have : g ∈ valuesThrough n := by
              simpa [hgzero] using hzeroSeen
            exact False.elim (hseen this)
          · omega
        have hpositive : n + 1 < a n := by
          omega
        have hcan' : CanSubtract (n + 1) (stateAt n) := by
          constructor
          · simpa [a] using hpositive
          · change a n - (n + 1) ∉ valuesThrough n
            rw [hcandidate]
            exact hseen
        exact False.elim (hcan hcan')

/-- The regular descent preceding the low-quotient cleanup therefore either
produces coverage or records the entire starting potential level `g` in the
actual history within the quotient budget. -/
theorem nonnegative_epoch_records_level_or_coverage
    {m n q r g : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hpotential : potential q r = Int.ofNat g) :
    CoverageStep m (a n) n ∨
      ∃ t,
        n ≤ t ∧ t ≤ n + q + 1 ∧
        g ∈ valuesThrough t := by
  have hnonnegative : 0 ≤ potential q r := by
    rw [hpotential]
    exact Int.natCast_nonneg g
  rcases nonnegative_epoch_lowQuotient_or_coverage
      hm hcoord hnonnegative with
    ⟨u, k, s, hnu, hubound, hucoord, hupotential, hresult⟩
  rcases hresult with hklow | hcoverage
  · have hlevel : potential k s = Int.ofNat g := by
      rw [hupotential, hpotential]
    have hseen := lowQuotient_level_seen_next hucoord hklow hlevel
    exact Or.inr ⟨u + 1, by omega, by omega, hseen⟩
  · exact Or.inl hcoverage

/-- A complete nonnegative epoch either supplies a `CoverageStep` from its
starting value or reaches a later actual state of strictly smaller potential.
The time bound is the quotient descent budget plus the two low-quotient
cleanup steps. -/
theorem nonnegative_epoch_potential_drop_or_coverage
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnonnegative : 0 ≤ potential q r) :
    CoverageStep m (a n) n ∨
      ∃ t k s,
        n < t ∧ t ≤ n + q + 2 ∧
        CoordinatesAt t k s ∧
        potential k s < potential q r := by
  rcases nonnegative_epoch_lowQuotient_or_coverage
      hm hcoord hnonnegative with
    ⟨u, p, v, hnu, hubound, hucoord, hupotential, hresult⟩
  rcases hresult with hplow | hcoverage
  · rcases lowQuotient_nonnegative_potential_drop
      hucoord hplow (by rw [hupotential]; exact hnonnegative) with
      ⟨t, k, s, hut, htbound, _, _, htcoord, _, hdrop⟩
    exact Or.inr ⟨t, k, s, by omega, by omega, htcoord, by omega⟩
  · exact Or.inl hcoverage

/-- In particular, a finite undershoot strip `0≤G<m` is dynamically reduced
to one of three outcomes: a coverage certificate, a return to the negative
half-space, or a strictly lower level of the same undershoot strip. -/
theorem undershoot_epoch_trichotomy
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnonnegative : 0 ≤ potential q r)
    (hbelow : potential q r < Int.ofNat m) :
    CoverageStep m (a n) n ∨
      ∃ t k s,
        n < t ∧ t ≤ n + q + 2 ∧
        CoordinatesAt t k s ∧
        ((potential k s < 0) ∨
          (0 ≤ potential k s ∧
            potential k s < potential q r ∧
            potential k s < Int.ofNat m)) := by
  rcases nonnegative_epoch_potential_drop_or_coverage
      hm hcoord hnonnegative with hcoverage |
        ⟨t, k, s, hnt, htbound, htcoord, hdrop⟩
  · exact Or.inl hcoverage
  · refine Or.inr ⟨t, k, s, hnt, htbound, htcoord, ?_⟩
    by_cases hnextNonnegative : 0 ≤ potential k s
    · exact Or.inr ⟨hnextNonnegative, hdrop, by omega⟩
    · exact Or.inl (by omega)

/-- Strong induction on the attained nonnegative potential level closes the
entire finite strip as a *dynamical* statement.  Starting from `G=g<m`, the
actual orbit eventually either returns to `G<0` or reaches a later state that
itself carries a `CoverageStep`.

The coverage certificate here is deliberately attached to the later state.
Transporting it back to the original first-occurrence parent requires an
additional value bound and is the remaining global-proof issue. -/
theorem undershootLevel_eventually_negative_or_localCoverage
    {m n q r g : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hpotential : potential q r = Int.ofNat g)
    (hgm : g < m) :
    ∃ t k s,
      n ≤ t ∧ CoordinatesAt t k s ∧
      (potential k s < 0 ∨ CoverageStep m (a t) t) := by
  induction g using Nat.strongRecOn generalizing n q r with
  | ind g ih =>
      have hnonnegative : 0 ≤ potential q r := by
        rw [hpotential]
        exact Int.natCast_nonneg g
      have hbelow : potential q r < Int.ofNat m := by
        rw [hpotential]
        exact Int.ofNat_lt.mpr hgm
      rcases undershoot_epoch_trichotomy hm hcoord hnonnegative hbelow with
        hcoverage | ⟨t, k, s, hnt, _, htcoord, hresult⟩
      · exact ⟨n, q, r, Nat.le_refl _, hcoord, Or.inr hcoverage⟩
      · rcases hresult with hnegative |
          ⟨hnextNonnegative, hdrop, hnextBelow⟩
        · exact ⟨t, k, s, Nat.le_of_lt hnt, htcoord, Or.inl hnegative⟩
        · let g' := s - upperTri k
          have htri : upperTri k ≤ s :=
            (potential_nonnegative_iff k s).mp hnextNonnegative
          have hnextPotential : potential k s = Int.ofNat g' := by
            apply (potential_eq_ofNat_iff k s g').mpr
            simp only [g']
            omega
          have hglt : g' < g := by
            rw [hnextPotential, hpotential] at hdrop
            exact Int.ofNat_lt.mp hdrop
          have hgm' : g' < m := Nat.lt_trans hglt hgm
          have hmnext : m ≤ t + 1 := by omega
          rcases ih g' hglt hmnext htcoord hnextPotential hgm' with
            ⟨u, p, v, htu, hucoord, huresult⟩
          exact ⟨u, p, v, by omega, hucoord, huresult⟩

/-- User-facing form of the preceding theorem, recovering the natural
potential level from an arbitrary point of the undershoot strip. -/
theorem undershoot_eventually_negative_or_localCoverage
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnonnegative : 0 ≤ potential q r)
    (hbelow : potential q r < Int.ofNat m) :
    ∃ t k s,
      n ≤ t ∧ CoordinatesAt t k s ∧
      (potential k s < 0 ∨ CoverageStep m (a t) t) := by
  let g := r - upperTri q
  have htri : upperTri q ≤ r :=
    (potential_nonnegative_iff q r).mp hnonnegative
  have hpotential : potential q r = Int.ofNat g := by
    apply (potential_eq_ofNat_iff q r g).mpr
    simp only [g]
    omega
  have hgm : g < m := by
    rw [hpotential] at hbelow
    exact Int.ofNat_lt.mp hbelow
  exact undershootLevel_eventually_negative_or_localCoverage
    hm hcoord hpotential hgm

/-- One complete negative-to-undershoot cycle.  Starting from `G<0`, either
the original state already obtains a coverage certificate, or the actual
orbit reaches a later negative state / later local coverage certificate. -/
theorem negative_undershoot_cycle
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnegative : potential q r < 0) :
    CoverageStep m (a n) n ∨
      ∃ t k s,
        n < t ∧ CoordinatesAt t k s ∧
        (potential k s < 0 ∨ CoverageStep m (a t) t) := by
  rcases negative_epoch_undershoot_or_coverage hm hcoord hnegative with
    ⟨u, q', r', b, s, k, hnu, _, hucoord, hborrow,
      hkcoord, hfrontier⟩
  rcases hfrontier with hundershoot | hcoverage
  · have hmnext : m ≤ (u + 1) + 1 := by omega
    rcases undershoot_eventually_negative_or_localCoverage
      hmnext hkcoord hundershoot.1 hundershoot.2 with
      ⟨t, p, v, hut, htcoord, htresult⟩
    exact Or.inr ⟨t, p, v, by omega, htcoord, htresult⟩
  · exact Or.inl hcoverage

/-- Exact frontier after one sign cycle.  If the later state has smaller
ordinary value, it already lifts to a `CoverageStep` for the original parent.
Consequently every unresolved cycle must return with a value at least as large
as the starting value.  This isolates the remaining conflict between
potential descent and value induction. -/
theorem negative_undershoot_cycle_coverage_or_parentGrowth
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hnegative : potential q r < 0) :
    CoverageStep m (a n) n ∨
      ∃ t k s,
        n < t ∧ a n ≤ a t ∧ CoordinatesAt t k s ∧
        (potential k s < 0 ∨ CoverageStep m (a t) t) := by
  rcases negative_undershoot_cycle hm hcoord hnegative with
    hcoverage | ⟨t, k, s, hnt, htcoord, htresult⟩
  · exact Or.inl hcoverage
  · by_cases hvalueDrop : a t < a n
    · rcases htresult with htnegative | htcoverage
      · have hkpos : 0 < k := by
          cases k with
          | zero =>
              simp [potential, upperTri] at htnegative
              omega
          | succ k => omega
        have hvalue := htcoord.eqn
        have htimeTarget : m ≤ t := by omega
        have hmul : t * 1 ≤ t * k := Nat.mul_le_mul_left t hkpos
        have hmvalue : m ≤ a t := by omega
        rcases exists_firstAt (seq := a) (x := a t) ⟨t, rfl⟩ with
          ⟨ft, hfirst⟩
        exact Or.inl
          (Or.inr ⟨a t, ft, hmvalue, hfirst, hvalueDrop⟩)
      · exact Or.inl (htcoverage.mono_parent hvalueDrop)
    · exact Or.inr ⟨t, k, s, hnt, by omega, htcoord, htresult⟩

end Recaman
