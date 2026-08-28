import Recaman.Undershoot

namespace Recaman

/-- Every positive-time quotient-zero state was reached by a legal
subtraction, hence its current value is genuinely at its first occurrence. -/
theorem zeroQuotient_firstAt {n r : Nat}
    (hn : 0 < n)
    (hcoord : CoordinatesAt n 0 r) :
    FirstAt a r n := by
  cases n with
  | zero => omega
  | succ u =>
      have heq := hcoord.eqn
      have hrlt := hcoord.remainder_lt
      have hcan : CanSubtract (u + 1) (stateAt u) := by
        by_cases h : CanSubtract (u + 1) (stateAt u)
        · exact h
        · have hadd := a_succ_of_not_canSubtract h
          simp at heq
          omega
      have hfirst := firstAt_succ_of_canSubtract hcan
      have hvalue : a (u + 1) = r := by
        simp at heq
        exact heq
      simpa [hvalue] using hfirst

/-- A quotient-zero landing reached strictly after a parent time consumes one
missing target-smaller value.  This is the bridge which absorbs the sole
boundary exception of `nonnegative_epoch_historyFrontier` when the state was
entered from a preceding negative epoch. -/
theorem later_zeroQuotient_historyBudgetProgress
    {m n t r : Nat}
    (hnt : n < t)
    (hrm : r < m)
    (hcoord : CoordinatesAt t 0 r) :
    HistoryBudgetProgress m
      ⟨a t, t⟩ ⟨a n, n⟩ := by
  have hfirst : FirstAt a r t :=
    zeroQuotient_firstAt (by omega) hcoord
  have hdrop :
      missingBelowCount m t < missingBelowCount m n :=
    missingBelowCount_strict_of_firstAt hrm hnt hfirst
  exact historyBudgetProgress_of_budgetDrop hdrop

/-- The key low-quotient history frontier.  On a nonnegative level `g≥3` at
quotient one, within two actual steps either:

* a legal subtraction makes the previously unseen `g<m` occur, strictly
  decreasing the missing-level budget;
* a forced addition followed by subtraction lowers the ordinary parent value;
* or the second subtraction is blocked and its concrete candidate already
  gives a `CoverageStep` for the original parent.

Thus the history-aware lexicographic rank always decreases unless coverage is
already obtained. -/
theorem qOne_historyBudgetProgress_or_coverage
    {m n r g : Nat}
    (hm : m ≤ n + 1)
    (hg : 3 ≤ g)
    (hgm : g < m)
    (hcoord : CoordinatesAt n 1 r)
    (hpotential : potential 1 r = Int.ofNat g) :
    CoverageStep m (a n) n ∨
      ∃ t k s,
        n < t ∧ t ≤ n + 2 ∧
        CoordinatesAt t k s ∧
        (potential k s = Int.ofNat (g - 1) ∨
          potential k s = Int.ofNat (g - 3)) ∧
        HistoryBudgetProgress m
          ⟨a t, t⟩ ⟨a n, n⟩ := by
  have hr : r = 1 + g := by
    simpa [upperTri] using
      (potential_eq_ofNat_iff 1 r g).mp hpotential
  have hregular : 1 ≤ r := by omega
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · have hsub := coordinates_sub_regular hcoord (by omega) hregular hcan
    have hzeroCoord : CoordinatesAt (n + 1) 0 g := by
      have : r - 1 = g := by omega
      simpa [this] using hsub.1
    have hfirstG : FirstAt a g (n + 1) := by
      have hfirst := firstAt_succ_of_canSubtract hcan
      have hvalue := a_succ_of_canSubtract hcan
      have hcand : a n - (n + 1) = g := by
        have heq := hcoord.eqn
        omega
      have : a (n + 1) = g := by omega
      simpa [this] using hfirst
    rcases coordinates_zeroQuotient_next hzeroCoord with
      ⟨_, hnext, hdrop⟩
    have hbudgetAtNext :
        missingBelowCount m (n + 1) < missingBelowCount m n :=
      missingBelowCount_strict_of_firstAt hgm (by omega) hfirstG
    have hbudgetLater :
        missingBelowCount m (n + 2) < missingBelowCount m n := by
      have hmono := missingBelowCount_antitone
        (m := m) (n := n + 1) (t := n + 2) (by omega)
      omega
    have hprogress : HistoryBudgetProgress m
        ⟨a (n + 2), n + 2⟩ ⟨a n, n⟩ :=
      historyBudgetProgress_of_budgetDrop hbudgetLater
    have hlevel : potential 1 g = Int.ofNat (g - 1) := by
      simp [potential, upperTri]
      have hgpos : 0 < g := by omega
      omega
    exact Or.inr
      ⟨n + 2, 1, g, by omega, by omega,
        by simpa [Nat.add_assoc] using hnext, Or.inl hlevel, hprogress⟩
  · have hadd := coordinates_add_regular hcoord hregular hcan
    have hqTwoCoord : CoordinatesAt (n + 1) 2 g := by
      have : r - 1 = g := by omega
      simpa [this] using hadd.1
    have hqTwoLevel : potential 2 g = Int.ofNat (g - 3) := by
      simp [potential, upperTri]
      omega
    have hqTwoRegular : 2 ≤ g := by omega
    by_cases hcanTwo : CanSubtract (n + 2) (stateAt (n + 1))
    · have hsub := coordinates_sub_regular
        hqTwoCoord (by omega) hqTwoRegular hcanTwo
      have hnextCoord : CoordinatesAt (n + 2) 1 (g - 2) := by
        simpa [Nat.add_assoc] using hsub.1
      have hnextLevel : potential 1 (g - 2) = Int.ofNat (g - 3) := by
        simp [potential, upperTri]
        omega
      have hexactValueDrop := a_add_then_sub_eq_pred hcan hcanTwo
      have hvalueDrop : a (n + 2) < a n := by
        omega
      have hprogress : HistoryBudgetProgress m
          ⟨a (n + 2), n + 2⟩ ⟨a n, n⟩ :=
        historyBudgetProgress_of_valueDrop (by omega) hvalueDrop
      exact Or.inr
        ⟨n + 2, 1, g - 2, by omega, by omega,
          hnextCoord, Or.inr hnextLevel, hprogress⟩
    · have haddValue := a_succ_of_not_canSubtract hcan
      let y := a n - 1
      have heq := hcoord.eqn
      have hpositive : n + 2 < a (n + 1) := by
        omega
      have hcandidate : a (n + 1) - (n + 2) = y := by
        simp only [y]
        omega
      have hseen : y ∈ valuesThrough (n + 1) := by
        by_cases hySeen : y ∈ valuesThrough (n + 1)
        · exact hySeen
        · have hcan' : CanSubtract (n + 2) (stateAt (n + 1)) := by
            constructor
            · simpa [a] using hpositive
            · change a (n + 1) - (n + 2) ∉ valuesThrough (n + 1)
              rw [hcandidate]
              exact hySeen
          exact False.elim (hcanTwo hcan')
      rcases history_member_has_firstAt hseen with ⟨fy, _, hfirstY⟩
      have hmy : m ≤ y := by
        simp only [y]
        omega
      have hylt : y < a n := by
        simp only [y]
        omega
      exact Or.inl (Or.inr ⟨y, fy, hmy, hfirstY, hylt⟩)

/-- Parent-parametric form of the quotient-one frontier.  It shows that the
local theorem fits the three-component search rank without changing the
active first-occurrence parent. -/
theorem qOne_historySearchProgress_or_coverage
    {m activeParent n r g : Nat}
    (hm : m ≤ n + 1)
    (hg : 3 ≤ g)
    (hgm : g < m)
    (hcoord : CoordinatesAt n 1 r)
    (hpotential : potential 1 r = Int.ofNat g) :
    CoverageStep m (a n) n ∨
      ∃ t k s,
        n < t ∧ t ≤ n + 2 ∧
        CoordinatesAt t k s ∧
        (potential k s = Int.ofNat (g - 1) ∨
          potential k s = Int.ofNat (g - 3)) ∧
        HistorySearchProgress m
          ⟨t, activeParent, a t⟩
          ⟨n, activeParent, a n⟩ := by
  rcases qOne_historyBudgetProgress_or_coverage
      hm hg hgm hcoord hpotential with hcoverage |
        ⟨t, k, s, hnt, htbound, htcoord, htlevel, htprogress⟩
  · exact Or.inl hcoverage
  · exact Or.inr ⟨t, k, s, hnt, htbound, htcoord, htlevel,
      htprogress.toHistorySearchProgress activeParent⟩

/-- A `CoverageStep` is compatible with the history-search rank when the
forward history horizon is held fixed: either the target already occurs, or
the active parent component strictly decreases.  The first-occurrence time
of the blocker is retained as evidence but is deliberately not used as the
history horizon. -/
theorem coverageStep_occurs_or_historySearchParentProgress
    {m v f horizon orbitValue : Nat}
    (hstep : CoverageStep m v f) :
    (∃ t, a t = m) ∨
      ∃ y fy,
        m ≤ y ∧ FirstAt a y fy ∧ y < v ∧
        HistorySearchProgress m
          ⟨horizon, y, orbitValue⟩
          ⟨horizon, v, orbitValue⟩ := by
  rcases hstep with hoccurs | ⟨y, fy, hmy, hfirstY, hyv⟩
  · exact Or.inl hoccurs
  · exact Or.inr ⟨y, fy, hmy, hfirstY, hyv,
      historySearchProgress_of_parentDrop (Nat.le_refl _) hyv⟩

/-- One-step repayment law for a forced addition.  If the next subtraction is
legal, the orbit value becomes exactly one smaller than the pre-addition
value.  If it is blocked, the candidate `a n - 1` is already in the forward
history and lowers the active parent.  Thus whenever that candidate is at
least the target, the three-component rank strictly decreases in either
branch. -/
theorem forcedAddition_followup_historySearchProgress
    {m activeParent n : Nat}
    (hm : 0 < m)
    (hbound : a n ≤ activeParent)
    (hcandidateLower : m ≤ a n - 1)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    (∃ y fy,
      y = a n - 1 ∧ m ≤ y ∧ FirstAt a y fy ∧
      y < activeParent ∧
      HistorySearchProgress m
        ⟨n + 2, y, a (n + 2)⟩
        ⟨n, activeParent, a n⟩) ∨
    HistorySearchProgress m
      ⟨n + 2, activeParent, a (n + 2)⟩
      ⟨n, activeParent, a n⟩ := by
  by_cases hcanNext : CanSubtract (n + 2) (stateAt (n + 1))
  · have hexact := a_add_then_sub_eq_pred hnot hcanNext
    have hdrop : a (n + 2) < a n := by omega
    exact Or.inr
      (historySearchProgress_of_orbitValueDrop (by omega) hdrop)
  · have haddValue := a_succ_of_not_canSubtract hnot
    let y := a n - 1
    have hy : y = a n - 1 := rfl
    have hmy : m ≤ y := by simpa only [y] using hcandidateLower
    have hapos : 1 < a n := by omega
    have hpositive : n + 2 < a (n + 1) := by omega
    have hcandidate : a (n + 1) - (n + 2) = y := by
      simp only [y]
      omega
    have hseen : y ∈ valuesThrough (n + 1) := by
      by_cases hySeen : y ∈ valuesThrough (n + 1)
      · exact hySeen
      · have hcan' : CanSubtract (n + 2) (stateAt (n + 1)) := by
          constructor
          · simpa [a] using hpositive
          · change a (n + 1) - (n + 2) ∉ valuesThrough (n + 1)
            rw [hcandidate]
            exact hySeen
        exact False.elim (hcanNext hcan')
    rcases history_member_has_firstAt hseen with ⟨fy, _, hfirstY⟩
    have hyCurrent : y < a n := by
      simp only [y]
      omega
    have hyParent : y < activeParent :=
      Nat.lt_of_lt_of_le hyCurrent hbound
    exact Or.inl ⟨y, fy, hy, hmy, hfirstY, hyParent,
      historySearchProgress_of_parentDrop (by omega) hyParent⟩

/-- At quotient at least two, the actual-orbit quotient bound makes the
blocked candidate `a n - 1` large enough for every target `m ≤ n+1`. -/
theorem CoordinatesAt.target_le_pred_of_two_le_quotient
    {m n q r : Nat}
    (hm : m ≤ n + 1)
    (hcoord : CoordinatesAt n q r)
    (hq : 2 ≤ q) :
    m ≤ a n - 1 := by
  have hquotientBound := hcoord.twice_quotient_le
  have heq := hcoord.eqn
  have hn : 3 ≤ n := by omega
  have hmul : n * 2 ≤ n * q := Nat.mul_le_mul_left n hq
  omega

/-- Therefore every forced addition from quotient at least two, while the
current value is still below the active parent, is discharged after at most
one more actual step by the history-search rank. -/
theorem coordinates_forcedAddition_twoQuotient_historySearchProgress
    {m activeParent n q r : Nat}
    (hmpos : 0 < m)
    (hm : m ≤ n + 1)
    (hbound : a n ≤ activeParent)
    (hcoord : CoordinatesAt n q r)
    (hq : 2 ≤ q)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    (∃ y fy,
      y = a n - 1 ∧ m ≤ y ∧ FirstAt a y fy ∧
      y < activeParent ∧
      HistorySearchProgress m
        ⟨n + 2, y, a (n + 2)⟩
        ⟨n, activeParent, a n⟩) ∨
    HistorySearchProgress m
      ⟨n + 2, activeParent, a (n + 2)⟩
      ⟨n, activeParent, a n⟩ := by
  exact forcedAddition_followup_historySearchProgress
    hmpos hbound
      (hcoord.target_le_pred_of_two_le_quotient hm hq) hnot

/-- Complete rank interpretation of the quotient-one frontier, under the
single transport condition that the explored orbit value has not exceeded
the active parent.  Every branch then either witnesses the target or strictly
decreases one of the three search-rank components. -/
theorem qOne_historySearchOutcome
    {m activeParent n r g : Nat}
    (hbound : a n ≤ activeParent)
    (hm : m ≤ n + 1)
    (hg : 3 ≤ g)
    (hgm : g < m)
    (hcoord : CoordinatesAt n 1 r)
    (hpotential : potential 1 r = Int.ofNat g) :
    (∃ u, a u = m) ∨
      (∃ y fy,
        m ≤ y ∧ FirstAt a y fy ∧ y < activeParent ∧
        HistorySearchProgress m
          ⟨n, y, a n⟩
          ⟨n, activeParent, a n⟩) ∨
      ∃ t k s,
        n < t ∧ t ≤ n + 2 ∧
        CoordinatesAt t k s ∧
        (potential k s = Int.ofNat (g - 1) ∨
          potential k s = Int.ofNat (g - 3)) ∧
        HistorySearchProgress m
          ⟨t, activeParent, a t⟩
          ⟨n, activeParent, a n⟩ := by
  rcases qOne_historySearchProgress_or_coverage
      (activeParent := activeParent) hm hg hgm hcoord hpotential with
    hcoverage | ⟨t, k, s, hnt, htbound, htcoord, htlevel, htprogress⟩
  · rcases hcoverage with hoccurs | ⟨y, fy, hmy, hfirstY, hyCurrent⟩
    · exact Or.inl hoccurs
    · have hyParent : y < activeParent :=
        Nat.lt_of_lt_of_le hyCurrent hbound
      exact Or.inr (Or.inl ⟨y, fy, hmy, hfirstY, hyParent,
        historySearchProgress_of_parentDrop (Nat.le_refl _) hyParent⟩)
  · exact Or.inr (Or.inr
      ⟨t, k, s, hnt, htbound, htcoord, htlevel, htprogress⟩)

/-- The history-aware frontier for an arbitrary nonnegative epoch on a level
`3 ≤ g < m`.  A regular subtraction prefix can only lower the parent value.
At its low-quotient endpoint, either:

* coverage has already been obtained;
* the original state itself had quotient zero (the one exceptional boundary
  which must be charged to the preceding negative epoch); or
* a later actual state has strictly smaller history-budget rank.

The endpoint potential is recorded explicitly: it is unchanged when the
prefix itself supplies progress, and is `g-1` or `g-3` after the quotient-one
cleanup. -/
theorem nonnegative_epoch_historyFrontier
    {m n q r g : Nat}
    (hm : m ≤ n + 1)
    (hg : 3 ≤ g)
    (hgm : g < m)
    (hcoord : CoordinatesAt n q r)
    (hpotential : potential q r = Int.ofNat g) :
    CoverageStep m (a n) n ∨ q = 0 ∨
      ∃ t k s,
        n < t ∧ t ≤ n + q + 2 ∧
        CoordinatesAt t k s ∧
        (potential k s = Int.ofNat g ∨
          potential k s = Int.ofNat (g - 1) ∨
          potential k s = Int.ofNat (g - 3)) ∧
        HistoryBudgetProgress m
          ⟨a t, t⟩ ⟨a n, n⟩ := by
  have hnonnegative : 0 ≤ potential q r := by
    rw [hpotential]
    exact Int.natCast_nonneg g
  rcases nonnegative_epoch_lowQuotient_or_coverage_with_value
      hm hcoord hnonnegative with
    ⟨u, p, v, hnu, hubound, huvalue, hfront, hsame,
      hucoord, hupotential, hresult⟩
  rcases hresult with hplow | hcoverage
  · have hlevel : potential p v = Int.ofNat g := by
      rw [hupotential, hpotential]
    have hpCases : p = 0 ∨ p = 1 := by omega
    rcases hpCases with hpzero | hpone
    · subst p
      rcases hfront with hueq | huDrop
      · have hqzero : q = 0 := by
          have := hsame hueq
          omega
        exact Or.inr (Or.inl hqzero)
      · have hprogress : HistoryBudgetProgress m
            ⟨a u, u⟩ ⟨a n, n⟩ :=
          historyBudgetProgress_of_valueDrop hnu huDrop
        have hnuStrict : n < u := by
          rcases Nat.eq_or_lt_of_le hnu with hueq | hlt
          · subst u
            exact False.elim (Nat.lt_irrefl _ huDrop)
          · exact hlt
        exact Or.inr (Or.inr
          ⟨u, 0, v, hnuStrict, by omega, hucoord,
            Or.inl hlevel, hprogress⟩)
    · subst p
      have hmAtU : m ≤ u + 1 := by omega
      rcases qOne_historyBudgetProgress_or_coverage
          hmAtU hg hgm hucoord hlevel with huCoverage |
            ⟨t, k, s, hut, htbound, htcoord, htlevel, htprogress⟩
      · rcases hfront with hueq | huDrop
        · subst u
          exact Or.inl (by simpa using huCoverage)
        · exact Or.inl (huCoverage.mono_parent huDrop)
      · have hprogress : HistoryBudgetProgress m
            ⟨a t, t⟩ ⟨a n, n⟩ := by
          rcases hfront with hueq | huDrop
          · subst u
            simpa using htprogress
          · exact htprogress.trans
              (historyBudgetProgress_of_valueDrop hnu huDrop)
        exact Or.inr (Or.inr
          ⟨t, k, s, by omega, by omega, htcoord,
            Or.inr htlevel, hprogress⟩)
  · exact Or.inl hcoverage

/-- Full nonnegative-epoch interpretation in the three-component search
rank.  Provided the epoch starts below the active parent, every branch is a
target witness, a blocker parent descent, the quotient-zero entry boundary,
or a strict forward search step. -/
theorem nonnegative_epoch_historySearchOutcome
    {m activeParent n q r g : Nat}
    (hbound : a n ≤ activeParent)
    (hm : m ≤ n + 1)
    (hg : 3 ≤ g)
    (hgm : g < m)
    (hcoord : CoordinatesAt n q r)
    (hpotential : potential q r = Int.ofNat g) :
    (∃ u, a u = m) ∨
      (∃ y fy,
        m ≤ y ∧ FirstAt a y fy ∧ y < activeParent ∧
        HistorySearchProgress m
          ⟨n, y, a n⟩
          ⟨n, activeParent, a n⟩) ∨
      q = 0 ∨
      ∃ t k s,
        n < t ∧ t ≤ n + q + 2 ∧
        CoordinatesAt t k s ∧
        (potential k s = Int.ofNat g ∨
          potential k s = Int.ofNat (g - 1) ∨
          potential k s = Int.ofNat (g - 3)) ∧
        HistorySearchProgress m
          ⟨t, activeParent, a t⟩
          ⟨n, activeParent, a n⟩ := by
  rcases nonnegative_epoch_historyFrontier
      hm hg hgm hcoord hpotential with hcoverage | hrest
  · rcases hcoverage with hoccurs | ⟨y, fy, hmy, hfirstY, hyCurrent⟩
    · exact Or.inl hoccurs
    · have hyParent : y < activeParent :=
        Nat.lt_of_lt_of_le hyCurrent hbound
      exact Or.inr (Or.inl ⟨y, fy, hmy, hfirstY, hyParent,
        historySearchProgress_of_parentDrop (Nat.le_refl _) hyParent⟩)
  · rcases hrest with hqzero |
        ⟨t, k, s, hnt, htbound, htcoord, htlevel, htprogress⟩
    · exact Or.inr (Or.inr (Or.inl hqzero))
    · exact Or.inr (Or.inr (Or.inr
        ⟨t, k, s, hnt, htbound, htcoord, htlevel,
          htprogress.toHistorySearchProgress activeParent⟩))

/-- History-rank frontier for a complete negative epoch.  All legal
zero-borrow prefix steps preserve the bound by the active parent.  The final
one-borrow transition then has three resolved forms:

* legal subtraction lowers the orbit component;
* a forced addition from quotient at least two is repaid or blocked within
  one further step;
* an already constructed `CoverageStep` witnesses the target or lowers the
  active parent component.

The only branch deliberately left outside the rank is a forced one-borrow
addition from pre-state quotient exactly one.  This is now the explicit
low-quotient debt chamber for the next epoch. -/
theorem negative_epoch_historySearchOutcome_or_qOneDebt
    {m activeParent n q r : Nat}
    (hmpos : 0 < m)
    (hm : m ≤ n + 1)
    (hbound : a n ≤ activeParent)
    (hcoord : CoordinatesAt n q r)
    (hnegative : potential q r < 0) :
    (∃ u, a u = m) ∨
      (∃ horizon y fy,
        m ≤ y ∧ FirstAt a y fy ∧ y < activeParent ∧
        HistorySearchProgress m
          ⟨horizon, y, a horizon⟩
          ⟨n, activeParent, a n⟩) ∨
      (∃ u p v,
        n < u ∧ CoordinatesAt u p v ∧
        HistorySearchProgress m
          ⟨u, activeParent, a u⟩
          ⟨n, activeParent, a n⟩) ∨
      ∃ t r' s,
        n ≤ t ∧ a t ≤ a n ∧
        CoordinatesAt t 1 r' ∧ BorrowData t 1 r' 1 s ∧
        ¬ CanSubtract (t + 1) (stateAt t) ∧
        CoordinatesAt (t + 1) 1 s ∧
        0 ≤ potential 1 s ∧ potential 1 s < Int.ofNat m := by
  rcases negative_epoch_undershoot_or_coverage_with_value
      hm hcoord hnegative with
    ⟨t, q', r', b, s, k, hnt, _, htvalue, htfront,
      htcoord, htborrow, hkcoord, hfrontier⟩
  rcases hfrontier with
      ⟨hb, hnonnegative, hbelow, hbranch⟩ | hcoverage
  · have hboundAt : a t ≤ activeParent :=
      Nat.le_trans htvalue hbound
    have liftProgress : ∀ {child : HistorySearchNode},
        HistorySearchProgress m child
            ⟨t, activeParent, a t⟩ →
          HistorySearchProgress m child
            ⟨n, activeParent, a n⟩ := by
      intro child hprogress
      rcases htfront with hteq | htvalueDrop
      · subst t
        simpa using hprogress
      · exact hprogress.trans
          (historySearchProgress_of_orbitValueDrop hnt htvalueDrop)
    rcases hbranch with ⟨hcan, _⟩ | ⟨hnot, hk⟩
    · have hstep := a_succ_of_canSubtract hcan
      have hpositive : t + 1 < a t := by
        simpa [a] using hcan.1
      have horbitDrop : a (t + 1) < a t := by omega
      have hprogress : HistorySearchProgress m
          ⟨t + 1, activeParent, a (t + 1)⟩
          ⟨t, activeParent, a t⟩ :=
        historySearchProgress_of_orbitValueDrop (by omega) horbitDrop
      exact Or.inr (Or.inr (Or.inl
        ⟨t + 1, k, s, by omega, hkcoord,
          liftProgress hprogress⟩))
    · have hqpos : 0 < q' := by
        have hchamber := htborrow.eq_one_iff.mp hb
        omega
      by_cases hqone : q' = 1
      · subst q'
        have hkone : k = 1 := by omega
        subst k
        subst b
        exact Or.inr (Or.inr (Or.inr
          ⟨t, r', s, hnt, htvalue, htcoord, htborrow,
            hnot, hkcoord, hnonnegative, hbelow⟩))
      · have hqtwo : 2 ≤ q' := by omega
        have hmAtT : m ≤ t + 1 := by omega
        rcases coordinates_forcedAddition_twoQuotient_historySearchProgress
            hmpos hmAtT hboundAt htcoord hqtwo hnot with
          ⟨y, fy, _, hmy, hfirstY, hyParent, hprogress⟩ |
            hprogress
        · exact Or.inr (Or.inl
            ⟨t + 2, y, fy, hmy, hfirstY, hyParent,
              liftProgress hprogress⟩)
        · rcases exists_coordinatesAt (n := t + 2) (by omega) with
            ⟨p, v, hchildCoord⟩
          exact Or.inr (Or.inr (Or.inl
            ⟨t + 2, p, v, by omega, hchildCoord,
              liftProgress hprogress⟩))
  · rcases hcoverage with hoccurs |
        ⟨y, fy, hmy, hfirstY, hyCurrent⟩
    · exact Or.inl hoccurs
    · have hyParent : y < activeParent :=
        Nat.lt_of_lt_of_le hyCurrent hbound
      exact Or.inr (Or.inl
        ⟨n, y, fy, hmy, hfirstY, hyParent,
          historySearchProgress_of_parentDrop
            (Nat.le_refl _) hyParent⟩)

/-- The remaining quotient-one debt chamber has rigid arithmetic.  Its
pre-state is `a t=t`, its landing level is `t-1`, and the target bounds force
either `m=t` (already witnessed) or the single diagonal-successor obligation
`m=t+1` with the original epoch starting at the same time. -/
theorem qOneDebt_target_or_diagonalSuccessor
    {m n t r s : Nat}
    (hm : m ≤ n + 1)
    (hnt : n ≤ t)
    (hcoord : CoordinatesAt t 1 r)
    (hborrow : BorrowData t 1 r 1 s)
    (hnonnegative : 0 ≤ potential 1 s)
    (hbelow : potential 1 s < Int.ofNat m) :
    (∃ u, a u = m) ∨
      (n = t ∧ m = t + 1 ∧ a t = t) := by
  have hchamber := hborrow.eq_one_iff.mp rfl
  have hrzero : r = 0 := by omega
  have hbalance := hborrow.balance
  have hs : s = t := by omega
  have hvalue : a t = t := by
    have heq := hcoord.eqn
    omega
  subst r
  subst s
  have htpos : 0 < t := by
    have hrlt := hcoord.remainder_lt
    omega
  have htargetLower : t ≤ m := by
    simp [potential, upperTri] at hbelow
    omega
  have htargetUpper : m ≤ t + 1 := by omega
  have hcases : m = t ∨ m = t + 1 := by omega
  rcases hcases with hmt | hmnext
  · exact Or.inl ⟨t, by simpa [hmt] using hvalue⟩
  · have hntEq : n = t := by omega
    exact Or.inr ⟨hntEq, hmnext, hvalue⟩

/-- The isolated remaining history statement: every positive diagonal state
`a t=t` has its successor value somewhere on the actual orbit. -/
def DiagonalSuccessorProperty : Prop :=
  ∀ t, 0 < t → a t = t → ∃ u, a u = t + 1

/-- Assuming only the diagonal-successor property, the exceptional debt
branch disappears and every negative epoch strictly advances the
history-search proof or witnesses the target. -/
theorem negative_epoch_historySearchOutcome
    (hdiagonal : DiagonalSuccessorProperty)
    {m activeParent n q r : Nat}
    (hmpos : 0 < m)
    (hm : m ≤ n + 1)
    (hbound : a n ≤ activeParent)
    (hcoord : CoordinatesAt n q r)
    (hnegative : potential q r < 0) :
    (∃ u, a u = m) ∨
      (∃ horizon y fy,
        m ≤ y ∧ FirstAt a y fy ∧ y < activeParent ∧
        HistorySearchProgress m
          ⟨horizon, y, a horizon⟩
          ⟨n, activeParent, a n⟩) ∨
      ∃ u p v,
        n < u ∧ CoordinatesAt u p v ∧
        HistorySearchProgress m
          ⟨u, activeParent, a u⟩
          ⟨n, activeParent, a n⟩ := by
  rcases negative_epoch_historySearchOutcome_or_qOneDebt
      hmpos hm hbound hcoord hnegative with
    hoccurs | hparent | horbit |
      ⟨t, r', s, hnt, _, htcoord, htborrow, _, _,
        hnonnegative, hbelow⟩
  · exact Or.inl hoccurs
  · exact Or.inr (Or.inl hparent)
  · exact Or.inr (Or.inr horbit)
  · rcases qOneDebt_target_or_diagonalSuccessor
        hm hnt htcoord htborrow hnonnegative hbelow with
      hoccurs | ⟨_, hmnext, hvalue⟩
    · exact Or.inl hoccurs
    · have htpos : 0 < t := by
        have hrlt := htcoord.remainder_lt
        omega
      have hsuccessor := hdiagonal t htpos hvalue
      exact Or.inl (by simpa [hmnext] using hsuccessor)

end Recaman
