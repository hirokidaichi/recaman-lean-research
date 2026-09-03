import Recaman.PopupLock

namespace Recaman

/-! # Residue law and the lock budget

Write `a n = q * n + r` with `r < n`: `q = a n / n` is the *level* and `r = a n % n` the
*residue* of the orbit at clock `n`.  Both Recamán steps send `(q, r)` to `(q ± 1, r - q)`
as long as `q ≤ r`; when `r < q` the residue jumps up to `r + (n + 1) - q`, whatever the
step is.  Chaffin's arcs are the maximal stretches of clocks along which the residue never
increases, so the residue budget decides where an arc ends.

Applied to the level-3/4 lock of `PopupLock`: the upper clock `m` of a lock pair
(`a m = 3 m + t`) has level 4 and residue `t - m`, the lower clock has level 3 and residue
`t - m - 4`, and the next upper clock has residue `t - m - 7`.  A pair keeps the residue law
iff `m + 7 ≤ t`; when `t < m + 7` the residue increases inside the pair.  In the comb-end
coordinates of `popup_lock_entry` (`m = i + 5`, `t = i + v - 1`, landing of `v` at clock
`i + 1`) the budget of pair `k` reads `13 + 7 k ≤ v`: the lock loses seven units of residue
per pair and the arc ends inside the first pair `K` with `v < 13 + 7 K`.

Finally, the level-two candidates presented during the lock are the orbit's own
pre-landing values (`prelanding_upper_values`): with a pre-landing run of `J` pairs the
candidates of the pairs `k` with `3 k + 1 ≤ J` are visited, so the lock cannot break before
pair `(J + 2) / 3`.

Everything here is arithmetic on top of the step recurrence and the lock lemmas.  No
target, cutoff, or reachability hypothesis is used.
-/

/-- Quotient of an explicit decomposition `x = q * n + r` with `r < n`. -/
theorem div_eq_of_decomp {x n q r : Nat} (hx : x = q * n + r) (hr : r < n) :
    x / n = q := by
  have hn : 0 < n := by omega
  have h : x = r + n * q := by rw [hx, Nat.mul_comm, Nat.add_comm]
  rw [h, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, Nat.zero_add]

/-- Remainder of an explicit decomposition `x = q * n + r` with `r < n`. -/
theorem mod_eq_of_decomp {x n q r : Nat} (hx : x = q * n + r) (hr : r < n) :
    x % n = r := by
  have h : x = r + n * q := by rw [hx, Nat.mul_comm, Nat.add_comm]
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- Residue law, addition: with `a n = q * n + r`, `r < n` and `q ≤ r`, an addition
raises the level by one and lowers the residue by the level. -/
theorem residue_add {n q r : Nat} (hval : a n = q * n + r) (hr : r < n) (hqr : q ≤ r)
    (hstep : a (n + 1) = a n + (n + 1)) :
    a (n + 1) = (q + 1) * (n + 1) + (r - q) ∧
      a (n + 1) / (n + 1) = q + 1 ∧ a (n + 1) % (n + 1) = r - q := by
  have hexp : (q + 1) * (n + 1) = q * n + q + (n + 1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  have hdec : a (n + 1) = (q + 1) * (n + 1) + (r - q) := by omega
  have hlt : r - q < n + 1 := by omega
  exact ⟨hdec, div_eq_of_decomp hdec hlt, mod_eq_of_decomp hdec hlt⟩

/-- Residue law, subtraction: with `a n = (q + 1) * n + r`, `r < n` and `q + 1 ≤ r`, a
subtraction lowers the level by one and lowers the residue by the level. -/
theorem residue_sub {n q r : Nat} (hval : a n = (q + 1) * n + r) (hr : r < n)
    (hqr : q + 1 ≤ r) (hstep : a (n + 1) = a n - (n + 1)) :
    a (n + 1) = q * (n + 1) + (r - (q + 1)) ∧
      a (n + 1) / (n + 1) = q ∧ a (n + 1) % (n + 1) = r - (q + 1) := by
  have hexp1 : (q + 1) * n = q * n + n := by rw [Nat.add_mul, Nat.one_mul]
  have hexp2 : q * (n + 1) = q * n + q := by rw [Nat.mul_add, Nat.mul_one]
  have hdec : a (n + 1) = q * (n + 1) + (r - (q + 1)) := by omega
  have hlt : r - (q + 1) < n + 1 := by omega
  exact ⟨hdec, div_eq_of_decomp hdec hlt, mod_eq_of_decomp hdec hlt⟩

/-- Residue wrap: when the residue is below the level (`r < q ≤ n`), the next residue is
`r + (n + 1) - q`, larger than `r`, whatever the step is.  This is the event that ends a
Chaffin arc. -/
theorem residue_wrap {n q r : Nat} (hval : a n = q * n + r) (hr : r < n) (hrq : r < q)
    (hqn : q ≤ n) :
    a (n + 1) % (n + 1) = r + (n + 1) - q ∧ a n % n < a (n + 1) % (n + 1) := by
  have hmod : a n % n = r := mod_eq_of_decomp hval hr
  have hrec := recurrence n
  by_cases hcan : CanSubtract (n + 1) (stateAt n)
  · rw [if_pos hcan] at hrec
    have hlt : n + 1 < a n := hcan.1
    have h2 : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with hq | hq
      · exfalso
        have hle : q * n ≤ 1 * n := Nat.mul_le_mul_right n (by omega)
        rw [Nat.one_mul] at hle
        omega
      · exact hq
    obtain ⟨p, hp⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    subst hp
    have hexp1 : (p + 2) * n = p * n + 2 * n := Nat.add_mul p 2 n
    have hexp2 : p * (n + 1) = p * n + p := by rw [Nat.mul_add, Nat.mul_one]
    have hdec : a (n + 1) = p * (n + 1) + (r + (n + 1) - (p + 2)) := by omega
    have hlt' : r + (n + 1) - (p + 2) < n + 1 := by omega
    have hmod' := mod_eq_of_decomp hdec hlt'
    refine ⟨hmod', ?_⟩
    rw [hmod, hmod']
    omega
  · rw [if_neg hcan] at hrec
    have hexp : q * (n + 1) = q * n + q := by rw [Nat.mul_add, Nat.mul_one]
    have hdec : a (n + 1) = q * (n + 1) + (r + (n + 1) - q) := by omega
    have hlt' : r + (n + 1) - q < n + 1 := by omega
    have hmod' := mod_eq_of_decomp hdec hlt'
    refine ⟨hmod', ?_⟩
    rw [hmod, hmod']
    omega

/-- The lower clock of a lock pair: from `a m = 3 m + t` with the level-three value
`2 m + t - 1` fresh, the orbit lands it: `a (m + 1) = 2 m + t - 1`. -/
theorem level34_lower {m t : Nat} (hval : a m = 3 * m + t) (ht : 3 ≤ t)
    (hfresh : 2 * m + t - 1 ∉ valuesThrough m) : a (m + 1) = 2 * m + t - 1 := by
  have hrec := recurrence m
  have hcan : CanSubtract (m + 1) (stateAt m) := by
    refine ⟨?_, ?_⟩
    · show m + 1 < a m
      omega
    · have hcand : (stateAt m).value - (m + 1) = 2 * m + t - 1 := by
        show a m - (m + 1) = 2 * m + t - 1
        omega
      rw [hcand]
      exact hfresh
  rw [if_pos hcan] at hrec
  omega

/-- Residues along one lock pair when the budget allows (`m + 7 ≤ t`): level 4 with
residue `t - m` at `m`, level 3 with residue `t - m - 4` at `m + 1`, level 4 with residue
`t - m - 7` at `m + 2`.  The residue drops by seven per pair. -/
theorem level34_pair_residues {m t : Nat} (hval : a m = 3 * m + t) (ht2 : t < 2 * m)
    (hfresh : 2 * m + t - 1 ∉ valuesThrough m)
    (hblocked : m + t - 3 ∈ valuesThrough (m + 1)) (hbudget : m + 7 ≤ t) :
    a m / m = 4 ∧ a m % m = t - m ∧
      a (m + 1) / (m + 1) = 3 ∧ a (m + 1) % (m + 1) = t - m - 4 ∧
      a (m + 2) / (m + 2) = 4 ∧ a (m + 2) % (m + 2) = t - m - 7 := by
  have hpair := level34_pair hval (by omega) hfresh hblocked
  have h0 : a m = 4 * m + (t - m) := by omega
  have h0lt : t - m < m := by omega
  have h1 : a (m + 1) = 3 * (m + 1) + (t - m - 4) := by omega
  have h1lt : t - m - 4 < m + 1 := by omega
  have h2 : a (m + 2) = 4 * (m + 2) + (t - m - 7) := by omega
  have h2lt : t - m - 7 < m + 2 := by omega
  exact ⟨div_eq_of_decomp h0 h0lt, mod_eq_of_decomp h0 h0lt,
    div_eq_of_decomp h1 h1lt, mod_eq_of_decomp h1 h1lt,
    div_eq_of_decomp h2 h2lt, mod_eq_of_decomp h2 h2lt⟩

/-- Budget failure inside a lock pair (`m ≤ t < m + 7`): the residue increases either at
the lower clock (`t < m + 4`, whatever the step) or at the clock after it
(`m + 4 ≤ t < m + 7`, again whatever the step). -/
theorem level34_pair_wrap {m t : Nat} (hval : a m = 3 * m + t) (hm : 4 ≤ m)
    (hmt : m ≤ t) (ht2 : t < 2 * m)
    (hfresh : 2 * m + t - 1 ∉ valuesThrough m) (hbudget : t < m + 7) :
    a m % m < a (m + 1) % (m + 1) ∨ a (m + 1) % (m + 1) < a (m + 2) % (m + 2) := by
  rcases Nat.lt_or_ge t (m + 4) with hlow | hhigh
  · left
    have h0 : a m = 4 * m + (t - m) := by omega
    exact (residue_wrap h0 (by omega) (by omega) hm).2
  · right
    have hlower := level34_lower hval (by omega) hfresh
    have h1 : a (m + 1) = 3 * (m + 1) + (t - m - 4) := by omega
    have hw := (residue_wrap h1 (by omega) (by omega) (by omega)).2
    rw [show m + 1 + 1 = m + 2 by omega] at hw
    exact hw

/-- Lock residues in comb-end coordinates.  After the lock entry
`a (i + 5) = 4 i + v + 14` of the isolated late landing of `v` at clock `i + 1`, as long as
the lock hypotheses hold for the pairs below `K` and the budget `13 + 7 K ≤ v` holds, pair
`k ≤ K` starts at level 4 with residue `v - 6 - 7 k`, and for `k < K` its lower clock has
level 3 with residue `v - 10 - 7 k`. -/
theorem popup_lock_residues {i v K : Nat} (hentry : a (i + 5) = 4 * i + v + 14)
    (hle : v ≤ i) (hbudget : 13 + 7 * K ≤ v)
    (hfresh : ∀ k, k < K →
      2 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 1 ∉ valuesThrough (i + 5 + 2 * k))
    (hblocked : ∀ k, k < K →
      (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 3 ∈ valuesThrough (i + 5 + 2 * k + 1)) :
    ∀ k, k ≤ K →
      a (i + 5 + 2 * k) / (i + 5 + 2 * k) = 4 ∧
      a (i + 5 + 2 * k) % (i + 5 + 2 * k) = v - 6 - 7 * k ∧
      (k < K → a (i + 5 + 2 * k + 1) / (i + 5 + 2 * k + 1) = 3 ∧
        a (i + 5 + 2 * k + 1) % (i + 5 + 2 * k + 1) = v - 10 - 7 * k) := by
  intro k hk
  have hval : a (i + 5) = 3 * (i + 5) + (i + v - 1) := by omega
  have hK : 5 * K + 3 ≤ i + v - 1 := by omega
  have hlock := level34_lock hval K hK hfresh hblocked
  have hup := hlock k hk
  have h0 : a (i + 5 + 2 * k) = 4 * (i + 5 + 2 * k) + (v - 6 - 7 * k) := by omega
  have h0lt : v - 6 - 7 * k < i + 5 + 2 * k := by omega
  refine ⟨div_eq_of_decomp h0 h0lt, mod_eq_of_decomp h0 h0lt, ?_⟩
  intro hkK
  have hlower := level34_lower hup (by omega) (hfresh k hkK)
  have h1 : a (i + 5 + 2 * k + 1) = 3 * (i + 5 + 2 * k + 1) + (v - 10 - 7 * k) := by omega
  have h1lt : v - 10 - 7 * k < i + 5 + 2 * k + 1 := by omega
  exact ⟨div_eq_of_decomp h1 h1lt, mod_eq_of_decomp h1 h1lt⟩

/-- Budget failure ends the arc inside the lock.  If the lock holds for the pairs below
`K`, pair `K` still starts at level 4 (`6 + 7 K ≤ v`) but its budget fails
(`v < 13 + 7 K`), then the residue increases at the lower clock of pair `K` or at the clock
after it, whatever the orbit does there. -/
theorem popup_lock_wrap {i v K : Nat} (hentry : a (i + 5) = 4 * i + v + 14) (hle : v ≤ i)
    (hstart : 6 + 7 * K ≤ v) (hbudget : v < 13 + 7 * K)
    (hfresh : ∀ k, k ≤ K →
      2 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 1 ∉ valuesThrough (i + 5 + 2 * k))
    (hblocked : ∀ k, k < K →
      (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 3 ∈ valuesThrough (i + 5 + 2 * k + 1)) :
    a (i + 5 + 2 * K) % (i + 5 + 2 * K) < a (i + 5 + 2 * K + 1) % (i + 5 + 2 * K + 1) ∨
      a (i + 5 + 2 * K + 1) % (i + 5 + 2 * K + 1) <
        a (i + 5 + 2 * K + 2) % (i + 5 + 2 * K + 2) := by
  have hval : a (i + 5) = 3 * (i + 5) + (i + v - 1) := by omega
  have hK : 5 * K + 3 ≤ i + v - 1 := by omega
  have hlock := level34_lock hval K hK (fun k hk => hfresh k (Nat.le_of_lt hk)) hblocked
  have hup := hlock K (Nat.le_refl K)
  exact level34_pair_wrap hup (by omega) (by omega) (by omega) (hfresh K (Nat.le_refl K))
    (by omega)

/-- Membership in the history persists to every later clock. -/
theorem valuesThrough_mono_of_le {x n t : Nat} (h : x ∈ valuesThrough n) (hnt : n ≤ t) :
    x ∈ valuesThrough t := by
  induction t with
  | zero =>
      have hn : n = 0 := by omega
      subst hn
      exact h
  | succ t ih =>
      rcases Nat.lt_or_ge n (t + 1) with hlt | hge
      · exact valuesThrough_persist (ih (by omega))
      · have hn : n = t + 1 := by omega
        subst hn
        exact h

/-- The lock cannot break before the pre-landing run is exhausted: with the pre-landing
chain of `J` pairs (the hypotheses of `prelanding_upper_values`), the level-two candidate
of lock pair `k` is the orbit's own value `a (i - 2 (3 k + 1) + 1)` whenever
`3 k + 1 ≤ J`, hence visited when presented. -/
theorem popup_lock_candidate_blocked_by_run {i v J : Nat} (hJ : 2 * J + 1 ≤ i)
    (hchain : ∀ j, j ≤ J → a (i - 2 * j) = (i - 2 * j) + (v + 1 + 3 * j))
    (hblocked : ∀ j, j ≤ J → v + 3 * j ∈ valuesThrough (i - 2 * j)) :
    ∀ k, 3 * k + 1 ≤ J →
      (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 3 ∈ valuesThrough (i + 5 + 2 * k + 1) := by
  intro k hk
  have hj := prelanding_upper_values hJ hchain hblocked (3 * k + 1) (by omega) hk
  have hcand : (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 3 = a (i - 2 * (3 * k + 1) + 1) := by
    omega
  rw [hcand]
  exact valuesThrough_mono_of_le (current_mem_valuesThrough _) (by omega)

/-- Consequently the lock of an isolated late landing persists for at least
`(J + 2) / 3` pairs whenever the level-three values it presents are fresh: the break
index is at least `⌊(J + 2) / 3⌋`. -/
theorem popup_lock_persists {i v J : Nat} (hentry : a (i + 5) = 4 * i + v + 14)
    (hJ : 2 * J + 1 ≤ i)
    (hchain : ∀ j, j ≤ J → a (i - 2 * j) = (i - 2 * j) + (v + 1 + 3 * j))
    (hrun : ∀ j, j ≤ J → v + 3 * j ∈ valuesThrough (i - 2 * j))
    (hoff : 5 * ((J + 2) / 3) + 3 ≤ i + v - 1)
    (hfresh : ∀ k, k < (J + 2) / 3 →
      2 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k) - 1 ∉ valuesThrough (i + 5 + 2 * k)) :
    ∀ k, k ≤ (J + 2) / 3 →
      a (i + 5 + 2 * k) = 3 * (i + 5 + 2 * k) + (i + v - 1 - 5 * k) := by
  have hval : a (i + 5) = 3 * (i + 5) + (i + v - 1) := by omega
  exact level34_lock hval ((J + 2) / 3) hoff hfresh
    (fun k hk => popup_lock_candidate_blocked_by_run hJ hchain hrun k (by omega))

end Recaman
