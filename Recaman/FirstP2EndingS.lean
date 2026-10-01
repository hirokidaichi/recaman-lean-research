import Recaman.LeadingRunSupply

namespace Recaman.FirstP2EndingS

open LeadingRunSupply
open ShortPeriodicSupply (sign)

/-! Words are newest first. Under prefix mass ceiling two, a minimal P2
word ends S. No sign restriction on earlier moments is assumed.

The shifted moment `defect w` changes by `1 - mass w` at each appended
sign. Before the first P2 it stays positive: its only possible decrease
is by one from height two, and equality would itself be P2. -/

def defect (w : List Bool) : Int :=
  moment w - (w.length : Int) * (mass w - 1)

theorem defect_append_sign (w : List Bool) (b : Bool) :
    defect (w ++ [b]) = defect w + 1 - mass w := by
  simp [defect, moment_append, mass_append, moment, sign]
  grind

/-- Positivity is derived from the ceiling and absence of P2 prefixes,
including the whole word; it is not an extra hypothesis on moments. -/
theorem defect_pos_before_p2 (w : List Bool) (hne : w ≠ [])
    (hceil : ∀ j, j ≤ w.length → mass (w.take j) ≤ 2)
    (hno : ∀ j, 0 < j → j ≤ w.length → ¬ P2 (w.take j)) :
    0 < defect w := by
  rcases List.eq_nil_or_concat w with hw | ⟨u, b, hw⟩
  · exact False.elim (hne hw)
  · simp only [List.concat_eq_append] at hw
    subst w
    have hcu : ∀ j, j ≤ u.length → mass (u.take j) ≤ 2 := by
      intro j hj
      have hc := hceil j (by simp; omega)
      rw [List.take_append_of_le_length hj] at hc
      exact hc
    have hnu : ∀ j, 0 < j → j ≤ u.length → ¬ P2 (u.take j) := by
      intro j hj hjlen
      have hn := hno j hj (by simp; omega)
      rw [List.take_append_of_le_length hjlen] at hn
      exact hn
    by_cases hu : u = []
    · subst u
      cases b <;> decide
    · have hi := defect_pos_before_p2 u hu hcu hnu
      have hc : mass u ≤ 2 := by simpa using hcu u.length (by omega)
      have hcfull : mass (u ++ [b]) ≤ 2 := by
        simpa only [List.take_length] using hceil (u ++ [b]).length (by omega)
      have hm : mass (u ++ [b]) = mass u + sign b := by
        simp [mass_append]
      have hd := defect_append_sign u b
      cases b with
      | true =>
        simp [sign] at hm
        omega
      | false =>
        simp [sign] at hm
        by_cases htop : mass u = 2
        · have hnonneg : 0 ≤ defect (u ++ [false]) := by omega
          apply Decidable.byContradiction
          intro hnpos
          have hz : defect (u ++ [false]) = 0 := by omega
          have hp : P2 (u ++ [false]) := by
            constructor
            · omega
            · simp [defect, hm, htop] at hz
              exact hz
          have hn := hno (u ++ [false]).length (by simp) (by omega)
          exact hn (by simpa only [List.take_length] using hp)
        · have hlow : mass u ≤ 1 := by omega
          omega
termination_by w.length
decreasing_by all_goals simp_all

/-- Exact all-length statement of issue #74. -/
theorem minimal_p2_ends_S (w : List Bool) (hp : P2 w)
    (hmin : ∀ j, 0 < j → j < w.length → ¬ P2 (w.take j))
    (hceil : ∀ j, j ≤ w.length → mass (w.take j) ≤ 2) :
    ∃ u, w = u ++ [false] := by
  rcases List.eq_nil_or_concat w with hw | ⟨u, b, hw⟩
  · simp [hw, P2] at hp
  · simp only [List.concat_eq_append] at hw
    subst w
    cases b with
    | false => exact ⟨u, rfl⟩
    | true =>
      have hu : u ≠ [] := by
        intro he
        subst u
        simp [P2, moment, sign] at hp
      have hcu : ∀ j, j ≤ u.length → mass (u.take j) ≤ 2 := by
        intro j hj
        have hc := hceil j (by simp; omega)
        rw [List.take_append_of_le_length hj] at hc
        exact hc
      have hnu : ∀ j, 0 < j → j ≤ u.length → ¬ P2 (u.take j) := by
        intro j hj hjlen
        have hn := hmin j hj (by simp; omega)
        rw [List.take_append_of_le_length hjlen] at hn
        exact hn
      have hi := defect_pos_before_p2 u hu hcu hnu
      have hm : mass u = 0 := by
        have := hp.1
        simp [mass_append, sign] at this
        omega
      have hz : defect (u ++ [true]) = 0 := by simp [defect, hp.1, hp.2]
      have hd := defect_append_sign u true
      omega

/-- The least positive P2 prefix exists and ends S. The output explicitly
retains leastness, including when the full word is not minimal. -/
theorem first_p2_prefix_ends_S (w : List Bool)
    (hceil : ∀ j, j ≤ w.length → mass (w.take j) ≤ 2)
    (hex : ∃ j, 0 < j ∧ j ≤ w.length ∧ P2 (w.take j)) :
    ∃ j, 0 < j ∧ j ≤ w.length ∧ P2 (w.take j) ∧
      (∀ k, 0 < k → k < j → ¬ P2 (w.take k)) ∧
      ∃ u, w.take j = u ++ [false] := by
  have least : ∀ n, 0 < n → n ≤ w.length → P2 (w.take n) →
      ∃ j, 0 < j ∧ j ≤ n ∧ P2 (w.take j) ∧
        ∀ k, 0 < k → k < j → ¬ P2 (w.take k) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn hnlen hp
      by_cases he : ∃ k, 0 < k ∧ k < n ∧ P2 (w.take k)
      · obtain ⟨k, hk, hkn, hpk⟩ := he
        obtain ⟨j, hj, hjk, hpj, hmin⟩ := ih k hkn hk (by omega) hpk
        exact ⟨j, hj, by omega, hpj, hmin⟩
      · refine ⟨n, hn, by omega, hp, ?_⟩
        intro k hk hkn hpk
        exact he ⟨k, hk, hkn, hpk⟩
  obtain ⟨n, hn, hnlen, hpn⟩ := hex
  obtain ⟨j, hj, hjn, hpj, hmin⟩ := least n hn hnlen hpn
  have hjlen : j ≤ w.length := by omega
  have hlen : (w.take j).length = j := by simp [Nat.min_eq_left hjlen]
  have hlocal : ∀ k, 0 < k → k < (w.take j).length →
      ¬ P2 ((w.take j).take k) := by
    intro k hk hkj
    have hkj' : k < j := by omega
    simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hkj')] using hmin k hk hkj'
  have hclocal : ∀ k, k ≤ (w.take j).length → mass ((w.take j).take k) ≤ 2 := by
    intro k hk
    have hkj : k ≤ j := by omega
    simpa [List.take_take, Nat.min_eq_left hkj] using hceil k (by omega)
  exact ⟨j, hj, hjlen, hpj, hmin, minimal_p2_ends_S (w.take j) hpj hlocal hclocal⟩

end Recaman.FirstP2EndingS
