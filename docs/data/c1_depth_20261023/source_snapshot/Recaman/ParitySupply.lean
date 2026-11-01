import Recaman.LeadingRunSupply

namespace Recaman.ParitySupply

open LeadingRunSupply

/-! All-lag P2 structure when every odd time is an A sign. -/

def pairs (v : List Bool) : List Bool := v.flatMap (fun b => [b,true])

theorem pairs_length (v : List Bool) : (pairs v).length = 2*v.length := by
  induction v with
  | nil => simp [pairs]
  | cons b v ih => simp [pairs, List.flatMap_cons] at *; omega

theorem positions_nonneg (v : List Bool) : 0 ≤ positions v := by
  induction v with
  | nil => simp [positions]
  | cons b v ih => have h := (ones_bounds v).1; cases b <;> simp [positions] <;> omega

theorem pairs_mass (v : List Bool) : mass (pairs v) = 2*ones v := by
  induction v with
  | nil => simp [pairs, ones]
  | cons b v ih =>
    change mass ([b,true] ++ pairs v) = _
    rw [mass_append, ih]
    cases b <;> simp [mass_cons, ShortPeriodicSupply.sign, ones] <;> omega

theorem pairs_moment (v : List Bool) :
    moment (pairs v) = 4*positions v-2*ones v+v.length := by
  induction v with
  | nil => simp [pairs, moment, positions, ones]
  | cons b v ih =>
    change moment ([b,true] ++ pairs v) = _
    rw [moment_append, ih, pairs_mass]
    cases b <;> simp [moment, mass_cons, ShortPeriodicSupply.sign, positions, ones] <;> omega

theorem fixed_first_not_P2 (v : List Bool) : ¬ P2 (true :: pairs v) := by
  intro h
  have ht := h.2
  change 1+mass (pairs v)+moment (pairs v) = 0 at ht
  rw [pairs_mass, pairs_moment] at ht
  have hpos := positions_nonneg v
  omega

theorem variable_first_P2_data (v : List Bool) (b : Bool)
    (h : P2 (pairs v ++ [b])) :
    b = false ∧ ones v = 1 ∧ (v.length : Int)+3 = 4*positions v := by
  have hs := h.1
  have ht := h.2
  rw [mass_append, pairs_mass] at hs
  rw [moment_append, pairs_length, pairs_moment] at ht
  have hpos := positions_nonneg v
  cases b <;> simp [moment, mass_cons, ShortPeriodicSupply.sign] at hs ht ⊢ <;> omega

theorem ones_zero_get (v : List Bool) (h : ones v = 0) (i : Nat) (hi : i < v.length) :
    v[i]? = some false := by
  induction v generalizing i with
  | nil => simp at hi
  | cons b v ih =>
    have hb := (ones_bounds v).1
    cases b
    · have ht : ones v = 0 := by simpa [ones] using h
      cases i with
      | zero => rfl
      | succ i => simpa using ih ht i (by simpa using hi)
    · simp [ones] at h
      omega

theorem ones_one_position (v : List Bool) (h : ones v = 1) :
    ∃ k, k < v.length ∧ positions v = (k : Int)+1 ∧ v[k]? = some true ∧
      ∀ i, i < v.length → i ≠ k → v[i]? = some false := by
  induction v with
  | nil => simp [ones] at h
  | cons b v ih =>
    have hb := (ones_bounds v).1
    cases b
    · have ht : ones v = 1 := by simpa [ones] using h
      obtain ⟨k,hk,hpos,hget,hothers⟩ := ih ht
      refine ⟨k+1,by simp; omega,?_,?_,?_⟩
      · simp [positions, ht, hpos]
        omega
      · simpa using hget
      · intro i hi hine
        cases i with
        | zero => rfl
        | succ i => simpa using hothers i (by simpa using hi) (by omega)
    · have ht : ones v = 0 := by simp [ones] at h; omega
      have hpos : positions v = 0 := by
        have hupper := positions_upper v
        rw [ht] at hupper
        have hlower := positions_nonneg v
        omega
      refine ⟨0,by simp,?_,rfl,?_⟩
      · simp [positions, ht, hpos]
      · intro i hi hine
        cases i with
        | zero => omega
        | succ i => simpa using ones_zero_get v ht i (by simpa using hi)

theorem past_succ (e : Int → Bool) (t : Int) (d : Nat) :
    past e t (d+1) = e (t-1) :: past e (t-1) d := by
  have hd : d+1 = 1+d := by omega
  rw [hd, past_append]
  have hhead : past e t 1 = [e (t-1)] := by simp [past]
  rw [hhead]
  rfl

def evenSigns (e : Int → Bool) (n : Int) : Bool := e (2*n)

theorem past_even (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (r : Nat) :
    past e (2*n) (2*r+1) = true :: pairs (past (evenSigns e) n r) := by
  induction r generalizing n with
  | zero =>
    have h := hfixed (n-1)
    have htime : 2*(n-1)+1 = 2*n-1 := by omega
    simpa [past, pairs, htime] using h
  | succ r ih =>
    have hd : 2*(r+1)+1 = ((2*r+1)+1)+1 := by omega
    rw [hd, past_succ, past_succ]
    have htime : 2*n-1-1 = 2*(n-1) := by omega
    rw [htime, ih, past_succ]
    have hfix : e (2*n-1) = true := by
      have hh := hfixed (n-1)
      have heq : 2*(n-1)+1 = 2*n-1 := by omega
      rwa [heq] at hh
    simp [pairs, evenSigns, hfix]

theorem past_odd (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (r : Nat) :
    past e (2*n+1) (2*r+1) = pairs (past (evenSigns e) (n+1) r) ++ [evenSigns e (n-r)] := by
  induction r generalizing n with
  | zero => simp [past, pairs, evenSigns]
  | succ r ih =>
    have hd : 2*(r+1)+1 = ((2*r+1)+1)+1 := by omega
    rw [hd, past_succ, past_succ]
    have htime : 2*n+1-1-1 = 2*(n-1)+1 := by omega
    rw [htime, ih, past_succ]
    have hfix : e (2*n+1-1-1) = true := by rw [htime]; exact hfixed (n-1)
    have ht₁ : n-1+1 = n := by omega
    have ht₂ : n+1-1 = n := by omega
    have ht₃ : n-1-(r : Int) = n-(r+1 : Nat) := by omega
    simp [pairs, evenSigns, ht₁, ht₂, ht₃, hfixed]


theorem P2_length_odd (e : Int → Bool) (t : Int) (d : Nat)
    (h : ShortPeriodicSupply.P2 e t d) : ∃ r, d = 2*r+1 := by
  have hc := p2_count_identities (past e t d) ((past_p2_iff e t d).mpr h)
  simp only [past, List.length_map, List.length_range] at hc
  exact ⟨d/2,by omega⟩

theorem even_phase_not_P2 (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (d : Nat) : ¬ ShortPeriodicSupply.P2 e (2*n) d := by
  intro h
  obtain ⟨r,rfl⟩ := P2_length_odd e (2*n) d h
  have hw := (past_p2_iff e (2*n) (2*r+1)).mpr h
  rw [past_even e hfixed] at hw
  exact fixed_first_not_P2 _ hw

theorem odd_P2_necessary (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (d : Nat) (h : ShortPeriodicSupply.P2 e (2*n+1) d) :
    ∃ k : Nat, d = 8*k+3 ∧ evenSigns e (n-k) = true ∧
      ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → evenSigns e (n-j) = false := by
  obtain ⟨r,hd⟩ := P2_length_odd e (2*n+1) d h
  have hw := (past_p2_iff e (2*n+1) d).mpr h
  rw [hd, past_odd e hfixed] at hw
  have hb := variable_first_P2_data _ _ hw
  obtain ⟨k,hk,hpos,hget,hothers⟩ := ones_one_position _ hb.2.1
  have hlen : (past (evenSigns e) (n+1) r).length = r := by simp [past]
  rw [hlen] at hk
  have hr : r = 4*k+1 := by rw [hlen,hpos] at hb; omega
  refine ⟨k,by omega,?_,?_⟩
  · have htime : n+1-((k : Int)+1) = n-k := by omega
    have hh : some (evenSigns e (n-k)) = some true := by simpa [past,hk,htime] using hget
    exact Option.some.inj hh
  · intro j hj hjk
    by_cases hjr : j = r
    · subst j
      exact hb.1
    · have hjlt : j < r := by omega
      have hh := hothers j (by rw [hlen]; exact hjlt) hjk
      have htime : n+1-((j : Int)+1) = n-j := by omega
      have hh' : some (evenSigns e (n-j)) = some false := by simpa [past,hjlt,htime] using hh
      exact Option.some.inj hh'

theorem zero_data_of_get (v : List Bool) (h : ∀ i, i < v.length → v[i]? = some false) :
    ones v = 0 ∧ positions v = 0 := by
  induction v with
  | nil => simp [ones,positions]
  | cons b v ih =>
    have hb := h 0 (by simp)
    have hb' : b = false := by simpa using hb
    subst b
    have ht := ih (fun i hi => by simpa using h (i+1) (by simpa using hi))
    simp [ones,positions,ht.1,ht.2]

theorem one_data_of_get (v : List Bool) (k : Nat) (hk : k < v.length)
    (hA : v[k]? = some true)
    (hS : ∀ i, i < v.length → i ≠ k → v[i]? = some false) :
    ones v = 1 ∧ positions v = (k : Int)+1 := by
  induction v generalizing k with
  | nil => simp at hk
  | cons b v ih =>
    cases k with
    | zero =>
      have hb : b = true := by simpa using hA
      subst b
      have ht := zero_data_of_get v (fun i hi => by simpa using hS (i+1) (by simpa using hi) (by omega))
      simp [ones,positions,ht.1,ht.2]
    | succ k =>
      have hb : b = false := by simpa using hS 0 (by simp) (by omega)
      subst b
      have ht := ih k (by simpa using hk) (by simpa using hA)
        (fun i hi hik => by simpa using hS (i+1) (by simpa using hi) (by omega))
      simp [ones,positions,ht.1,ht.2]
      omega

theorem odd_P2_sufficient (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (k : Nat) (hA : evenSigns e (n-k) = true)
    (hS : ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → evenSigns e (n-j) = false) :
    ShortPeriodicSupply.P2 e (2*n+1) (8*k+3) := by
  have hlast := hS (4*k+1) (by omega) (by omega)
  have hlen : (past (evenSigns e) (n+1) (4*k+1)).length = 4*k+1 := by simp [past]
  have hvA : (past (evenSigns e) (n+1) (4*k+1))[k]? = some true := by
    have htime : n+1-((k : Int)+1) = n-k := by omega
    simp [past,show k < 4*k+1 by omega,htime,hA]
  have hvS : ∀ i, i < (past (evenSigns e) (n+1) (4*k+1)).length →
      i ≠ k → (past (evenSigns e) (n+1) (4*k+1))[i]? = some false := by
    intro i hi hik
    have hi' : i < 4*k+1 := by rw [hlen] at hi; exact hi
    have htime : n+1-((i : Int)+1) = n-i := by omega
    simp [past,hi',htime,hS i (by omega) hik]
  have hv := one_data_of_get _ k (by rw [hlen]; omega) hvA hvS
  apply (past_p2_iff e (2*n+1) (8*k+3)).mp
  have hd : 8*k+3 = 2*(4*k+1)+1 := by omega
  rw [hd, past_odd e hfixed, hlast]
  constructor
  · rw [mass_append,pairs_mass,hv.1]
    simp [mass_cons,ShortPeriodicSupply.sign]
  · rw [moment_append,pairs_moment,pairs_length,hv.1,hv.2,hlen]
    simp [moment,mass_cons,ShortPeriodicSupply.sign]
    omega

/-- Exact all-lag classification; both directions are proved. -/
theorem odd_P2_iff (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (d : Nat) : ShortPeriodicSupply.P2 e (2*n+1) d ↔
    ∃ k : Nat, d = 8*k+3 ∧ evenSigns e (n-k) = true ∧
      ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → evenSigns e (n-j) = false := by
  constructor
  · exact odd_P2_necessary e hfixed n d
  · rintro ⟨k,rfl,hA,hS⟩
    exact odd_P2_sufficient e hfixed n k hA hS


theorem witness_unique (f : Int → Bool) (n : Int) (k l : Nat)
    (hkA : f (n-k) = true)
    (hkS : ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → f (n-j) = false)
    (hlA : f (n-l) = true)
    (hlS : ∀ j : Nat, j ≤ 4*l+1 → j ≠ l → f (n-j) = false) : k = l := by
  by_cases hkl : k < l
  · have h := hlS k (by omega) (by omega)
    rw [hkA] at h
    contradiction
  · by_cases hlk : l < k
    · have h := hkS l (by omega) (by omega)
      rw [hlA] at h
      contradiction
    · omega

/-- Every supplied phase has exactly one lag in the parity-restricted stream. -/
theorem P2_lag_unique (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (n : Int) (d d₂ : Nat) (h : ShortPeriodicSupply.P2 e (2*n+1) d)
    (h₂ : ShortPeriodicSupply.P2 e (2*n+1) d₂) : d = d₂ := by
  obtain ⟨k,hk,hkA,hkS⟩ := odd_P2_necessary e hfixed n d h
  obtain ⟨l,hl,hlA,hlS⟩ := odd_P2_necessary e hfixed n d₂ h₂
  have hkl := witness_unique (evenSigns e) n k l hkA hkS hlA hlS
  omega

theorem witness_charge_is_S (f : Int → Bool) (n : Int) (k : Nat)
    (hS : ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → f (n-j) = false) :
    f (n-2*k-1) = false := by
  have h := hS (2*k+1) (by omega) (by omega)
  have htime : n-((2*k+1 : Nat) : Int) = n-2*k-1 := by omega
  rwa [htime] at h

theorem witness_charge_injective (f : Int → Bool) (n m : Int) (k l : Nat)
    (hkA : f (n-k) = true)
    (hkS : ∀ j : Nat, j ≤ 4*k+1 → j ≠ k → f (n-j) = false)
    (hlA : f (m-l) = true)
    (hlS : ∀ j : Nat, j ≤ 4*l+1 → j ≠ l → f (m-j) = false)
    (heq : n-2*k-1 = m-2*l-1) : n = m ∧ k = l := by
  by_cases hkl : k < l
  · have hj : 2*l-k ≤ 4*l+1 := by omega
    have hjne : 2*l-k ≠ l := by omega
    have h := hlS (2*l-k) hj hjne
    have htime : m-((2*l-k : Nat) : Int) = n-k := by omega
    rw [htime,hkA] at h
    contradiction
  · by_cases hlk : l < k
    · have h := hkS (2*k-l) (by omega) (by omega)
      have htime : n-((2*k-l : Nat) : Int) = m-l := by omega
      rw [htime,hlA] at h
      contradiction
    · constructor <;> omega

theorem supplied_phase_is_odd (e : Int → Bool) (hfixed : ∀ n : Int, e (2*n+1) = true)
    (t : Int) (d : Nat) (h : ShortPeriodicSupply.P2 e t d) : ∃ n : Int, t = 2*n+1 := by
  have hdiv := Int.ediv_mul_add_emod t 2
  have hlo := Int.emod_nonneg t (by decide : (2 : Int) ≠ 0)
  have hhi := Int.emod_lt_of_pos t (by decide : (0 : Int) < 2)
  by_cases hmod : t % 2 = 0
  · have ht : t = 2*(t/2) := by omega
    rw [ht] at h
    exact False.elim (even_phase_not_P2 e hfixed (t/2) d h)
  · exact ⟨t/2,by omega⟩

end Recaman.ParitySupply
