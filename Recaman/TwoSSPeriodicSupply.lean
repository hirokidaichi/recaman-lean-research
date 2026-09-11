import Recaman.TwoSSEndpoint
import Recaman.LowSSPeriodicSupply

/-!
# TwoSSPeriodicSupply

Periodic modular endpoint injectivity and joint capacity for SS=2 windows.

Key results:
- `two_SS_endpoint_mod_injective`: Any two SS=2 windows with the same modular
  endpoint phase must belong to identical phases modulo p.
- `ss_one_two_endpoint_mod_disjoint`: An SS=1 window and an SS=2 window can
  never produce the same modular endpoint phase.
- `two_SS_clean_endpoint_mod_order`: Any shared modular endpoint between an SS=2
  window and a clean window forces the clean window to strictly precede the SS=2
  window in time.
- `periodic_twoSS_Sended_capacity`: Capacity bound `|U2| ≤ |D|` for S-ended SS=2
  windows.
- `periodic_one_two_SS_Sended_joint_capacity`: Joint capacity bound `|U1| + |U2| ≤ |D|`
  for the disjoint union of one-SS and two-SS S-ended windows.
-/

namespace Recaman.TwoSSPeriodicSupply

open LeadingRunSupply OneSSMultiplicity LowSSEndpoint EndpointRepetitionBudget TwoSSEndpoint SharpPeriodicSupply LowSSPeriodicSupply

/-- Two SS=2 windows ending at A having the same modular endpoint phase must
belong to identical phases modulo p. -/
theorem two_SS_endpoint_mod_injective (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (t u : Int) (d f : Nat)
    (htA : e t = true) (huA : e u = true)
    (htss : ssCount (past e t d) = 2) (huss : ssCount (past e u f) = 2)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u f)
    (heq : endpointPhase p t d = endpointPhase p u f) : t % p = u % p := by
  have hmod := phase_eq_mod p hp (t - d) (u - f) heq
  obtain ⟨z, hz⟩ := lift_equal_mod p _ _ hmod
  have huA' : e (u + z * p) = true := by rw [LagElevenPeriodic.e_shift e p hper]; exact huA
  have huss' : ssCount (past e (u + z * p) f) = 2 := by rw [past_shift e p hper]; exact huss
  have huP' := (p2_shift e p hper u z f).mpr huP
  have htu := two_SS_endpoint_injective e t (u + z * p) d f htA huA' htss huss' htP huP' (by omega)
  rw [htu]
  simp [Int.add_emod]

/-- An SS=1 window and an SS=2 window ending at A can never have the same modular
endpoint phase. -/
theorem ss_one_two_endpoint_mod_disjoint (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (t u : Int) (d f : Nat)
    (htA : e t = true) (huA : e u = true)
    (htss : ssCount (past e t d) = 1) (huss : ssCount (past e u f) = 2)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u f)
    (heq : endpointPhase p t d = endpointPhase p u f) : False := by
  have hmod := phase_eq_mod p hp (t - d) (u - f) heq
  obtain ⟨z, hz⟩ := lift_equal_mod p _ _ hmod
  have huA' : e (u + z * p) = true := by rw [LagElevenPeriodic.e_shift e p hper]; exact huA
  have huss' : ssCount (past e (u + z * p) f) = 2 := by rw [past_shift e p hper]; exact huss
  have huP' := (p2_shift e p hper u z f).mpr huP
  exact ss_one_two_no_shared_endpoint e t (u + z * p) d f htA huA' htss huss' htP huP' (by omega)

/-- An SS=2 window can never precede a clean window on the same endpoint residue:
any shared endpoint forces the clean window to be strictly earlier in time. -/
theorem two_SS_clean_endpoint_mod_order (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (t u : Int) (d f : Nat)
    (htA : e t = true) (huA : e u = true)
    (htss : ssCount (past e t d) = 2) (huss : ssCount (past e u f) = 0)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u f)
    (heq : endpointPhase p t d = endpointPhase p u f) :
    ∃ z : Int, u + z * p < t ∧ t - d = (u + z * p) - f := by
  have hmod := phase_eq_mod p hp (t - d) (u - f) heq
  obtain ⟨z, hz⟩ := lift_equal_mod p _ _ hmod
  have huA' : e (u + z * p) = true := by rw [LagElevenPeriodic.e_shift e p hper]; exact huA
  have huss' : ssCount (past e (u + z * p) f) ≤ 2 := by rw [past_shift e p hper, huss]; omega
  have huP' := (p2_shift e p hper u z f).mpr huP
  by_cases hlt : t < u + z * p
  · let k := ((u + z * p) - t).toNat
    have hk : (k : Int) = (u + z * p) - t := Int.toNat_of_nonneg (by omega)
    have hkpos : 0 < k := by omega
    have htime : t + (k : Int) = u + z * p := by omega
    have hlen : k + d = f := by omega
    have huP'' : ShortPeriodicSupply.P2 e (t + k) (k + d) := by
      rw [htime, hlen]; exact huP'
    have huss'' : ssCount (past e (t + k) (k + d)) ≤ 2 := by
      rw [htime, hlen]; exact huss'
    have htss_ge : 1 ≤ ssCount (past e t d) := by rw [htss]; omega
    have hf := stream_earlier_ss_pos_obstruction e t k d hkpos htA huP'' htP htss_ge huss''
    exact False.elim hf
  · by_cases he : t = u + z * p
    · subst he
      have heqd : d = f := by omega
      subst f
      have hcontra : ssCount (past e (u + z * p) d) = 0 := by
        rw [past_shift e p hper u z d, huss]
      omega
    · refine ⟨z, by omega, by omega⟩

/-- Capacity bound |U2| ≤ |D| for S-ended SS=2 windows. -/
theorem periodic_twoSS_Sended_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (hUnodup : U.Nodup) (hUrange : ∀ u, u ∈ U → u < p)
    (hSupply : ∀ u, u ∈ U → e u = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d) = 2 ∧ e (u - d) = false) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  classical
  let lag := fun u : Nat => if hu : u ∈ U then Classical.choose (hSupply u hu).2 else 0
  have hlag : ∀ u, u ∈ U → ShortPeriodicSupply.P2 e u (lag u) ∧
      ssCount (past e u (lag u)) = 2 ∧ e (u - lag u) = false := by
    intro u hu
    dsimp [lag]
    rw [dif_pos hu]
    exact Classical.choose_spec (hSupply u hu).2
  let f := fun u : Nat => endpointPhase p u (lag u)
  have hinj : ∀ u v, u ∈ U → v ∈ U → f u = f v → u = v := by
    intro u v hu hv heq
    have hmod := two_SS_endpoint_mod_injective e p hp hper u v (lag u) (lag v)
      (hSupply u hu).1 (hSupply v hv).1 (hlag u hu).2.1 (hlag v hv).2.1
      (hlag u hu).1 (hlag v hv).1 heq
    have hult := hUrange u hu
    have hvlt := hUrange v hv
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hnodup := LagElevenPeriodic.nodup_map_of_inj hUnodup hinj
  have hsub : U.map f ⊆ LagElevenPeriodic.subPhases e 0 p := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
    apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
    refine ⟨phase_lt p hp _, ?_⟩
    simpa [f] using endpoint_is_S e p hp hper u (lag u) (hlag u hu).2.2
  have hlen := hnodup.length_le_of_subset hsub
  simpa using hlen

/-- Joint capacity of one-SS and two-SS phases whose windows end in S:
their endpoint images are disjoint, so their combined count is bounded by |D|. -/
theorem periodic_one_two_SS_Sended_joint_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U1 U2 : List Nat) (hU1nodup : U1.Nodup) (hU2nodup : U2.Nodup)
    (hU1range : ∀ u, u ∈ U1 → u < p) (hU2range : ∀ u, u ∈ U2 → u < p)
    (hSupply1 : ∀ u, u ∈ U1 → e u = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d) = 1 ∧ e (u - d) = false)
    (hSupply2 : ∀ u, u ∈ U2 → e u = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d) = 2 ∧ e (u - d) = false) :
    U1.length + U2.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  classical
  let lag1 := fun u : Nat => if hu : u ∈ U1 then Classical.choose (hSupply1 u hu).2 else 0
  have hlag1 : ∀ u, u ∈ U1 → ShortPeriodicSupply.P2 e u (lag1 u) ∧
      ssCount (past e u (lag1 u)) = 1 ∧ e (u - lag1 u) = false := by
    intro u hu; dsimp [lag1]; rw [dif_pos hu]; exact Classical.choose_spec (hSupply1 u hu).2
  let lag2 := fun u : Nat => if hu : u ∈ U2 then Classical.choose (hSupply2 u hu).2 else 0
  have hlag2 : ∀ u, u ∈ U2 → ShortPeriodicSupply.P2 e u (lag2 u) ∧
      ssCount (past e u (lag2 u)) = 2 ∧ e (u - lag2 u) = false := by
    intro u hu; dsimp [lag2]; rw [dif_pos hu]; exact Classical.choose_spec (hSupply2 u hu).2
  let f1 := fun u : Nat => endpointPhase p u (lag1 u)
  let f2 := fun u : Nat => endpointPhase p u (lag2 u)
  have hinj1 : ∀ u v, u ∈ U1 → v ∈ U1 → f1 u = f1 v → u = v := by
    intro u v hu hv heq
    have h1 : ssCount (past e u (lag1 u)) ≤ 1 := by
      have := (hlag1 u hu).2.1; omega
    have h2 : ssCount (past e v (lag1 v)) ≤ 1 := by
      have := (hlag1 v hv).2.1; omega
    have hmod := LowSSPeriodicSupply.endpoint_mod_injective e p hp hper u v (lag1 u) (lag1 v)
      (hSupply1 u hu).1 (hSupply1 v hv).1 h1 h2
      (hlag1 u hu).1 (hlag1 v hv).1 heq
    have hult := hU1range u hu; have hvlt := hU1range v hv
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hinj2 : ∀ u v, u ∈ U2 → v ∈ U2 → f2 u = f2 v → u = v := by
    intro u v hu hv heq
    have hmod := two_SS_endpoint_mod_injective e p hp hper u v (lag2 u) (lag2 v)
      (hSupply2 u hu).1 (hSupply2 v hv).1 (hlag2 u hu).2.1 (hlag2 v hv).2.1
      (hlag2 u hu).1 (hlag2 v hv).1 heq
    have hult := hU2range u hu; have hvlt := hU2range v hv
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hdisj : ∀ a, a ∈ U1.map f1 → a ∉ U2.map f2 := by
    intro a ha1 ha2
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha1
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp ha2
    have hcontra := ss_one_two_endpoint_mod_disjoint e p hp hper u v (lag1 u) (lag2 v)
      (hSupply1 u hu).1 (hSupply2 v hv).1 (hlag1 u hu).2.1 (hlag2 v hv).2.1
      (hlag1 u hu).1 (hlag2 v hv).1 heq.symm
    exact hcontra
  have h1nodup := LagElevenPeriodic.nodup_map_of_inj hU1nodup hinj1
  have h2nodup := LagElevenPeriodic.nodup_map_of_inj hU2nodup hinj2
  have hnodup := LagElevenPeriodic.nodup_append h1nodup h2nodup hdisj
  have hsub : (U1.map f1 ++ U2.map f2) ⊆ LagElevenPeriodic.subPhases e 0 p := by
    apply List.append_subset.mpr
    constructor
    · intro q hq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
      apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
      refine ⟨phase_lt p hp _, ?_⟩
      simpa [f1] using endpoint_is_S e p hp hper u (lag1 u) (hlag1 u hu).2.2
    · intro q hq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
      apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
      refine ⟨phase_lt p hp _, ?_⟩
      simpa [f2] using endpoint_is_S e p hp hper u (lag2 u) (hlag2 u hu).2.2
  have hlen := hnodup.length_le_of_subset hsub
  simp only [List.length_append, List.length_map] at hlen
  exact hlen

/-- A window of length at least the period p covers all residue classes modulo p. -/
theorem window_covers_all_phases (p : Nat) (hp : 0 < p) (t : Int) (d : Nat) (hd : p ≤ d)
    (s : Nat) (hs : s < p) :
    ∃ i : Nat, i < d ∧ (t - 1 - (i : Int)) % (p : Int) = (s : Int) := by
  let rem := (t - 1 - (s : Int)) % (p : Int)
  have hrem_nonneg : 0 ≤ rem := Int.emod_nonneg _ (by omega)
  have hrem_lt : rem < (p : Int) := Int.emod_lt_of_pos _ (by omega)
  let i := rem.toNat
  have hi : (i : Int) = rem := Int.toNat_of_nonneg hrem_nonneg
  have hilt : i < p := by omega
  have hid : i < d := by omega
  refine ⟨i, hid, ?_⟩
  rw [hi]
  have hdiv := Int.ediv_mul_add_emod (t - 1 - (s : Int)) (p : Int)
  have hrew : t - 1 - rem = (t - 1 - (s : Int)) / (p : Int) * (p : Int) + (s : Int) := by omega
  rw [hrew, Int.add_emod]
  have hzero : (t - 1 - (s : Int)) / (p : Int) * (p : Int) % (p : Int) = 0 := by simp
  rw [hzero, Int.zero_add, Int.emod_emod]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Periodic sign values agree on congruent inputs modulo p. -/
theorem emod_eq_shift (e : Int → Bool) (p : Nat) (_hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (x y : Int) (heq : x % (p : Int) = y % (p : Int)) :
    e x = e y := by
  obtain ⟨z, hz⟩ := lift_equal_mod p x y heq
  rw [hz, LagElevenPeriodic.e_shift e p hper]

/-- A window of length at least the period p contains every subtraction phase of e. -/
theorem periodic_window_covers_subtraction (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (d : Nat) (hd : p ≤ d)
    (s : Nat) (hs : s < p) (hsS : e s = false) :
    ∃ i : Nat, i < d ∧ e (t - 1 - (i : Int)) = false ∧ (t - 1 - (i : Int)) % (p : Int) = (s : Int) := by
  obtain ⟨i, hid, hmod⟩ := window_covers_all_phases p hp t d hd s hs
  refine ⟨i, hid, ?_, hmod⟩
  have he : e (t - 1 - (i : Int)) = e (s : Int) := by
    apply emod_eq_shift e p hp hper
    rw [hmod, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [he, hsS]

/-- An SS=2 window in a period p ≤ 11 covers ALL subtraction phases of the period. -/
theorem ss2_window_covers_all_subtractions_of_p_le_eleven (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (d : Nat)
    (hP : ShortPeriodicSupply.P2 e t d) (hss : ssCount (past e t d) = 2)
    (s : Nat) (hs : s < p) (hsS : e s = false) :
    ∃ i : Nat, i < d ∧ e (t - 1 - (i : Int)) = false ∧ (t - 1 - (i : Int)) % (p : Int) = (s : Int) := by
  have hd11 := TwoSSEndpoint.stream_ss2_lag_ge_eleven e t d hP hss
  have hpd : p ≤ d := by omega
  exact periodic_window_covers_subtraction e p hp hper t d hpd s hs hsS

end Recaman.TwoSSPeriodicSupply
