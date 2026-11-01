import Recaman.NestedReservoirCapacity

namespace Recaman.ShortReservoirCapacity

open ShortPeriodicSupply LagElevenSupply LagElevenPeriodic
open SharpPeriodicSupply NestedReservoirCapacity

/-! Concrete lag-at-most-eleven supply plus the bounded-excess extension. -/

def shortPhases (e : Int → Bool) (p : Nat) : List Nat := u7Phases e 0 p ++ u11Phases e 0 p

def shortOff (e : Int → Bool) (u : Nat) : Nat :=
  if supplied (window e u) then phi7Off (window e u) else charge (typeOf (maskAt e u))

theorem small_P2_lags (e : Int → Bool) (t : Int) (d : Nat) (hd : d ≤ 11)
    (hP : P2 e t d) : d = 3 ∨ d = 7 ∨ d = 11 := by
  have h := LeadingRunSupply.p2_count_identities (LeadingRunSupply.past e t d)
    ((LeadingRunSupply.past_p2_iff e t d).mpr hP)
  simp only [LeadingRunSupply.past, List.length_map, List.length_range] at h
  omega

theorem mem_shortPhases (e : Int → Bool) (p u : Nat) :
    u ∈ shortPhases e p ↔ u < p ∧ e u = true ∧ ∃ d, d ≤ 11 ∧ P2 e u d := by
  simp only [shortPhases, List.mem_append, mem_u7Phases, mem_u11Phases, Int.zero_add]
  constructor
  · rintro (h | h)
    · obtain ⟨d,hd0,hd7,hP⟩ := (supplied_window_iff e u).mp h.2.2
      exact ⟨h.1,h.2.1,d,by omega,hP⟩
    · exact ⟨h.1,h.2.1,11,by decide,((minLag11At_iff e u).mp h.2.2).1⟩
  · rintro ⟨hu,hA,d,hd,hP⟩
    by_cases hs : supplied (window e u) = true
    · exact Or.inl ⟨hu,hA,hs⟩
    · right
      have hnot (k : Nat) (hk : 1 ≤ k) (hk7 : k ≤ 7) : ¬ P2 e u k := by
        intro hPk
        exact hs ((supplied_window_iff e u).mpr ⟨k,hk,hk7,hPk⟩)
      have hd11 : d = 11 := by
        rcases small_P2_lags e u d hd hP with h3 | h7 | h11
        · subst d; exact False.elim (hnot 3 (by decide) (by decide) hP)
        · subst d; exact False.elim (hnot 7 (by decide) (by decide) hP)
        · exact h11
      subst d
      exact ⟨hu,hA,(minLag11At_iff e u).mpr
        ⟨hP,hnot 3 (by decide) (by decide),hnot 7 (by decide) (by decide)⟩⟩

theorem shortPhases_nodup (e : Int → Bool) (p : Nat) : (shortPhases e p).Nodup := by
  apply nodup_append
  · exact List.nodup_range.filter _
  · exact List.nodup_range.filter _
  · intro u hu h11
    have h7 := (mem_u7Phases e 0 p u).mp hu
    have hmin := (mem_u11Phases e 0 p u).mp h11
    have h := u7_not_u11 e (0+u) h7.2.2
    rw [hmin.2.2] at h
    contradiction

theorem shortOff_bounds (e : Int → Bool) (p u : Nat) (hu : u ∈ shortPhases e p) :
    1 ≤ shortOff e u ∧ shortOff e u ≤ 11 := by
  by_cases hs : supplied (window e u) = true
  · have hb := phi7Off_bounds hs
    simp only [shortOff, hs, ↓reduceIte]
    omega
  · have hmin : minLag11 (maskAt e u) = true := by
      rcases List.mem_append.mp hu with h7 | h11
      · exact False.elim (hs (by simpa using ((mem_u7Phases e 0 p u).mp h7).2.2))
      · simpa using ((mem_u11Phases e 0 p u).mp h11).2.2
    have hm := (typeOf_spec _ (maskAt_lt e u) hmin).1
    have hb := of_decide_eq_true (List.all_eq_true.mp charge_bounds _ hm)
    simp only [shortOff, hs, Bool.false_eq_true, ↓reduceIte]
    omega

theorem short_phase_eq_phi7 (e : Int → Bool) (p u : Nat)
    (hs : supplied (window e u) = true) :
    phase p ((u : Int)-shortOff e u) = phi7Phase e 0 p u := by
  simp [shortOff, hs, phase, phi7Phase]

theorem short_phase_eq_phi11 (e : Int → Bool) (p u : Nat)
    (hmin : minLag11 (maskAt e u) = true) :
    phase p ((u : Int)-shortOff e u) = phi11Phase e 0 p u := by
  have hs : supplied (window e u) = false := by
    cases h : supplied (window e u)
    · rfl
    · have hh := u7_not_u11 e u h
      rw [hmin] at hh
      contradiction
  simp [shortOff, hs, phase, phi11Phase]


theorem short_image_is_S (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (u : Nat) (hu : u ∈ shortPhases e p) :
    e (phase p ((u : Int)-shortOff e u)) = false := by
  rcases List.mem_append.mp hu with h7 | h11
  · have h := (mem_u7Phases e 0 p u).mp h7
    rw [short_phase_eq_phi7 e p u (by simpa using h.2.2)]
    simpa using phi7Phase_is_sub e 0 hper hp u h.2.1 h.2.2
  · have h := (mem_u11Phases e 0 p u).mp h11
    rw [short_phase_eq_phi11 e p u (by simpa using h.2.2)]
    simpa using phi11Phase_is_sub e 0 hper hp u h.2.1 h.2.2

theorem short_phase_injective (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (u v : Nat)
    (hu : u ∈ shortPhases e p) (hv : v ∈ shortPhases e p)
    (heq : phase p ((u : Int)-shortOff e u) = phase p ((v : Int)-shortOff e v)) : u = v := by
  rcases List.mem_append.mp hu with hu7 | hu11 <;>
    rcases List.mem_append.mp hv with hv7 | hv11
  · have h := (mem_u7Phases e 0 p u).mp hu7
    have k := (mem_u7Phases e 0 p v).mp hv7
    rw [short_phase_eq_phi7 e p u (by simpa using h.2.2),
      short_phase_eq_phi7 e p v (by simpa using k.2.2)] at heq
    exact phi7Phase_inj e 0 hper hp u v h.1 k.1 h.2.1 k.2.1 h.2.2 k.2.2 heq
  · have h := (mem_u7Phases e 0 p u).mp hu7
    have k := (mem_u11Phases e 0 p v).mp hv11
    rw [short_phase_eq_phi7 e p u (by simpa using h.2.2),
      short_phase_eq_phi11 e p v (by simpa using k.2.2)] at heq
    exact False.elim (phi7_phi11_image_ne e 0 hper hp u v h.1 k.1 h.2.1 k.2.1 h.2.2 k.2.2 heq)
  · have h := (mem_u11Phases e 0 p u).mp hu11
    have k := (mem_u7Phases e 0 p v).mp hv7
    rw [short_phase_eq_phi11 e p u (by simpa using h.2.2),
      short_phase_eq_phi7 e p v (by simpa using k.2.2)] at heq
    exact False.elim (phi7_phi11_image_ne e 0 hper hp v u k.1 h.1 k.2.1 h.2.1 k.2.2 h.2.2 heq.symm)
  · have h := (mem_u11Phases e 0 p u).mp hu11
    have k := (mem_u11Phases e 0 p v).mp hv11
    rw [short_phase_eq_phi11 e p u (by simpa using h.2.2),
      short_phase_eq_phi11 e p v (by simpa using k.2.2)] at heq
    exact phi11Phase_inj e 0 hper hp u v h.1 k.1 h.2.1 k.2.1 h.2.2 k.2.2 heq

/-- All short supplied A phases are included; the old short injection is
fully discharged, rather than retained as a premise. -/
theorem short_plus_bounded_excess_capacity (e : Int → Bool) (p R : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (hp : 0 < p)
    (Q : List Nat) (run : Nat → Nat)
    (hQnodup : Q.Nodup) (hQrange : ∀ t, t ∈ Q → t < p)
    (hRun : ∀ t, t ∈ Q → 4*R+13 ≤ run t ∧ e t = true ∧
      (∀ i, i < run t → e ((t : Int)-((i+1 : Nat) : Int)) = true) ∧
      e ((t : Int)-run t-1) = false ∧
      ∃ d, P2 e t d ∧ (d : Int) ≤ 4*run t-1+4*R) :
    suppliedCount e 0 p + u11Count e 0 p + Q.length ≤ subtractionCount e 0 p := by
  have hcap := bounded_excess_periodic_capacity_extension e p 11 R hper hp
    (shortPhases e p) Q run (shortOff e) (shortPhases_nodup e p) hQnodup
    (fun u hu => ((mem_shortPhases e p u).mp hu).1) hQrange
    (fun u hu => ((mem_shortPhases e p u).mp hu).2.1)
    (fun u hu => shortOff_bounds e p u hu)
    (fun u hu => short_image_is_S e p hp hper u hu)
    (fun u v hu hv heq => short_phase_injective e p hp hper u v hu hv heq)
    (by
      intro t ht
      have h := hRun t ht
      exact ⟨by omega,by omega,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩)
  simpa [shortPhases, suppliedCount_eq_filter, u11Count_eq_filter,
    subtractionCount_eq_filter] using hcap

/-- A genuine new supply class: m17, excess4, minimum lag71. -/
theorem nonsharp_extension_word_certificate :
    let w := BoundedExcessReservoir.failedFixedChargeFamily 17
    w.length = 71 ∧ w.take 17 = List.replicate 17 true ∧
      w[17]? = some false ∧ LeadingRunSupply.P2 w ∧
      (∀ d : Fin 71, ¬ LeadingRunSupply.P2 (w.take d.val)) ∧
      17 = 4*1+13 ∧ 71 = 4*17-1+4*1 := by
  unfold LeadingRunSupply.P2 LeadingRunSupply.mass
  decide

end Recaman.ShortReservoirCapacity
