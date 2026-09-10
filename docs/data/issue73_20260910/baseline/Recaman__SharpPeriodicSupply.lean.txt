import Recaman.LeadingRunSupply
import Recaman.LagElevenPeriodic

namespace Recaman.SharpPeriodicSupply

open LeadingRunSupply

/-! Periodic lifting of the uniform sharp-window charge.
The general capacity extension is proved here; concrete short-map applications are paper-only.
-/

theorem past_shift (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t k : Int) (d : Nat) :
    past e (t+k*p) d = past e t d := by
  unfold past
  apply List.map_congr_left
  intro i _
  have heq : t+k*p-((i+1 : Nat) : Int) = (t-((i+1 : Nat) : Int))+k*p := by omega
  rw [heq, LagElevenPeriodic.e_shift e p hper]

theorem p2_shift (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t k : Int) (d : Nat) :
    ShortPeriodicSupply.P2 e (t+k*p) d ↔ ShortPeriodicSupply.P2 e t d := by
  rw [← past_p2_iff, ← past_p2_iff, past_shift e p hper]

theorem leading_shift (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t k : Int) (m : Nat)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true) :
    ∀ i, i < m → e ((t+k*p)-((i+1 : Nat) : Int)) = true := by
  intro i hi
  have heq : t+k*p-((i+1 : Nat) : Int) = (t-((i+1 : Nat) : Int))+k*p := by omega
  rw [heq, LagElevenPeriodic.e_shift e p hper]
  exact ha i hi

theorem lift_equal_mod (p : Nat) (a b : Int) (h : a % p = b % p) :
    ∃ k : Int, a = b+k*p := by
  have hdvd : (p : Int) ∣ a-b := Int.dvd_iff_emod_eq_zero.mpr
    ((Int.emod_eq_emod_iff_emod_sub_eq_zero).mp h)
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  rw [Int.mul_comm] at hk
  omega

/-- Equal sharp charges modulo p imply equal source phases, at every period. -/
theorem sharp_charge_mod_injective (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t u : Int) (m n : Nat)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (ht : ShortPeriodicSupply.P2 e t (4*m-1))
    (hu : ShortPeriodicSupply.P2 e u (4*n-1))
    (heq : (t-m-2) % p = (u-n-2) % p) : t % p = u % p := by
  obtain ⟨k, hk⟩ := lift_equal_mod p (t-m-2) (u-n-2) heq
  have hau' := leading_shift e p hper u k n hau
  have hu' := (p2_shift e p hper u k (4*n-1)).mpr hu
  have htime := sharp_charge_injective e t (u+k*p) m n hm hn hat hau' ht hu'
    (by omega)
  rw [htime]
  simp [Int.add_emod, Int.mul_emod]

/-- Every sharp charge is an S phase, including periods shorter than its lag. -/
theorem sharp_charge_is_S (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (m : Nat) (hm : 3 ≤ m)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hp : ShortPeriodicSupply.P2 e t (4*m-1)) :
    e ((t-m-2) % p) = false := by
  have hs := stream_sharp_S_block e t m hm ha hp 1 (by omega)
  have hpos : t-((m+1+1 : Nat) : Int) = t-m-2 := by omega
  rw [hpos] at hs
  have hd := Int.ediv_mul_add_emod (t-m-2) (p : Int)
  have heq : t-m-2 = (t-m-2) % p + ((t-m-2)/p)*p := by omega
  rw [heq, LagElevenPeriodic.e_shift e p hper] at hs
  exact hs

/-- The short and sharp images are disjoint modulo p. The short rule's
lag-3 convention is stated as an exact local offset, as in phi7/phi11. -/
theorem sharp_short_mod_disjoint (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t u : Int) (m L d j : Nat)
    (hm : 3 ≤ m) (hL : L+1 ≤ m)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hp : ShortPeriodicSupply.P2 e t (4*m-1))
    (hj : 1 ≤ j) (hjL : j ≤ L) (hd : d ≤ L)
    (hcur : e u = true) (hshort : ShortPeriodicSupply.P2 e u d)
    (hlag3 : ShortPeriodicSupply.P2 e u 3 → j = 3) :
    (u-j) % p ≠ (t-m-2) % p := by
  intro heq
  obtain ⟨k, hk⟩ := lift_equal_mod p (t-m-2) (u-j) heq.symm
  have hcur' : e (u+k*p) = true := by
    rw [LagElevenPeriodic.e_shift e p hper]
    exact hcur
  have hshort' := (p2_shift e p hper u k d).mpr hshort
  have hlag3' : ShortPeriodicSupply.P2 e (u+k*p) 3 → j = 3 :=
    fun h => hlag3 ((p2_shift e p hper u k 3).mp h)
  exact sharp_protected_charge e t (u+k*p) m L d j hm hL ha hp hj hjL hd
    hcur' hshort' hlag3' (by omega)

def phase (p : Nat) (t : Int) : Nat := (t % p).toNat

theorem phase_cast (p : Nat) (hp : 0 < p) (t : Int) :
    (phase p t : Int) = t % p := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg t (by omega))

theorem phase_lt (p : Nat) (hp : 0 < p) (t : Int) : phase p t < p := by
  have hc := phase_cast p hp t
  have ht := Int.emod_lt_of_pos t (show (0 : Int) < p by omega)
  omega

theorem phase_eq_mod (p : Nat) (hp : 0 < p) (t u : Int)
    (h : phase p t = phase p u) : t % p = u % p := by
  have ht := phase_cast p hp t
  have hu := phase_cast p hp u
  omega

/-- General finite capacity extension. U and Q are distinct phase lists;
the hypotheses give exactly the old short injection and the sharp-window
conditions. There is no assumed injection, capacity, or matching for Q. -/
theorem periodic_capacity_extension (e : Int → Bool) (p L : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (hp : 0 < p)
    (U Q : List Nat) (run off : Nat → Nat)
    (hUnodup : U.Nodup) (hQnodup : Q.Nodup)
    (hUrange : ∀ u, u ∈ U → u < p) (hQrange : ∀ t, t ∈ Q → t < p)
    (hUA : ∀ u, u ∈ U → e u = true)
    (hUsupply : ∀ u, u ∈ U → ∃ d : Nat, d ≤ L ∧ ShortPeriodicSupply.P2 e u d)
    (hOff : ∀ u, u ∈ U → 1 ≤ off u ∧ off u ≤ L ∧
      (ShortPeriodicSupply.P2 e u 3 → off u = 3))
    (hUS : ∀ u, u ∈ U → e (phase p ((u : Int)-off u)) = false)
    (hUinj : ∀ u v, u ∈ U → v ∈ U →
      phase p ((u : Int)-off u) = phase p ((v : Int)-off v) → u = v)
    (hRun : ∀ t, t ∈ Q → 3 ≤ run t ∧ L+1 ≤ run t ∧
      (∀ i, i < run t → e ((t : Int)-((i+1 : Nat) : Int)) = true) ∧
      ShortPeriodicSupply.P2 e t (4*run t-1)) :
    U.length + Q.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  let f := fun u : Nat => phase p ((u : Int)-off u)
  let g := fun t : Nat => phase p ((t : Int)-run t-2)
  have hfn : (U.map f).Nodup := LagElevenPeriodic.nodup_map_of_inj hUnodup hUinj
  have hgn : (Q.map g).Nodup := by
    apply LagElevenPeriodic.nodup_map_of_inj hQnodup
    intro t u ht hu heq
    have htR := hRun t ht
    have huR := hRun u hu
    have hmod := phase_eq_mod p hp ((t : Int)-run t-2) ((u : Int)-run u-2) heq
    have htumod := sharp_charge_mod_injective e p hper t u (run t) (run u)
      htR.1 huR.1 htR.2.2.1 huR.2.2.1 htR.2.2.2 huR.2.2.2 hmod
    have htlt := hQrange t ht
    have hult := hQrange u hu
    rw [Int.emod_eq_of_lt (by omega) (by omega),
      Int.emod_eq_of_lt (by omega) (by omega)] at htumod
    omega
  have hdisj : ∀ a, a ∈ U.map f → a ∉ Q.map g := by
    intro a ha hb
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    obtain ⟨t, ht, heq⟩ := List.mem_map.mp hb
    have hmod := phase_eq_mod p hp ((u : Int)-off u) ((t : Int)-run t-2) heq.symm
    have htR := hRun t ht
    obtain ⟨d, hd, hsup⟩ := hUsupply u hu
    have ho := hOff u hu
    exact sharp_short_mod_disjoint e p hper t u (run t) L d (off u)
      htR.1 htR.2.1 htR.2.2.1 htR.2.2.2 ho.1 ho.2.1 hd (hUA u hu)
      hsup ho.2.2 hmod
  have hnodup := LagElevenPeriodic.nodup_append hfn hgn hdisj
  have hsubset : U.map f ++ Q.map g ⊆ LagElevenPeriodic.subPhases e 0 p := by
    intro y hy
    apply (LagElevenPeriodic.mem_subPhases e 0 p y).mpr
    rcases List.mem_append.mp hy with hU | hQ
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hU
      refine ⟨phase_lt p hp _, ?_⟩
      simpa [f] using hUS u hu
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hQ
      have htR := hRun t ht
      have hs := sharp_charge_is_S e p hper t (run t) htR.1 htR.2.2.1 htR.2.2.2
      refine ⟨phase_lt p hp _, ?_⟩
      simpa [g, phase_cast p hp] using hs
  have hlen := hnodup.length_le_of_subset hsubset
  simpa using hlen

end Recaman.SharpPeriodicSupply
