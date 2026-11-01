import Recaman.LocalParitySupply
import Recaman.ParityPeriodicSupply

namespace Recaman.LocalParityPeriodic

open LeadingRunSupply LocalParitySupply SharpPeriodicSupply
open ParityPeriodicSupply (chargePhase)

/-! All-lag capacity for locally parity-clean windows in arbitrary periodic words. -/

theorem charge_formula (p : Nat) (t : Int) (k : Nat) :
    chargePhase p t (8*k+3) = phase p (t-4*k-3) := by
  have hdiv : (8*k+3+3)/2 = 4*k+3 := by omega
  unfold chargePhase
  rw [hdiv]
  congr 1
  omega

theorem clean_shift (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t z : Int) (d : Nat)
    (ha : EvenBackA e t d) : EvenBackA e (t+z*p) d := by
  intro i hi hid heven
  have htime : t+z*p-(i : Int) = (t-i)+z*p := by omega
  rw [htime,LagElevenPeriodic.e_shift e p hper]
  exact ha i hi hid heven

theorem charge_is_S (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d : Nat)
    (ha : EvenBackA e t d) (hP : ShortPeriodicSupply.P2 e t d) :
    e (chargePhase p t d) = false := by
  obtain ⟨k,rfl,hA,hS⟩ := local_P2_necessary e t d ha hP
  rw [charge_formula,phase_cast p hp]
  have h := local_charge_S e t k hS
  let q := t-4*(k : Int)-3
  have htime : q = q % p+(q/p)*p := by have := Int.ediv_mul_add_emod q (p : Int); omega
  change e q = false at h
  rw [htime,LagElevenPeriodic.e_shift e p hper] at h
  exact h

theorem charge_mod_injective (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t u : Int) (d d₂ : Nat)
    (hat : EvenBackA e t d) (hau : EvenBackA e u d₂)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u d₂)
    (heq : chargePhase p t d = chargePhase p u d₂) : t % p = u % p := by
  obtain ⟨k,rfl,hkA,hkS⟩ := local_P2_necessary e t d hat htP
  obtain ⟨l,rfl,hlA,hlS⟩ := local_P2_necessary e u d₂ hau huP
  rw [charge_formula,charge_formula] at heq
  have hmod := phase_eq_mod p hp (t-4*k-3) (u-4*l-3) heq
  obtain ⟨z,hz⟩ := lift_equal_mod p _ _ hmod
  have hlA' : e (u+z*p-((2*l+1 : Nat) : Int)) = true := by
    have htime : u+z*p-((2*l+1 : Nat) : Int) = (u-((2*l+1 : Nat) : Int))+z*p := by omega
    rw [htime,LagElevenPeriodic.e_shift e p hper]
    exact hlA
  have hlS' : ∀ j : Nat, j ≤ 4*l+1 → j ≠ l →
      e (u+z*p-((2*j+1 : Nat) : Int)) = false := by
    intro j hj hjl
    have htime : u+z*p-((2*j+1 : Nat) : Int) = (u-((2*j+1 : Nat) : Int))+z*p := by omega
    rw [htime,LagElevenPeriodic.e_shift e p hper]
    exact hlS j hj hjl
  have htu := (local_charge_injective e t (u+z*p) k l hkA hkS hlA' hlS' (by omega)).1
  rw [htu]
  simp [Int.add_emod]

/-- No global parity premise is present: each counted P2 witness has its own
local fixed-A offsets, and witnesses of either parity coexist. -/
theorem periodic_clean_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x)
    (U : List Nat) (hUnodup : U.Nodup) (hUrange : ∀ u, u ∈ U → u < p)
    (hSupply : ∀ u, u ∈ U → ∃ d : Nat, ShortPeriodicSupply.P2 e u d ∧ EvenBackA e u d) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  classical
  let lag := fun u : Nat => if hu : u ∈ U then Classical.choose (hSupply u hu) else 0
  have hlag : ∀ u, u ∈ U → ShortPeriodicSupply.P2 e u (lag u) ∧ EvenBackA e u (lag u) := by
    intro u hu
    dsimp [lag]
    rw [dif_pos hu]
    exact Classical.choose_spec (hSupply u hu)
  let f := fun u : Nat => chargePhase p u (lag u)
  have hinj : ∀ u v, u ∈ U → v ∈ U → f u = f v → u = v := by
    intro u v hu hv heq
    have hmod := charge_mod_injective e p hp hper u v (lag u) (lag v)
      (hlag u hu).2 (hlag v hv).2 (hlag u hu).1 (hlag v hv).1 heq
    have hult := hUrange u hu
    have hvlt := hUrange v hv
    rw [Int.emod_eq_of_lt (by omega) (by omega),
      Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hnodup := LagElevenPeriodic.nodup_map_of_inj hUnodup hinj
  have hsub : U.map f ⊆ LagElevenPeriodic.subPhases e 0 p := by
    intro q hq
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hq
    apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
    refine ⟨phase_lt p hp _, ?_⟩
    simpa [f] using charge_is_S e p hp hper u (lag u) (hlag u hu).2 (hlag u hu).1
  have hlen := hnodup.length_le_of_subset hsub
  simpa using hlen

end Recaman.LocalParityPeriodic
