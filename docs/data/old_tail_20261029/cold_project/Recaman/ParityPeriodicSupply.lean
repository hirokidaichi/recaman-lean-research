import Recaman.ParitySupply
import Recaman.SharpPeriodicSupply

namespace Recaman.ParityPeriodicSupply

open ParitySupply SharpPeriodicSupply

/-! Full all-lag periodic capacity with a fixed-A parity. -/

def chargePhase (p : Nat) (t : Int) (d : Nat) : Nat := phase p (t-((d+3)/2 : Nat))

theorem charge_formula (p : Nat) (n : Int) (k : Nat) :
    chargePhase p (2*n+1) (8*k+3) = phase p (2*(n-2*k-1)) := by
  have hdiv : (8*k+3+3)/2 = 4*k+3 := by omega
  unfold chargePhase
  rw [hdiv]
  congr 1
  omega

theorem charge_is_S (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x)
    (hfixed : ∀ n : Int, e (2*n+1) = true) (t : Int) (d : Nat)
    (hP : ShortPeriodicSupply.P2 e t d) : e (chargePhase p t d) = false := by
  obtain ⟨n,rfl⟩ := supplied_phase_is_odd e hfixed t d hP
  obtain ⟨k,rfl,hA,hS⟩ := odd_P2_necessary e hfixed n d hP
  rw [charge_formula, phase_cast p hp]
  have hcharge := witness_charge_is_S (evenSigns e) n k hS
  change e (2*(n-2*k-1)) = false at hcharge
  let q := 2*(n-2*(k : Int)-1)
  have htime : q = q % p+(q/p)*p := by have := Int.ediv_mul_add_emod q (p : Int); omega
  change e q = false at hcharge
  rw [htime,LagElevenPeriodic.e_shift e p hper] at hcharge
  exact hcharge

/-- Equal charge phases force equal supplied source phases, even if either
lag wraps around the period. The period need not itself be even. -/
theorem charge_mod_injective (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x)
    (hfixed : ∀ n : Int, e (2*n+1) = true) (t u : Int) (d d₂ : Nat)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u d₂)
    (heq : chargePhase p t d = chargePhase p u d₂) : t % p = u % p := by
  obtain ⟨n,rfl⟩ := supplied_phase_is_odd e hfixed t d htP
  obtain ⟨m,rfl⟩ := supplied_phase_is_odd e hfixed u d₂ huP
  obtain ⟨k,rfl,hkA,hkS⟩ := odd_P2_necessary e hfixed n d htP
  obtain ⟨l,rfl,hlA,hlS⟩ := odd_P2_necessary e hfixed m d₂ huP
  rw [charge_formula,charge_formula] at heq
  have hmod := phase_eq_mod p hp (2*(n-2*k-1)) (2*(m-2*l-1)) heq
  obtain ⟨z,hz⟩ := lift_equal_mod p _ _ hmod
  let m' := n-2*(k : Int)+2*l
  have htime : 2*m'+1 = (2*m+1)+z*p := by dsimp [m']; omega
  have hP' : ShortPeriodicSupply.P2 e (2*m'+1) (8*l+3) := by
    rw [htime]
    exact (p2_shift e p hper (2*m+1) z (8*l+3)).mpr huP
  obtain ⟨l',hl',hlA',hlS'⟩ := odd_P2_necessary e hfixed m' (8*l+3) hP'
  have hll : l' = l := by omega
  subst l'
  have hnm := witness_charge_injective (evenSigns e) n m' k l hkA hkS hlA' hlS'
    (by dsimp [m']; omega)
  have htus : 2*n+1 = (2*m+1)+z*p := by rw [hnm.1]; exact htime
  rw [htus]
  simp [Int.add_emod]

/-- All supplied phases, with no lag restriction or long-run condition, have
an injective S charge. The fixed-A parity is an explicit essential premise. -/
theorem periodic_all_lag_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x)
    (hfixed : ∀ n : Int, e (2*n+1) = true)
    (U : List Nat) (hUnodup : U.Nodup) (hUrange : ∀ u, u ∈ U → u < p)
    (hSupply : ∀ u, u ∈ U → ∃ d : Nat, ShortPeriodicSupply.P2 e u d) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  classical
  let lag := fun u : Nat => if hu : u ∈ U then Classical.choose (hSupply u hu) else 0
  have hlag : ∀ u, u ∈ U → ShortPeriodicSupply.P2 e u (lag u) := by
    intro u hu
    dsimp [lag]
    rw [dif_pos hu]
    exact Classical.choose_spec (hSupply u hu)
  let f := fun u : Nat => chargePhase p u (lag u)
  have hinj : ∀ u v, u ∈ U → v ∈ U → f u = f v → u = v := by
    intro u v hu hv heq
    have hmod := charge_mod_injective e p hp hper hfixed u v (lag u) (lag v)
      (hlag u hu) (hlag v hv) heq
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
    simpa [f] using charge_is_S e p hp hper hfixed u (lag u) (hlag u hu)
  have hlen := hnodup.length_le_of_subset hsub
  simpa using hlen


def noParityStream (t : Int) : Bool := decide (3 ≤ t % 7)

/-- The same charge can be an A without the parity hypothesis, even for
an actual P2 window; this counterexample uses a wrapping lag. -/
theorem parity_premise_counterexample :
    ShortPeriodicSupply.P2 noParityStream 5 11 ∧
    chargePhase 7 5 11 = 5 ∧ noParityStream 5 = true ∧ noParityStream 1 = false := by
  unfold ShortPeriodicSupply.P2
  decide

end Recaman.ParityPeriodicSupply
