import Recaman.EventualPeriodicSupply

namespace Recaman.PeriodicTailRepresentation

open LeadingRunSupply PositivePeriodLag EventualPeriodicSupply CanonicalSSFreeSupply

/-! Natural eventual periodicity is converted to an integer periodic word;
positive drift then gives the complete finite P2 cutoff. -/

def extension (f : Nat → Bool) (N p : Nat) (t : Int) : Bool :=
  f (N+((t-N) % (p : Int)).toNat)

theorem extension_periodic (f : Nat → Bool) (N p : Nat) (t : Int) :
    extension f N p (t+p) = extension f N p t := by
  have ht : t+(p : Int)-N=(t-N)+p := by omega
  simp [extension,ht]

theorem natural_period_iterate (f : Nat → Bool) (N p : Nat)
    (hper : ∀ n, N ≤ n → f (n+p)=f n) (n q : Nat) (hn : N ≤ n) :
    f (n+q*p)=f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : n+(q+1)*p=(n+q*p)+p := by grind
    rw [heq,hper _ (by omega),ih]

theorem extension_agrees (f : Nat → Bool) (N p : Nat) (_hp : 0 < p)
    (hper : ∀ n, N ≤ n → f (n+p)=f n) (n : Nat) (hn : N ≤ n) :
    extension f N p n = f n := by
  have hsub : (n : Int)-N=((n-N : Nat) : Int) := by omega
  have hdecomp : N+(n-N)%p+(n-N)/p*p=n := by
    have hd : (n-N)/p*p+(n-N)%p=n-N := by simpa [Nat.mul_comm] using Nat.div_add_mod (n-N) p
    omega
  have h := natural_period_iterate f N p hper (N+(n-N)%p) ((n-N)/p) (by omega)
  rw [hdecomp] at h
  simpa [extension,hsub,← Int.natCast_emod] using h.symm

theorem positive_period_P2_cutoff (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ t : Int, e (t+p)=e t) (hS : 1 ≤ mass (past e 0 p))
    (t : Int) (d : Nat) (hP : ShortPeriodicSupply.P2 e t d) :
    0 < d ∧ d < p*(p+1) := by
  have hm := ((past_p2_iff e t d).mpr hP).1
  have hdecomp := periodic_past_blocks e p hper t (d/p) (d%p)
  have hd : d/p*p+d%p=d := by simpa [Nat.mul_comm] using Nat.div_add_mod d p
  rw [hd] at hdecomp
  rw [hdecomp,mass_append,blocks_mass] at hm
  have hs : 1 ≤ mass (past e t p) := by rw [period_mass_constant e p hp hper]; exact hS
  have hr := (mass_bounds (past e t (d%p))).1
  have hlen : (past e t (d%p)).length = d%p := by simp [past]
  rw [hlen] at hr
  have hprod := Int.mul_le_mul_of_nonneg_left hs (Int.natCast_nonneg (d/p))
  have hrem : d%p < p := Nat.mod_lt _ hp
  have hq : d/p ≤ p := by omega
  have hmul := Nat.mul_le_mul_right p hq
  have hpos : 0 < d := by
    by_cases hz : d=0
    · subst d
      have hm0 := ((past_p2_iff e t 0).mpr hP).1
      simp [past] at hm0
    · omega
  refine ⟨hpos,?_⟩
  simp only [Nat.mul_add,Nat.mul_one]
  omega

/-- The statement uses only the actual natural tail's periodicity and mass,
with no pre-existing integer extension or P2 assumption. -/
theorem canonical_natural_eventual_supply (N p : Nat) (hp : 0 < p)
    (hper : ∀ n : Nat, N ≤ n → canonicalSign ((n+p : Nat) : Int)=canonicalSign n)
    (hS : 1 ≤ mass (past canonicalSign ((N+p : Nat) : Int) p)) :
    let e := extension (fun n : Nat => canonicalSign n) N p
    ∀ t : Int, e t = true → ∃ d : Nat, 0 < d ∧ d < p*(p+1) ∧ ShortPeriodicSupply.P2 e t d := by
  let e := extension (fun n : Nat => canonicalSign n) N p
  have he : ∀ n : Nat, N ≤ n → canonicalSign n = e n := by
    intro n hn
    exact (extension_agrees (fun n : Nat => canonicalSign n) N p hp hper n hn).symm
  have hep : ∀ t : Int, e (t+p)=e t := extension_periodic _ N p
  have hw := past_agrees e N (N+p) p he (by omega) (by omega)
  have hmass := period_mass_constant e p hp hep (N+p : Nat)
  have hs : 1 ≤ mass (past e 0 p) := by rw [hw] at hS; omega
  change ∀ t : Int, e t = true → ∃ d : Nat, 0 < d ∧ d < p*(p+1) ∧ ShortPeriodicSupply.P2 e t d
  intro t hA
  obtain ⟨d,hd,_,hP⟩ := every_A_phase_has_P2 e N p hp he hep hs t hA
  exact ⟨d,hd,(positive_period_P2_cutoff e p hp hep hs t d hP).2,hP⟩

def balancedCounter (t : Int) : Bool := decide (2 ≤ t%4)

theorem balancedCounter_periodic (t : Int) : balancedCounter (t+4)=balancedCounter t := by
  simp [balancedCounter]

theorem balanced_unbounded_P2 (q : Nat) :
    mass (past balancedCounter 0 4)=0 ∧ ShortPeriodicSupply.P2 balancedCounter 0 (4*q+3) := by
  have hb : past balancedCounter 0 4 = [true,true,false,false] := by decide
  have hv : past balancedCounter 0 3 = [true,true,false] := by decide
  have h := periodic_past_blocks balancedCounter 4 balancedCounter_periodic 0 q 3
  have heq : q*4+3=4*q+3 := by omega
  rw [heq,hb,hv] at h
  have hm := blocks_mass [true,true,false,false] q
  have hM := blocks_moment [true,true,false,false] q
  have hl := blocks_length [true,true,false,false] q
  simp [mass_cons,ShortPeriodicSupply.sign,moment] at hm hM hl
  constructor
  · rw [hb]; decide
  · apply (past_p2_iff balancedCounter 0 (4*q+3)).mp
    rw [h]
    constructor
    · simp [mass_append,hm,mass_cons,ShortPeriodicSupply.sign]
    · rw [moment_append,hl]
      simp [mass_cons,ShortPeriodicSupply.sign,moment]
      omega

end Recaman.PeriodicTailRepresentation
