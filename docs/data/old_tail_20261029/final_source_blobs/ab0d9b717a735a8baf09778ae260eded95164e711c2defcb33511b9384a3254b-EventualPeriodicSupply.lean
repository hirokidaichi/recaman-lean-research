import Recaman.PositivePeriodLag
import Recaman.OrbitBounds

namespace Recaman.EventualPeriodicSupply

open LeadingRunSupply PositivePeriodLag FiniteP2Semantics CanonicalSSFreeSupply

/-! Canonical positive-drift eventual-periodic reduction. The finite original
history and nonpositive-candidate cases are discharged, not assumed away. -/

theorem blocks_growth_arithmetic (p r q R S B s C n : Int)
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hpR : p ≤ R) (hrR : r ≤ R)
    (hq : 4*R+4 ≤ q) (hS : 1 ≤ S) (hB : 2*B ≤ p*(p+1))
    (hs : -r ≤ s) (hC : 2*C ≤ r*(r+1)) (hn : q*p+r+1 ≤ n) :
    2*q ≤ 2*n*(q*S+s-1)-(2*q*B+p*S*q*(q-1)+2*q*p*s+2*C) := by
  have hq0 : 0 ≤ q := by omega
  let h := n-(q*p+r+1)
  have hh : 0 ≤ h := by dsimp [h]; omega
  have hn' : n = q*p+r+1+h := by dsimp [h]; omega
  have hcoef : 0 ≤ 2*n-p*(q-1) := by
    have hprod := Int.mul_nonneg (show 0 ≤ p by omega) (show 0 ≤ q+1 by omega)
    have heq : 2*n-p*(q-1) = p*(q+1)+2*(r+1+h) := by grind
    omega
  have h1 := Int.mul_nonneg (Int.mul_nonneg hq0 hcoef) (show 0 ≤ S-1 by omega)
  have h2 := Int.mul_nonneg hq0 (show 0 ≤ p*(p+1)-2*B by omega)
  have h3 := Int.mul_nonneg (show 0 ≤ 2*(n-q*p) by omega) (show 0 ≤ s+r by omega)
  have h4 : 0 ≤ r*(r+1)-2*C := by omega
  let T := p*q*(q-p-2)+2*q*(r+1)-(r+1)*(3*r+2)+2*h*(q-r-1)
  have hdecomp :
      2*n*(q*S+s-1)-(2*q*B+p*S*q*(q-1)+2*q*p*s+2*C) =
      q*(2*n-p*(q-1))*(S-1)+q*(p*(p+1)-2*B)+
      2*(n-q*p)*(s+r)+(r*(r+1)-2*C)+T := by dsimp [T]; grind
  have hneg := Int.mul_le_mul (show r+1 ≤ R+1 by omega)
    (show 3*r+2 ≤ 3*R+2 by omega) (show 0 ≤ 3*r+2 by omega) (show 0 ≤ R+1 by omega)
  have hbig := Int.mul_le_mul (show R+1 ≤ q by omega)
    (show 3*R+2 ≤ q-p-2 by omega) (show 0 ≤ 3*R+2 by omega) hq0
  have hbigp := Int.mul_nonneg (show 0 ≤ p-1 by omega)
    (Int.mul_nonneg hq0 (show 0 ≤ q-p-2 by omega))
  have hpos1 := Int.mul_nonneg hq0 hr
  have hpos2 := Int.mul_nonneg hh (show 0 ≤ q-r-1 by omega)
  have heq : T-2*q = (p-1)*(q*(q-p-2))+
      (q*(q-p-2)-(R+1)*(3*R+2))+
      ((R+1)*(3*R+2)-(r+1)*(3*r+2))+2*(q*r)+2*(h*(q-r-1)) := by dsimp [T]; grind
  omega

theorem repeated_word_candidate_growth (b v : List Bool) (q R : Nat) (n : Int)
    (hb : 0 < b.length) (hpR : b.length ≤ R) (hvR : v.length ≤ R)
    (hq : 4*R+4 ≤ q) (hS : 1 ≤ mass b)
    (hn : ((blocks b q ++ v).length : Int) < n) :
    (q : Int) ≤ n*(mass (blocks b q ++ v)-1)-moment (blocks b q ++ v) := by
  have hM := blocks_moment b q
  have hn' : (q : Int)*b.length+v.length+1 ≤ n := by
    simp only [List.length_append,blocks_length,Int.natCast_add,Int.natCast_mul] at hn
    omega
  have h := blocks_growth_arithmetic b.length v.length q R (mass b) (moment b)
    (mass v) (moment v) n (by omega) (by omega) (by omega) (by omega)
    (by omega) hS (moment_upper b) (mass_bounds v).1 (moment_upper v) hn'
  simp only [mass_append,blocks_mass,moment_append,blocks_length,Int.natCast_mul]
  grind

theorem period_mass_succ (e : Int → Bool) (p : Nat) (_hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) :
    mass (past e (t+1) p) = mass (past e t p) := by
  have hleft := ParitySupply.past_succ e (t+1) p
  have hright := past_append e (t+1) p 1
  have ht : t+1-1=t := by omega
  rw [ht] at hleft
  have he := hper (t-p)
  have hepos : t-(p : Int)+p=t := by omega
  rw [hepos] at he
  have hrightmass := congrArg mass hright
  have hleftmass := congrArg mass hleft
  simp only [mass_append,mass_cons] at hrightmass hleftmass
  have hlast : mass (past e (t+1-p) 1) = ShortPeriodicSupply.sign (e t) := by
    have hs : t+1-(p : Int)-1=t-p := by omega
    simp [past,hs,← he]
  rw [hlast] at hrightmass
  omega

theorem period_mass_constant (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) :
    mass (past e t p) = mass (past e 0 p) := by
  have hn (n : Nat) : mass (past e n p) = mass (past e 0 p) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have h := period_mass_succ e p hp hper n
      simpa only [Int.natCast_add,Int.cast_ofNat_Int] using h.trans ih
  have hmod0 : 0 ≤ t % (p : Int) := Int.emod_nonneg _ (by omega)
  have hcast : ((t % (p : Int)).toNat : Int) = t % p := Int.toNat_of_nonneg hmod0
  have h := hn (t % (p : Int)).toNat
  rw [hcast] at h
  have ht : t % (p : Int)+(t/p)*p=t := by have hh:=Int.ediv_mul_add_emod t (p : Int); omega
  have hs := SharpPeriodicSupply.past_shift e p hper (t%p) (t/p) p
  rw [ht] at hs
  rw [hs]
  exact h

/-- Window equality requires every transition to be after the preperiod. -/
theorem past_agrees (e : Int → Bool) (N t d : Nat)
    (he : ∀ n : Nat, N ≤ n → canonicalSign n = e n)
    (hd : d ≤ t) (hN : N ≤ t-d) : past canonicalSign t d = past e t d := by
  unfold past
  apply List.map_congr_left
  intro i hi
  have hi' : i < d := List.mem_range.mp hi
  have hpos : (t : Int)-((i+1 : Nat) : Int) = ((t-(i+1) : Nat) : Int) := by omega
  rw [hpos]
  exact he _ (by omega)

theorem canonical_whole_prefix_value (t : Nat) :
    (a t : Int) = ((t+1 : Nat) : Int)*mass (past canonicalSign t t)-moment (past canonicalSign t t) := by
  have h := window_prefix_identities canonicalSign 0 t
  have hv := canonical_value_prefix t
  simp only [Nat.zero_add,ShortPeriodicSupply.signSum,weightedPrefix] at h
  have hcast : ((t+1 : Nat) : Int) = (t : Int)+1 := by omega
  rw [hcast]
  grind

theorem canonical_prefix_blocks (e : Int → Bool) (N t p q : Nat)
    (he : ∀ n : Nat, N ≤ n → canonicalSign n = e n)
    (hper : ∀ x : Int, e (x+p) = e x) (ht : N+q*p ≤ t) :
    past canonicalSign t t = blocks (past e t p) q ++
      past canonicalSign ((t : Int)-(q*p : Nat)) (t-q*p) := by
  have hd : q*p+(t-q*p)=t := by omega
  have h := past_append canonicalSign t (q*p) (t-q*p)
  rw [hd] at h
  rw [h,past_agrees e N t (q*p) he (by omega) (by omega)]
  have hblock := periodic_past_blocks e p hper t q 0
  have hz : past e (t : Int) 0 = [] := rfl
  simp only [Nat.add_zero,hz,List.append_nil] at hblock
  rw [hblock]

theorem canonical_candidate_growth (e : Int → Bool) (N p t : Nat) (hp : 0 < p)
    (he : ∀ n : Nat, N ≤ n → canonicalSign n = e n)
    (hper : ∀ x : Int, e (x+p) = e x)
    (hS : 1 ≤ mass (past e 0 p)) (ht : N ≤ t)
    (hq : 4*(N+p)+4 ≤ (t-N)/p) :
    (((t-N)/p : Nat) : Int) ≤ (a t : Int)-((t+1 : Nat) : Int) := by
  let q := (t-N)/p
  have hdiv : q*p+(t-N)%p=t-N := by
    simpa [q,Nat.mul_comm] using Nat.div_add_mod (t-N) p
  have hr : (t-N)%p < p := Nat.mod_lt _ hp
  have htq : N+q*p ≤ t := by omega
  have hword := canonical_prefix_blocks e N t p q he hper htq
  have hlen : (blocks (past e t p) q ++
      past canonicalSign ((t : Int)-(q*p : Nat)) (t-q*p)).length = t := by
    rw [← hword]; simp [past]
  have hpos := period_mass_constant e p hp hper t
  have hs : 1 ≤ mass (past e t p) := by omega
  have h := repeated_word_candidate_growth (past e t p)
    (past canonicalSign ((t : Int)-(q*p : Nat)) (t-q*p)) q (N+p) (t+1 : Nat)
    (by simpa [past] using hp) (by simp [past]) (by simp [past]; omega)
    hq hs (by rw [hlen]; omega)
  rw [← hword] at h
  have hv := canonical_whole_prefix_value t
  have heq : ((t+1 : Nat) : Int)*(mass (past canonicalSign t t)-1)-
      moment (past canonicalSign t t) = (a t : Int)-((t+1 : Nat) : Int) := by grind
  rw [heq] at h
  exact h

/-- Every sufficiently late actual A has a supplier inside the periodic tail,
and that supplier is P2. The old finite history is eliminated by growth. -/
theorem late_A_has_P2 (e : Int → Bool) (N p t : Nat) (hp : 0 < p)
    (he : ∀ n : Nat, N ≤ n → canonicalSign n = e n)
    (hper : ∀ x : Int, e (x+p) = e x)
    (hS : 1 ≤ mass (past e 0 p)) (ht : N ≤ t)
    (hq : upperTri N+4*(N+p)+5 ≤ (t-N)/p)
    (hlate : (lagBound p : Int)*(lagBound p+4) < 4*((t+1 : Nat) : Int))
    (hA : e t = true) :
    ∃ d : Nat, 0 < d ∧ d ≤ t-N ∧ d < lagBound p ∧ ShortPeriodicSupply.P2 e t d := by
  have hg := canonical_candidate_growth e N p t hp he hper hS ht (by omega)
  have hpos : t+1 < a t := by omega
  have hAcan : canonicalSign t = true := (he t ht).trans hA
  rw [canonicalSign_nat] at hAcan
  have hnot : ¬ CanSubtract (t+1) (stateAt t) := of_decide_eq_true hAcan
  have hseen : a t-(t+1) ∈ valuesThrough t := by
    by_cases hm : a t-(t+1) ∈ valuesThrough t
    · exact hm
    · exact False.elim (hnot ⟨hpos,hm⟩)
  obtain ⟨u,hu,huv⟩ := mem_valuesThrough_iff.mp hseen
  have hNu : N ≤ u := by
    by_cases hle : N ≤ u
    · exact hle
    · have hb := Nat.le_trans (a_le_upperTri u) (upperTri_mono (show u ≤ N by omega))
      omega
  have hd : 0 < t-u := by
    by_cases heq : u = t
    · rw [heq] at huv; omega
    · omega
  have hv : a (u+(t-u)) = a u+(u+(t-u))+1 := by
    have htime : u+(t-u)=t := by omega
    rw [htime]
    omega
  have hc := ShortBlockerRigidity.canonical_collision_moment u (t-u) hv
  have htime : u+(t-u)=t := by omega
  rw [htime] at hc
  have hw := past_agrees e N t (t-u) he (by omega) (by omega)
  rw [hw] at hc
  have hs : 1 ≤ mass (past e t p) := by rw [period_mass_constant e p hp hper]; exact hS
  have hP := late_periodic_collision_P2 e p hp hper t (t-u) (t+1 : Nat)
    hs (by omega) hc hlate
  have hbound := periodic_collision_lag_bound e p hp hper t (t-u) (t+1 : Nat)
    hs (by omega) hc
  exact ⟨t-u,hd,by omega,hbound,hP⟩

def threshold (N p : Nat) : Nat :=
  N+(upperTri N+4*(N+p)+5)*p+lagBound p*(lagBound p+4)+1

/-- Canonical version of the positive-drift eventual-periodic reduction.
Every A phase requires P2; neither full supply nor its lag is assumed. -/
theorem every_A_phase_has_P2 (e : Int → Bool) (N p : Nat) (hp : 0 < p)
    (he : ∀ n : Nat, N ≤ n → canonicalSign n = e n)
    (hper : ∀ x : Int, e (x+p) = e x)
    (hS : 1 ≤ mass (past e 0 p)) (t : Int) (hA : e t = true) :
    ∃ d : Nat, 0 < d ∧ d < lagBound p ∧ ShortPeriodicSupply.P2 e t d := by
  let r : Nat := (t % (p : Int)).toNat
  let K : Nat := threshold N p+1
  let T : Nat := r+K*p
  have hr0 : 0 ≤ t % (p : Int) := Int.emod_nonneg _ (by omega)
  have hrcast : (r : Int) = t % p := Int.toNat_of_nonneg hr0
  have hT : threshold N p ≤ T := by
    have hmul := Nat.le_mul_of_pos_right K hp
    have hK : threshold N p ≤ K := by dsimp [K]; omega
    have hT0 : K*p ≤ T := by dsimp [T]; omega
    omega
  have htN : N ≤ T := by dsimp [threshold] at hT; omega
  have hq : upperTri N+4*(N+p)+5 ≤ (T-N)/p := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    dsimp [threshold] at hT
    omega
  have hlate : (lagBound p : Int)*(lagBound p+4) < 4*((T+1 : Nat) : Int) := by
    have hnat : lagBound p*(lagBound p+4) < T := by dsimp [threshold] at hT; omega
    have hcast : ((lagBound p*(lagBound p+4) : Nat) : Int) =
        (lagBound p : Int)*(lagBound p+4) := by simp
    omega
  have ht : t = (r : Int)+(t/p)*p := by
    have hh := Int.ediv_mul_add_emod t (p : Int)
    omega
  have hAr : e r = true := by
    have h := LagElevenPeriodic.e_shift e p hper (t/p) r
    rw [← ht] at h
    exact h.symm.trans hA
  have hTc : (T : Int) = (r : Int)+(K : Int)*p := by simp [T]
  have hAT : e T = true := by
    rw [hTc,LagElevenPeriodic.e_shift e p hper]
    exact hAr
  obtain ⟨d,hd,_,hbound,hP⟩ := late_A_has_P2 e N p T hp he hper hS htN hq hlate hAT
  rw [hTc] at hP
  have hPr := (SharpPeriodicSupply.p2_shift e p hper r K d).mp hP
  refine ⟨d,hd,hbound,?_⟩
  rw [ht]
  exact (SharpPeriodicSupply.p2_shift e p hper r (t/p) d).mpr hPr

end Recaman.EventualPeriodicSupply
