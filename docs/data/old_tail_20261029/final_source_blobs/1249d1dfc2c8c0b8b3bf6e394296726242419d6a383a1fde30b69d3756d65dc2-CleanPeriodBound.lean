import Recaman.LocalParityPeriodic

namespace Recaman.CleanPeriodBound

open LocalParitySupply LocalParityPeriodic

/-! Sharp bounds on the period of a clean P2 witness. The current-A
qualification is essential for the strongest uniform inequality. -/

theorem clean_oldest_S (e : Int → Bool) (t : Int) (d : Nat)
    (ha : EvenBackA e t d) (hP : ShortPeriodicSupply.P2 e t d) : e (t-d) = false := by
  obtain ⟨k,rfl,_,hS⟩ := local_P2_necessary e t d ha hP
  have h := hS (4*k+1) (by omega) (by omega)
  have hindex : 2*(4*k+1)+1 = 8*k+3 := by omega
  rwa [hindex] at h

theorem even_period_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (k : Nat)
    (hpeven : p % 2 = 0) (ha : EvenBackA e t (8*k+3))
    (hP : ShortPeriodicSupply.P2 e t (8*k+3)) : 6*k+4 ≤ p := by
  obtain ⟨l,hl,hA,hS⟩ := local_P2_necessary e t (8*k+3) ha hP
  have hlk : l = k := by omega
  subst l
  let N := p/2
  have hpN : p = 2*N := by dsimp [N]; omega
  have hN : 0 < N := by omega
  by_cases hsmall : N ≤ 3*k+1
  · have hS' := hS (k+N) (by omega) (by omega)
    have htime : t-((2*(k+N)+1 : Nat) : Int)+(p : Int) = t-((2*k+1 : Nat) : Int) := by omega
    have hshift := hper (t-((2*(k+N)+1 : Nat) : Int))
    rw [htime,hA,hS'] at hshift
    contradiction
  · omega

theorem odd_period_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d : Nat)
    (hpodd : p % 2 = 1) (ha : EvenBackA e t d)
    (hP : ShortPeriodicSupply.P2 e t d) : d ≤ p := by
  obtain ⟨k,rfl,hA,hS⟩ := local_P2_necessary e t d ha hP
  by_cases hk : k = 0
  · subst k
    by_cases hge : 3 ≤ p
    · omega
    · have hp1 : p = 1 := by omega
      have hs := hS 1 (by decide) (by decide)
      have hav := ha 2 (by decide) (by decide) (by decide)
      have ht : t-((2*1+1 : Nat) : Int)+(p : Int) = t-(2 : Nat) := by omega
      have h := hper (t-((2*1+1 : Nat) : Int))
      rw [ht,hav,hs] at h
      contradiction
  · by_cases hge : 8*k+3 ≤ p
    · exact hge
    · have hs : e (t-1) = false := by simpa using hS 0 (by omega) (by omega)
      have hav := ha (p+1) (by omega) (by omega) (by omega)
      have ht : t-((p+1 : Nat) : Int)+(p : Int) = t-1 := by omega
      have h := hper (t-((p+1 : Nat) : Int))
      rw [ht,hs,hav] at h
      contradiction

theorem clean_lag_lt_twice_period (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d : Nat)
    (ha : EvenBackA e t d) (hP : ShortPeriodicSupply.P2 e t d) : d < 2*p := by
  by_cases hpe : p % 2 = 0
  · obtain ⟨k,rfl,_,_⟩ := local_P2_necessary e t d ha hP
    have h := even_period_bound e p hp hper t k hpe ha hP
    omega
  · have hpo : p % 2 = 1 := by omega
    have h := odd_period_bound e p hp hper t d hpo ha hP
    omega

theorem odd_current_A_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d : Nat)
    (hpodd : p % 2 = 1) (hcur : e t = true) (ha : EvenBackA e t d)
    (hP : ShortPeriodicSupply.P2 e t d) : d+2 ≤ p := by
  have hle := odd_period_bound e p hp hper t d hpodd ha hP
  have hlast := clean_oldest_S e t d ha hP
  have hne : d ≠ p := by
    intro heq
    have h := hper (t-d)
    have ht : t-(d : Int)+(p : Int) = t := by omega
    rw [ht,hcur,hlast] at h
    contradiction
  obtain ⟨k,hd,_,_⟩ := local_P2_necessary e t d ha hP
  omega

/-- This coefficient and additive constant are attained for every k. -/
theorem sharp_current_A_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d : Nat)
    (hcur : e t = true) (ha : EvenBackA e t d)
    (hP : ShortPeriodicSupply.P2 e t d) : 3*d+7 ≤ 4*p := by
  by_cases hpe : p % 2 = 0
  · obtain ⟨k,rfl,_,_⟩ := local_P2_necessary e t d ha hP
    have h := even_period_bound e p hp hper t k hpe ha hP
    omega
  · have hpo : p % 2 = 1 := by omega
    have h := odd_current_A_bound e p hp hper t d hpo hcur ha hP
    omega

def sharpFamily (k : Nat) (t : Int) : Bool :=
  if t % 2 = 1 then true else decide (t % ((6*k+4 : Nat) : Int) = 0)

theorem sharpFamily_periodic (k : Nat) (t : Int) :
    sharpFamily k (t+((6*k+4 : Nat) : Int)) = sharpFamily k t := by
  have h2 : (t+((6*k+4 : Nat) : Int)) % 2 = t % 2 := by omega
  have hp : (t+((6*k+4 : Nat) : Int)) % ((6*k+4 : Nat) : Int) =
      t % ((6*k+4 : Nat) : Int) := by simp
  unfold sharpFamily
  rw [h2,hp]

theorem sharpFamily_odd (k : Nat) (n : Int) : sharpFamily k (2*n+1) = true := by
  have h : (2*n+1) % 2 = 1 := by omega
  simp [sharpFamily,h]

theorem sharpFamily_even (k : Nat) (n : Int) :
    sharpFamily k (2*n) = decide ((2*n) % ((6*k+4 : Nat) : Int) = 0) := by
  have h : (2*n) % 2 = 0 := by omega
  simp [sharpFamily,h]

theorem bounded_multiple_zero (p x : Int) (_hp : 0 < p)
    (hlo : -p < x) (hhi : x < p) (hmod : x % p = 0) : x = 0 := by
  by_cases hx : 0 ≤ x
  · rw [Int.emod_eq_of_lt hx hhi] at hmod
    exact hmod
  · have hxp : 0 ≤ x+p := by omega
    have hxplt : x+p < p := by omega
    have hm : (x+p) % p = x % p := by simp
    rw [Int.emod_eq_of_lt hxp hxplt,hmod] at hm
    omega

theorem sharpFamily_clean (k : Nat) :
    EvenBackA (sharpFamily k) (2*(k : Int)+1) (8*k+3) := by
  intro i hi hid heven
  have ht : 2*(k : Int)+1-(i : Int) = 2*((k : Int)-((i/2 : Nat) : Int))+1 := by omega
  rw [ht]
  exact sharpFamily_odd k _

theorem sharpFamily_P2 (k : Nat) :
    ShortPeriodicSupply.P2 (sharpFamily k) (2*(k : Int)+1) (8*k+3) := by
  apply local_P2_sufficient (sharpFamily k) (2*(k : Int)+1) k (sharpFamily_clean k)
  · have ht : 2*(k : Int)+1-((2*k+1 : Nat) : Int) = 0 := by omega
    rw [ht]
    simp [sharpFamily]
  · intro j hj hjk
    have ht : 2*(k : Int)+1-((2*j+1 : Nat) : Int) = 2*((k : Int)-j) := by omega
    rw [ht,sharpFamily_even]
    apply decide_eq_false
    intro hm
    have hx := bounded_multiple_zero ((6*k+4 : Nat) : Int) (2*((k : Int)-j))
      (by omega) (by omega) (by omega) hm
    omega

/-- The lag is unique among all possible lags, and the sharp bound has zero
slack for every parameter k, including k=0. -/
theorem sharpFamily_certificate (k : Nat) :
    (∀ t : Int, sharpFamily k (t+((6*k+4 : Nat) : Int)) = sharpFamily k t) ∧
    sharpFamily k (2*(k : Int)+1) = true ∧
    EvenBackA (sharpFamily k) (2*(k : Int)+1) (8*k+3) ∧
    (∀ d : Nat, ShortPeriodicSupply.P2 (sharpFamily k) (2*(k : Int)+1) d ↔ d = 8*k+3) ∧
    3*(8*k+3)+7 = 4*(6*k+4) := by
  refine ⟨sharpFamily_periodic k,sharpFamily_odd k k,sharpFamily_clean k,?_,by omega⟩
  intro d
  constructor
  · intro hP
    exact ParitySupply.P2_lag_unique (sharpFamily k) (sharpFamily_odd k) k d (8*k+3)
      hP (sharpFamily_P2 k)
  · rintro rfl
    exact sharpFamily_P2 k

def currentSCounter (t : Int) : Bool := !decide (t % 3 = 0)

theorem currentSCounter_periodic (t : Int) : currentSCounter (t+3) = currentSCounter t := by
  simp [currentSCounter]

theorem current_A_premise_counterexample :
    currentSCounter 0 = false ∧ ShortPeriodicSupply.P2 currentSCounter 0 3 ∧
    EvenBackA currentSCounter 0 3 ∧ ¬ (3*3+7 ≤ 4*3) := by
  refine ⟨by decide,by unfold ShortPeriodicSupply.P2; decide,?_,by decide⟩
  intro i hi hi3 heven
  have hi2 : i = 2 := by omega
  subst i
  decide

end Recaman.CleanPeriodBound
