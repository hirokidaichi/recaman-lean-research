import Recaman.ShortBlockerRigidity
import Recaman.SharpPeriodicSupply

namespace Recaman.PositivePeriodLag

open LeadingRunSupply

/-! Positive periodic drift bounds the lag of a collision, without assuming
P2 or a fixed supplier lag. The residual old word is entirely arbitrary. -/

def blocks (b : List Bool) : Nat → List Bool
  | 0 => []
  | q+1 => b ++ blocks b q

theorem blocks_length (b : List Bool) (q : Nat) : (blocks b q).length = q*b.length := by
  induction q with
  | zero => simp [blocks]
  | succ q ih => simp [blocks,ih,Nat.add_mul,Nat.add_comm]

theorem blocks_mass (b : List Bool) (q : Nat) : mass (blocks b q) = (q : Int)*mass b := by
  induction q with
  | zero => simp [blocks]
  | succ q ih => simp [blocks,mass_append,ih]; grind

theorem blocks_moment (b : List Bool) (q : Nat) :
    2*moment (blocks b q) = 2*(q : Int)*moment b +
      (b.length : Int)*mass b*q*(q-1) := by
  induction q with
  | zero => simp [blocks,moment]
  | succ q ih => simp only [blocks,moment_append,blocks_mass,Int.natCast_add,Int.cast_ofNat_Int]; grind

theorem mass_bounds (w : List Bool) : -(w.length : Int) ≤ mass w ∧ mass w ≤ w.length := by
  have h := ones_bounds w
  have hm := mass_eq w
  omega

theorem moment_upper (w : List Bool) : 2*moment w ≤ (w.length : Int)*(w.length+1) := by
  induction w with
  | nil => simp [moment]
  | cons b w ih =>
    have hm := (mass_bounds w).2
    have hs : ShortPeriodicSupply.sign b ≤ 1 := by cases b <;> decide
    simp only [moment,List.length_cons,Int.natCast_add,Int.cast_ofNat_Int]
    have heq : ((w.length : Int)+1)*(w.length+1+1) =
        (w.length : Int)*(w.length+1)+2*w.length+2 := by grind
    omega

/-- Arithmetic core, with independent (weakened-history) block moments. -/
theorem collision_blocks_arithmetic (p r q S B s C n : Int)
    (hp : 1 ≤ p) (hr : 0 ≤ r) (hrp : r < p) (hq : 0 ≤ q)
    (hS : 1 ≤ S) (hB : 2*B ≤ p*(p+1))
    (hs : -r ≤ s) (hC : 2*C ≤ r*(r+1))
    (hn : q*p+r+1 ≤ n)
    (hc : 2*n*(q*S+s-1) = 2*q*B+p*S*q*(q-1)+2*q*p*s+2*C) :
    q < 4*p+4 := by
  by_cases hsmall : q < 4*p+4
  · exact hsmall
  · have hqbig : 4*p+4 ≤ q := by omega
    let h := n-(q*p+r+1)
    have hh : 0 ≤ h := by dsimp [h]; omega
    have hn' : n = q*p+r+1+h := by dsimp [h]; omega
    have hcoef : 0 ≤ 2*n-p*(q-1) := by
      have hprod := Int.mul_nonneg (show 0 ≤ p by omega) (show 0 ≤ q+1 by omega)
      have heq : 2*n-p*(q-1) = p*(q+1)+2*(r+1+h) := by grind
      omega
    have h1 := Int.mul_nonneg (Int.mul_nonneg hq hcoef) (show 0 ≤ S-1 by omega)
    have h2 := Int.mul_nonneg hq (show 0 ≤ p*(p+1)-2*B by omega)
    have h3 := Int.mul_nonneg (show 0 ≤ 2*(n-q*p) by omega) (show 0 ≤ s+r by omega)
    have h4 : 0 ≤ r*(r+1)-2*C := by omega
    let T := p*q*(q-p-2)+2*q*(r+1)-(r+1)*(3*r+2)+2*h*(q-r-1)
    have hdecomp :
        2*n*(q*S+s-1)-(2*q*B+p*S*q*(q-1)+2*q*p*s+2*C) =
        q*(2*n-p*(q-1))*(S-1)+q*(p*(p+1)-2*B)+
        2*(n-q*p)*(s+r)+(r*(r+1)-2*C)+T := by dsimp [T]; grind
    have hT : T ≤ 0 := by omega
    have hneg := Int.mul_le_mul (show r+1 ≤ p by omega)
      (show 3*r+2 ≤ 3*p-1 by omega) (show 0 ≤ 3*r+2 by omega) (show 0 ≤ p by omega)
    have hbig := Int.mul_le_mul (show p ≤ q by omega)
      (show 3 ≤ q-p-2 by omega) (show 0 ≤ 3 by omega) (show 0 ≤ q by omega)
    have hbigp := Int.mul_le_mul_of_nonneg_left hbig (show 0 ≤ p by omega)
    have hpos1 := Int.mul_nonneg hq (show 0 ≤ r+1 by omega)
    have hpos2 := Int.mul_nonneg hh (show 0 ≤ q-r-1 by omega)
    have heq : T = (p*q*(q-p-2)-3*p*p)+
        (p*(3*p-1)-(r+1)*(3*r+2))+p+2*(q*(r+1))+2*(h*(q-r-1)) := by dsimp [T]; grind
    have hbp : 3*p*p ≤ p*q*(q-p-2) := by grind
    omega

theorem repeated_word_collision_bound (b v : List Bool) (q : Nat) (n : Int)
    (hb : 0 < b.length) (hv : v.length < b.length) (hS : 1 ≤ mass b)
    (hn : ((blocks b q ++ v).length : Int) < n)
    (hc : moment (blocks b q ++ v) = n*(mass (blocks b q ++ v)-1)) :
    q < 4*b.length+4 ∧ (blocks b q ++ v).length < (4*b.length+4)*b.length := by
  have hM := blocks_moment b q
  have hcol : 2*n*((q : Int)*mass b+mass v-1) =
      2*(q : Int)*moment b+(b.length : Int)*mass b*q*(q-1)+
      2*q*b.length*mass v+2*moment v := by
    rw [moment_append,mass_append,blocks_mass,blocks_length] at hc
    simp only [Int.natCast_mul] at hc
    grind
  have hn' : (q : Int)*b.length+v.length+1 ≤ n := by
    simp only [List.length_append,blocks_length,Int.natCast_add,Int.natCast_mul] at hn
    omega
  have h := collision_blocks_arithmetic b.length v.length q (mass b) (moment b)
    (mass v) (moment v) n (by omega) (by omega) (by omega) (by omega)
    hS (moment_upper b) (mass_bounds v).1 (moment_upper v) hn' hcol
  have hq' : q < 4*b.length+4 := by omega
  refine ⟨hq',?_⟩
  rw [List.length_append,blocks_length]
  have hp := Nat.mul_le_mul_right b.length (show q+1 ≤ 4*b.length+4 by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hp ⊢
  omega

theorem periodic_past_blocks (e : Int → Bool) (p : Nat)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (q r : Nat) :
    past e t (q*p+r) = blocks (past e t p) q ++ past e t r := by
  induction q generalizing t with
  | zero => simp [blocks]
  | succ q ih =>
    have heq : (q+1)*p+r = p+(q*p+r) := by grind
    rw [heq,past_append,ih]
    have hs (d : Nat) : past e (t-p) d = past e t d := by
      have h := SharpPeriodicSupply.past_shift e p hper t (-1) d
      simpa [Int.sub_eq_add_neg] using h
    rw [hs p,hs r]
    simp only [blocks,List.append_assoc]

/-- Uniform in the clock and phase; P2 is not an input. -/
theorem periodic_collision_lag_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d : Nat) (n : Int)
    (hS : 1 ≤ mass (past e t p)) (hn : (d : Int) < n)
    (hc : moment (past e t d) = n*(mass (past e t d)-1)) :
    d < (4*p+4)*p := by
  have hdecomp := periodic_past_blocks e p hper t (d/p) (d%p)
  have hd : d/p*p+d%p = d := by simpa [Nat.mul_comm] using Nat.div_add_mod d p
  rw [hd] at hdecomp
  have hb : 0 < (past e t p).length := by simpa [past] using hp
  have hv : (past e t (d%p)).length < (past e t p).length := by
    simpa [past] using Nat.mod_lt d hp
  have hlen : (blocks (past e t p) (d/p) ++ past e t (d%p)).length = d := by
    rw [← hdecomp]; simp [past]
  rw [hdecomp] at hc
  have h := repeated_word_collision_bound (past e t p) (past e t (d%p))
    (d/p) n hb hv hS (by rw [hlen]; exact hn) hc
  have hh := h.2
  rw [hlen] at hh
  simpa [past] using hh

def lagBound (p : Nat) : Nat := (4*p+4)*p

/-- All periodic-history collisions at this explicit late clock are P2. -/
theorem late_periodic_collision_P2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x+p) = e x) (t : Int) (d : Nat) (n : Int)
    (hS : 1 ≤ mass (past e t p)) (hn : (d : Int) < n)
    (hc : moment (past e t d) = n*(mass (past e t d)-1))
    (hlate : (lagBound p : Int)*(lagBound p+4) < 4*n) :
    ShortPeriodicSupply.P2 e t d := by
  have hd := periodic_collision_lag_bound e p hp hper t d n hS hn hc
  have hd' : d < lagBound p := hd
  have hdi : (d : Int) ≤ lagBound p := by omega
  have hbound : (d : Int)*(d+4) ≤ (lagBound p : Int)*(lagBound p+4) :=
    Int.mul_le_mul hdi (by omega)
      (by omega) (by omega)
  have hmass : mass (past e t d) = 1 := by
    by_cases hm : mass (past e t d) = 1
    · exact hm
    · have hpos : 0 < (past e t d).length := by
        by_cases hz : d = 0
        · subst d; simp [past,moment] at hc; omega
        · simp [past]; omega
      have h := ShortBlockerRigidity.nonunit_collision_bound (past e t d) n
        (by omega) hpos hc hm
      simp only [past,List.length_map,List.length_range] at h
      omega
  apply (past_p2_iff e t d).mp
  refine ⟨hmass,?_⟩
  rw [hmass] at hc
  simpa using hc

/-- A balanced repeated word has unbounded non-P2 collision lag, so the
positive mass assumption has mathematical content. -/
theorem zero_drift_counterfamily (q : Nat) (hq : 1 ≤ q) :
    mass (blocks [true,true,true,false,false,false] q) = 0 ∧
    moment (blocks [true,true,true,false,false,false] q) = -(9*(q : Int)) ∧
    (blocks [true,true,true,false,false,false] q).length < 9*q := by
  have hm := blocks_mass [true,true,true,false,false,false] q
  have hM := blocks_moment [true,true,true,false,false,false] q
  have hl := blocks_length [true,true,true,false,false,false] q
  simp only [mass_cons,mass_nil,moment,ShortPeriodicSupply.sign] at hm hM
  simp at hm hM hl
  exact ⟨hm,by omega,by omega⟩

end Recaman.PositivePeriodLag
