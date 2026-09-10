import Recaman.FiniteP2Semantics
import Recaman.SignedSupplyGap

namespace Recaman.ShortBlockerRigidity

open LeadingRunSupply SignedSupplyGap FiniteP2Semantics CanonicalSSFreeSupply

/-! A clock-dependent bound separates general historical blockers from P2.
Sharpness is in the arbitrary sign-word model, not an all-parameter claim
of canonical reachability. -/

theorem moment_upper_of_mass (w : List Bool) (m : Int) (hm : mass w = m) :
    4*moment w ≤ (w.length : Int)*w.length + 2*w.length*m - m*m + 2*m := by
  have hp := positions_upper w
  have hc := mass_eq w
  have ht := twice_moment w
  have heq :
      (w.length : Int)*w.length + 2*w.length*m - m*m + 2*m - 4*moment w =
      4*(ones w*(2*(w.length : Int)-ones w+1)-2*positions w) := by grind
  omega

/-- Any collision whose mass differs from one must have a long enough
window. No periodicity, history freshness, or assumed P2 is used here. -/
theorem nonunit_collision_bound (w : List Bool) (n : Int) (_hn : 0 < n)
    (hw : 0 < w.length) (hcoll : moment w = n*(mass w-1)) (hne : mass w ≠ 1) :
    4*n ≤ (w.length : Int)*(w.length+4) := by
  let d : Int := w.length
  let m : Int := mass w
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hsq : 0 ≤ d*d := Int.mul_nonneg (by omega) (by omega)
  by_cases hbound : 4*n ≤ d*(d+4)
  · exact hbound
  · have hgap : 0 < 4*n-d*(d+4) := by omega
    by_cases hm : 2 ≤ m
    · have hM := moment_upper_of_mass w m rfl
      change 4*moment w ≤ d*d+2*d*m-m*m+2*m at hM
      have hrem := Int.mul_nonneg (show 0 ≤ m-2 by omega)
        (show 0 ≤ d*d+2*d+m by omega)
      have heq :
          (m-1)*(d*(d+4)-4*n) =
          (d*d+2*d*m-m*m+2*m-4*moment w)+(m-2)*(d*d+2*d+m) := by
        change moment w = n*(m-1) at hcoll
        grind
      have hpos := Int.mul_pos (show 0 < m-1 by omega) hgap
      have hneg : (m-1)*(4*n-d*(d+4)) = -((m-1)*(d*(d+4)-4*n)) := by grind
      omega
    · have hm0 : m ≤ 0 := by dsimp [m] at *; omega
      have hM := moment_lower_of_mass w m rfl
      change -(d*d)+2*d*m+m*m+2*m ≤ 4*moment w at hM
      have hrem := Int.mul_nonneg (show 0 ≤ -m by omega)
        (show 0 ≤ d*d+2*d-m-2 by omega)
      have heq :
          (1-m)*(d*(d+4)-4*n) =
          (d*d-2*d*m-m*m-2*m+4*moment w)+(-m)*(d*d+2*d-m-2)+4*d := by
        change moment w = n*(m-1) at hcoll
        grind
      have hpos := Int.mul_pos (show 0 < 1-m by omega) hgap
      have hneg : (1-m)*(4*n-d*(d+4)) = -((1-m)*(d*(d+4)-4*n)) := by grind
      omega

theorem canonical_collision_moment (u d : Nat)
    (hv : a (u+d) = a u+(u+d)+1) :
    moment (past canonicalSign ((u+d : Nat) : Int) d) =
      ((u+d+1 : Nat) : Int)*(mass (past canonicalSign ((u+d : Nat) : Int) d)-1) := by
  have hw := window_prefix_identities canonicalSign u d
  have ht := canonical_value_prefix (u+d)
  have hu := canonical_value_prefix u
  have hv' : (a (u+d) : Int) - a u = ((u+d+1 : Nat) : Int) := by omega
  have hclock : ((u+d+1 : Nat) : Int) = ((u+d : Nat) : Int)+1 := by omega
  grind

theorem canonical_nonP2_blocker_bound (u d : Nat)
    (hv : a (u+d) = a u+(u+d)+1)
    (hnot : ¬ ShortPeriodicSupply.P2 canonicalSign ((u+d : Nat) : Int) d) :
    4*((u+d+1 : Nat) : Int) ≤ (d : Int)*(d+4) := by
  have hd : 0 < d := by
    by_cases hz : d = 0
    · subst d
      simp only [Nat.add_zero] at hv
      omega
    · omega
  have hcoll := canonical_collision_moment u d hv
  have hmne : mass (past canonicalSign ((u+d : Nat) : Int) d) ≠ 1 := by
    intro hm
    have hM : moment (past canonicalSign ((u+d : Nat) : Int) d) = 0 := by
      rw [hm] at hcoll
      simpa using hcoll
    exact hnot ((past_p2_iff canonicalSign ((u+d : Nat) : Int) d).mp ⟨hm,hM⟩)
  have h := nonunit_collision_bound (past canonicalSign ((u+d : Nat) : Int) d)
    ((u+d+1 : Nat) : Int) (by omega) (by simpa [past] using hd) hcoll hmne
  simpa [past] using h

theorem canonical_short_blocker_P2 (u d : Nat)
    (hv : a (u+d) = a u+(u+d)+1)
    (hshort : (d : Int)*(d+4) < 4*((u+d+1 : Nat) : Int)) :
    ShortPeriodicSupply.P2 canonicalSign ((u+d : Nat) : Int) d := by
  by_cases hP : ShortPeriodicSupply.P2 canonicalSign ((u+d : Nat) : Int) d
  · exact hP
  · have h := canonical_nonP2_blocker_bound u d hv hP
    omega

def equalityFamily (r : Nat) : List Bool :=
  List.replicate (r-1) false ++ List.replicate (r+1) true

theorem equalityFamily_certificate (r : Nat) (hr : 1 ≤ r) :
    (equalityFamily r).length = 2*r ∧ mass (equalityFamily r) = 2 ∧
    moment (equalityFamily r) = (r : Int)*(r+2) ∧
    2*r+1 ≤ r*(r+2) ∧ 4*(r*(r+2)) = (2*r)*(2*r+4) := by
  have hrsub : ((r-1 : Nat) : Int) = (r : Int)-1 := by omega
  have hlen : (equalityFamily r).length = 2*r := by simp [equalityFamily]; omega
  have hones : ones (equalityFamily r) = (r : Int)+1 := by simp [equalityFamily,ones_append]
  have hm := mass_eq (equalityFamily r)
  rw [hlen,hones] at hm
  have hp := positions_replicate_A (r+1)
  have hpos : positions (equalityFamily r) =
      ((r : Int)-1)*((r : Int)+1)+positions (List.replicate (r+1) true) := by
    simp [equalityFamily,positions_append,hrsub,Int.add_comm]
  have hM := twice_moment (equalityFamily r)
  rw [hlen,hpos] at hM
  have hsq : 1 ≤ r*r := Nat.mul_pos hr hr
  refine ⟨hlen,by omega,?_,?_,by grind⟩
  · simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at hp hM
    grind
  · simp only [Nat.mul_add,Nat.mul_two]
    omega

/-- Equality cannot be included in the rigidity hypothesis, even on the
canonical prefix: AA exposes the historical zero at step3. -/
theorem strictness_canonical_certificate :
    a 2 = a 0+3 ∧ (2 : Nat)*(2+4) = 4*3 ∧
    ¬ ShortPeriodicSupply.P2 canonicalSign 2 2 := by
  unfold ShortPeriodicSupply.P2
  decide

end Recaman.ShortBlockerRigidity
