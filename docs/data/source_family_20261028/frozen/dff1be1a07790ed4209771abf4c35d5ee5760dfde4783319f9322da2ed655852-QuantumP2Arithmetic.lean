import Recaman.StratifiedCapacityHierarchy
import Recaman.P2ModFourRigidity

/-!
# QuantumP2Arithmetic: Discrete Quantum Formulas for Additions, Subtractions, and Surplus

This module establishes exact closed-form algebraic formulas for the additions, subtractions,
and donation surpluses of P2 words across all quantum levels `m`:

1. `p2_ones_eq_two_m_plus_two`: Any P2 word of length `4*m + 3` contains exactly `2*m + 2` additions.
2. `p2_subtractions_eq_two_m_plus_one`: Any P2 word of length `4*m + 3` contains exactly `2*m + 1` subtractions.
3. `p2_subtraction_surplus_eq_two_m`: The internal subtraction surplus after donating one subtraction
   is exactly `2*m`.
4. `quantum_level_zero_values`: Level 0 (`m = 0`, lag 3) has 2 additions, 1 subtraction, surplus 0.
5. `quantum_level_one_values`: Level 1 (`m = 1`, lag 7) has 4 additions, 3 subtractions, surplus 2.
6. `quantum_level_two_values`: Level 2 (`m = 2`, lag 11) has 6 additions, 5 subtractions, surplus 4.
7. `quantum_level_three_values`: Level 3 (`m = 3`, lag 15) has 8 additions, 7 subtractions, surplus 6.
8. `quantum_level_four_values`: Level 4 (`m = 4`, lag 19) has 10 additions, 9 subtractions, surplus 8.
9. `tight_size_forces_quantum_level_bound`: In any tight subset A, if a member window covers
   at least `2*m + 1` subtractions, then `2*m + 1 ≤ |A|`.
10. `tight_size_le_two_forces_level_zero`: In any tight subset of size `|A| ≤ 2`, any window covering
    at least `2*m + 1` subtractions must have `m = 0` (forcing lag 3).
11. `grand_quantum_p2_arithmetic_synthesis`: Master synthesis theorem on quantum P2 arithmetic.
-/

namespace Recaman.QuantumP2Arithmetic

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TightBottleneckBound

/-- Any P2 word of length 4*m + 3 contains exactly 2*m + 2 additions. -/
theorem p2_ones_eq_two_m_plus_two (w : List Bool) (hP : P2 w) (m : Nat) (hlen : w.length = 4 * m + 3) :
    ones w = 2 * m + 2 := by
  have hm := hP.1
  have hmass := mass_eq w
  omega

/-- Any P2 word of length 4*m + 3 contains exactly 2*m + 1 subtractions. -/
theorem p2_subtractions_eq_two_m_plus_one (w : List Bool) (hP : P2 w) (m : Nat) (hlen : w.length = 4 * m + 3) :
    w.length - ones w = 2 * m + 1 := by
  have hm := hP.1
  have hmass := mass_eq w
  omega

/-- The internal subtraction surplus of a P2 word of length 4*m + 3 after donating one subtraction
is exactly 2*m. -/
theorem p2_subtraction_surplus_eq_two_m (w : List Bool) (hP : P2 w) (m : Nat) (hlen : w.length = 4 * m + 3) :
    (w.length - ones w) - 1 = 2 * m := by
  have hsubs := p2_subtractions_eq_two_m_plus_one w hP m hlen
  omega

/-- Level 0 (m = 0, lag 3): 2 additions, 1 subtraction, 0 surplus. -/
theorem quantum_level_zero_values (w : List Bool) (hP : P2 w) (hlen : w.length = 3) :
    ones w = 2 ∧ w.length - ones w = 1 ∧ (w.length - ones w) - 1 = 0 := by
  have h0 : w.length = 4 * 0 + 3 := by omega
  exact ⟨p2_ones_eq_two_m_plus_two w hP 0 h0,
         p2_subtractions_eq_two_m_plus_one w hP 0 h0,
         p2_subtraction_surplus_eq_two_m w hP 0 h0⟩

/-- Level 1 (m = 1, lag 7): 4 additions, 3 subtractions, 2 surplus. -/
theorem quantum_level_one_values (w : List Bool) (hP : P2 w) (hlen : w.length = 7) :
    ones w = 4 ∧ w.length - ones w = 3 ∧ (w.length - ones w) - 1 = 2 := by
  have h1 : w.length = 4 * 1 + 3 := by omega
  exact ⟨p2_ones_eq_two_m_plus_two w hP 1 h1,
         p2_subtractions_eq_two_m_plus_one w hP 1 h1,
         p2_subtraction_surplus_eq_two_m w hP 1 h1⟩

/-- Level 2 (m = 2, lag 11): 6 additions, 5 subtractions, 4 surplus. -/
theorem quantum_level_two_values (w : List Bool) (hP : P2 w) (hlen : w.length = 11) :
    ones w = 6 ∧ w.length - ones w = 5 ∧ (w.length - ones w) - 1 = 4 := by
  have h2 : w.length = 4 * 2 + 3 := by omega
  exact ⟨p2_ones_eq_two_m_plus_two w hP 2 h2,
         p2_subtractions_eq_two_m_plus_one w hP 2 h2,
         p2_subtraction_surplus_eq_two_m w hP 2 h2⟩

/-- Level 3 (m = 3, lag 15): 8 additions, 7 subtractions, 6 surplus. -/
theorem quantum_level_three_values (w : List Bool) (hP : P2 w) (hlen : w.length = 15) :
    ones w = 8 ∧ w.length - ones w = 7 ∧ (w.length - ones w) - 1 = 6 := by
  have h3 : w.length = 4 * 3 + 3 := by omega
  exact ⟨p2_ones_eq_two_m_plus_two w hP 3 h3,
         p2_subtractions_eq_two_m_plus_one w hP 3 h3,
         p2_subtraction_surplus_eq_two_m w hP 3 h3⟩

/-- Level 4 (m = 4, lag 19): 10 additions, 9 subtractions, 8 surplus. -/
theorem quantum_level_four_values (w : List Bool) (hP : P2 w) (hlen : w.length = 19) :
    ones w = 10 ∧ w.length - ones w = 9 ∧ (w.length - ones w) - 1 = 8 := by
  have h4 : w.length = 4 * 4 + 3 := by omega
  exact ⟨p2_ones_eq_two_m_plus_two w hP 4 h4,
         p2_subtractions_eq_two_m_plus_one w hP 4 h4,
         p2_subtraction_surplus_eq_two_m w hP 4 h4⟩

/-- Tight Size Bound on Quantum Level: In any tight subset A, if a member window covers
at least 2*m + 1 subtractions, then 2*m + 1 ≤ |A|. -/
theorem tight_size_forces_quantum_level_bound (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat) (u : Nat) (hu : u ∈ A)
    (htight : (neighborhood e p A lag).length = A.length)
    (m : Nat) (hNk : 2 * m + 1 ≤ (neighborhood e p [u] lag).length) :
    2 * m + 1 ≤ A.length :=
  tight_size_lower_bound p hp A lag u hu (2 * m + 1) hNk htight

/-- Tight Size ≤ 2 Forces Level Zero: In any tight subset of size |A| ≤ 2, any window covering
at least 2*m + 1 subtractions must have m = 0. -/
theorem tight_size_le_two_forces_level_zero (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat) (u : Nat) (hu : u ∈ A)
    (hlen : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (m : Nat) (hNk : 2 * m + 1 ≤ (neighborhood e p [u] lag).length) :
    m = 0 := by
  have hbound := tight_size_forces_quantum_level_bound p hp A lag u hu htight m hNk
  omega

/-- Master Synthesis: Grand Quantum P2 Arithmetic Theorem. -/
theorem grand_quantum_p2_arithmetic_synthesis (w : List Bool) (hP : P2 w) (m : Nat) (hlen : w.length = 4 * m + 3) :
    ones w = 2 * m + 2 ∧
    w.length - ones w = 2 * m + 1 ∧
    (w.length - ones w) - 1 = 2 * m :=
  ⟨p2_ones_eq_two_m_plus_two w hP m hlen,
   p2_subtractions_eq_two_m_plus_one w hP m hlen,
   p2_subtraction_surplus_eq_two_m w hP m hlen⟩

end Recaman.QuantumP2Arithmetic
