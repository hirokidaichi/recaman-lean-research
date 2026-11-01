import Recaman.NoSSMassOne
import Recaman.LeadingRunSupply

/-!
# P2ModFourRigidity: Universal Mod-4 Parity Law and Discrete Quantum Length Hierarchy

This module establishes the universal modulo 4 rigidity law for all P2 words:
1. `p2_length_mod_four`: Any P2 word satisfies `w.length % 4 = 3` (proved in `NoSSMassOne`).
2. `no_p2_mod4_zero`, `no_p2_mod4_one`, `no_p2_mod4_two`: Forbidden residue classes.
3. `p2_length_is_odd`: Every P2 word has odd length.
4. `no_p2_even_length`: Even lengths are universally impossible for P2 words.
5. Specific forbidden lengths: 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20, 21.
6. Discrete quantum length stratification:
   - `p2_length_lt_seven_eq_three`: Any P2 word with length < 7 has length 3.
   - `p2_length_lt_eleven_cases`: Any P2 word with length < 11 has length 3 or 7.
   - `p2_length_lt_fifteen_cases`: Any P2 word with length < 15 has length 3, 7, or 11.
   - `p2_length_lt_nineteen_cases`: Any P2 word with length < 19 has length 3, 7, 11, or 15.
   - `p2_length_lt_twenty_three_cases`: Any P2 word with length < 23 has length 3, 7, 11, 15, or 19.
   - `p2_length_discrete_gap`: Universal non-existence in intervals (4k+3, 4k+7).
-/

namespace Recaman.P2ModFourRigidity

open Recaman.LeadingRunSupply Recaman.NoSSMassOne

/-- Any word with length % 4 ≠ 3 cannot be a P2 word. -/
theorem p2_length_ne_three_mod4 (w : List Bool) (hmod : w.length % 4 ≠ 3) (hP : P2 w) : False := by
  have h4 := p2_length_mod_four w hP
  exact hmod h4

/-- Residue class 0 mod 4 is impossible for P2 words. -/
theorem no_p2_mod4_zero (w : List Bool) (hmod : w.length % 4 = 0) (hP : P2 w) : False := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Residue class 1 mod 4 is impossible for P2 words. -/
theorem no_p2_mod4_one (w : List Bool) (hmod : w.length % 4 = 1) (hP : P2 w) : False := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Residue class 2 mod 4 is impossible for P2 words. -/
theorem no_p2_mod4_two (w : List Bool) (hmod : w.length % 4 = 2) (hP : P2 w) : False := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Every P2 word has odd length. -/
theorem p2_length_is_odd (w : List Bool) (hP : P2 w) : w.length % 2 = 1 := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Even lengths are universally impossible for P2 words. -/
theorem no_p2_even_length (w : List Bool) (heven : w.length % 2 = 0) (hP : P2 w) : False := by
  have hodd := p2_length_is_odd w hP
  omega

/-- No P2 word of length 1. -/
theorem no_p2_length_1 (w : List Bool) (hlen : w.length = 1) (hP : P2 w) : False :=
  no_p2_mod4_one w (by omega) hP

/-- No P2 word of length 2. -/
theorem no_p2_length_2 (w : List Bool) (hlen : w.length = 2) (hP : P2 w) : False :=
  no_p2_mod4_two w (by omega) hP

/-- No P2 word of length 4. -/
theorem no_p2_length_4 (w : List Bool) (hlen : w.length = 4) (hP : P2 w) : False :=
  no_p2_mod4_zero w (by omega) hP

/-- No P2 word of length 5. -/
theorem no_p2_length_5 (w : List Bool) (hlen : w.length = 5) (hP : P2 w) : False :=
  no_p2_mod4_one w (by omega) hP

/-- No P2 word of length 6. -/
theorem no_p2_length_6 (w : List Bool) (hlen : w.length = 6) (hP : P2 w) : False :=
  no_p2_mod4_two w (by omega) hP

/-- No P2 word of length 8. -/
theorem no_p2_length_8 (w : List Bool) (hlen : w.length = 8) (hP : P2 w) : False :=
  no_p2_mod4_zero w (by omega) hP

/-- No P2 word of length 9. -/
theorem no_p2_length_9 (w : List Bool) (hlen : w.length = 9) (hP : P2 w) : False :=
  no_p2_mod4_one w (by omega) hP

/-- No P2 word of length 10. -/
theorem no_p2_length_10 (w : List Bool) (hlen : w.length = 10) (hP : P2 w) : False :=
  no_p2_mod4_two w (by omega) hP

/-- No P2 word of length 12. -/
theorem no_p2_length_12 (w : List Bool) (hlen : w.length = 12) (hP : P2 w) : False :=
  no_p2_mod4_zero w (by omega) hP

/-- No P2 word of length 13. -/
theorem no_p2_length_13 (w : List Bool) (hlen : w.length = 13) (hP : P2 w) : False :=
  no_p2_mod4_one w (by omega) hP

/-- No P2 word of length 14. -/
theorem no_p2_length_14 (w : List Bool) (hlen : w.length = 14) (hP : P2 w) : False :=
  no_p2_mod4_two w (by omega) hP

/-- No P2 word of length 16. -/
theorem no_p2_length_16 (w : List Bool) (hlen : w.length = 16) (hP : P2 w) : False :=
  no_p2_mod4_zero w (by omega) hP

/-- No P2 word of length 17. -/
theorem no_p2_length_17 (w : List Bool) (hlen : w.length = 17) (hP : P2 w) : False :=
  no_p2_mod4_one w (by omega) hP

/-- No P2 word of length 18. -/
theorem no_p2_length_18 (w : List Bool) (hlen : w.length = 18) (hP : P2 w) : False :=
  no_p2_mod4_two w (by omega) hP

/-- No P2 word of length 20. -/
theorem no_p2_length_20 (w : List Bool) (hlen : w.length = 20) (hP : P2 w) : False :=
  no_p2_mod4_zero w (by omega) hP

/-- No P2 word of length 21. -/
theorem no_p2_length_21 (w : List Bool) (hlen : w.length = 21) (hP : P2 w) : False :=
  no_p2_mod4_one w (by omega) hP

/-- P2 length lower bound: Any P2 word has length at least 3. -/
theorem p2_length_ge_three (w : List Bool) (hP : P2 w) : 3 ≤ w.length := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Discrete Quantum Step 1: Any P2 word with length < 7 has length exactly 3. -/
theorem p2_length_lt_seven_eq_three (w : List Bool) (hlt : w.length < 7) (hP : P2 w) :
    w.length = 3 := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Discrete Quantum Step 2: Any P2 word with length < 11 has length 3 or 7. -/
theorem p2_length_lt_eleven_cases (w : List Bool) (hlt : w.length < 11) (hP : P2 w) :
    w.length = 3 ∨ w.length = 7 := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Discrete Quantum Step 3: Any P2 word with length < 15 has length 3, 7, or 11. -/
theorem p2_length_lt_fifteen_cases (w : List Bool) (hlt : w.length < 15) (hP : P2 w) :
    w.length = 3 ∨ w.length = 7 ∨ w.length = 11 := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Discrete Quantum Step 4: Any P2 word with length < 19 has length 3, 7, 11, or 15. -/
theorem p2_length_lt_nineteen_cases (w : List Bool) (hlt : w.length < 19) (hP : P2 w) :
    w.length = 3 ∨ w.length = 7 ∨ w.length = 11 ∨ w.length = 15 := by
  have h4 := p2_length_mod_four w hP
  omega

/-- Discrete Quantum Step 5: Any P2 word with length < 23 has length 3, 7, 11, 15, or 19. -/
theorem p2_length_lt_twenty_three_cases (w : List Bool) (hlt : w.length < 23) (hP : P2 w) :
    w.length = 3 ∨ w.length = 7 ∨ w.length = 11 ∨ w.length = 15 ∨ w.length = 19 := by
  have h4 := p2_length_mod_four w hP
  omega

/-- General Gap Theorem: Between 4k-1 and 4k+3, there are no P2 word lengths. -/
theorem p2_length_discrete_gap (w : List Bool) (k : Nat)
    (h_gt : 4 * k + 3 < w.length) (h_lt : w.length < 4 * k + 7) (hP : P2 w) : False := by
  have h4 := p2_length_mod_four w hP
  omega

end Recaman.P2ModFourRigidity
