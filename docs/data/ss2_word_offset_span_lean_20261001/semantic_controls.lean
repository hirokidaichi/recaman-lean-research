import Recaman.SS2WordOffsetSpan

open Recaman.LeadingRunSupply Recaman.SSFreeSupply
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.LagSevenDonorCoverage (oldestOffset)
open Recaman.SS2WordOffsetSpan

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def signs (s : String) : List Bool := s.toList.map (fun c => c == 'A')

-- Literal-boundary equality precedes use of the general family theorems.
example : word 0 = signs "SAAASSAAASS" ∧
    word 1 = signs "SASAAASSAAASSASASAS" ∧
    (word 7).length = 67 := by decide

-- The all-parameter results really apply at k=0, k=1 and k=7.
theorem checked_family (k : Nat) :
    P2 (word k) ∧ (∀ d, d < (word k).length → ¬ P2 ((word k).take d)) ∧
    ssCount (word k) = 2 ∧ NoSAAS (true :: word k) ∧
    (word k)[0]? = some false ∧ oldestOffset (word k) = 8*k+11 ∧
    (word k)[oldestOffset (word k)-1]? = some false ∧
    ((word k).reverse.takeWhile id).length = 0 :=
  ⟨word_P2 k, word_minimum k, word_ssCount k, history_noSAAS k,
    word_newest_S k, word_oldestOffset k, (word_true_oldest_S k).1,
    word_terminal_length k⟩

example : P2 (word 0) ∧ ∀ d, d < 11 → ¬ P2 ((word 0).take d) := by
  obtain ⟨hp, hm, _⟩ := checked_family 0
  refine ⟨hp, ?_⟩
  intro d hd
  exact hm d (by simpa [word_length] using hd)
example : NoSAAS (true :: word 1) := (checked_family 1).2.2.2.1
example : oldestOffset (word 7) = 67 := by simpa using word_oldestOffset 7
example : (word 7)[66]? = some false ∧ (word 7)[67]? = none := by
  have h := word_true_oldest_S 7
  constructor
  · simpa [word_oldestOffset] using h.1
  · exact h.2 67 (by rw [word_oldestOffset]; decide)

-- Converse classification realizes both a core prefix and a tail prefix.
example : ((word 7).take 17).length = 17 := by decide
example : 17 < (word 7).length ∧ mass ((word 7).take 17) = 1 := by
  apply (proper_mass_one_positions_iff 7 17).mpr
  exact Or.inl (by decide)
example : moment ((word 7).take 17) = 25 := by
  have hm := ((proper_mass_one_positions_iff 7 17).mpr (Or.inl (by decide)))
  have h := proper_mass_one_prefix 7 17 hm.1 hm.2
  rcases h with h | h | h | ⟨i,hi,hd,hM⟩ <;> omega
example : 65 < (word 7).length ∧ mass ((word 7).take 65) = 1 := by
  apply (proper_mass_one_positions_iff 7 65).mpr
  exact Or.inr (Or.inr (Or.inr ⟨20, by decide, by decide⟩))
example : moment ((word 7).take 65) = 1 := by
  have hm := (proper_mass_one_positions_iff 7 65).mpr
    (Or.inr (Or.inr (Or.inr ⟨20, by decide, by decide⟩)))
  have h := proper_mass_one_prefix 7 65 hm.1 hm.2
  rcases h with h | h | h | ⟨i,hi,hd,hM⟩ <;> omega
example : ¬(11 < (word 0).length ∧ mass ((word 0).take 11) = 1) := by
  rw [proper_mass_one_positions_iff]
  omega

-- The unbounded theorem itself is consumed, with the key word premises retained.
theorem bound_1000 : ∃ k, P2 (word k) ∧
    (∀ d, 0 < d → d < (word k).length → ¬ P2 ((word k).take d)) ∧
    ssCount (word k) = 2 ∧ NoSAAS (true :: word k) ∧
    ((word k).reverse.takeWhile id).length = 0 ∧
    1000 < oldestOffset (word k)-1 := by
  obtain ⟨k,hP,hmin,hss,hno,hlen,hfirst,hold,hbit,htail,hspan,hbig⟩ :=
    exists_unbounded_span 1000
  exact ⟨k,hP,hmin,hss,hno,htail,hbig⟩

-- Counterfactuals are distinct words, not applications of the family theorem.
def wrongCore := alt false 1 ++ signs "AAASSSASASA" ++ alt true 3
def extraAS := alt false 1 ++ core ++ alt true 4
example : P2 wrongCore ∧ ssCount wrongCore = 2 ∧ wrongCore.length = 19 ∧
    P2 (wrongCore.take 7) ∧ 7 < wrongCore.length := by decide
example : mass extraAS = 1 ∧ moment extraAS = -1 ∧ extraAS.length = 21 ∧
    P2 (extraAS.take 19) ∧ 19 < extraAS.length := by decide
example : ¬ P2 extraAS := by decide
example : ssCount (signs "SSS") = 2 := by decide

#print axioms checked_family
#print axioms bound_1000
