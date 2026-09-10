import Recaman.CanonicalSSFreeSupply

namespace Recaman.FiniteP2Semantics

open LeadingRunSupply ParitySupply CanonicalSSFreeSupply ShortPeriodicSupply

/-! Exact finite-history semantics of the prefix-key census. The sign at
time n is the transition n -> n+1, whose magnitude is n+1. -/

def weightedPrefix (e : Int → Bool) : Nat → Int
  | 0 => 0
  | n+1 => weightedPrefix e n + (n : Int)*sign (e n)

theorem window_prefix_identities (e : Int → Bool) (u d : Nat) :
    mass (past e ((u+d : Nat) : Int) d) = signSum e 0 (u+d) - signSum e 0 u ∧
    moment (past e ((u+d : Nat) : Int) d) =
      ((u+d : Nat) : Int)*mass (past e ((u+d : Nat) : Int) d) -
        (weightedPrefix e (u+d) - weightedPrefix e u) := by
  induction d with
  | zero => simp [past,moment]
  | succ d ih =>
    have htime : ((u+(d+1) : Nat) : Int)-1 = ((u+d : Nat) : Int) := by omega
    have hnat : u+(d+1) = (u+d)+1 := by omega
    rw [past_succ,htime]
    simp only [mass_cons,moment,hnat,signSum,weightedPrefix,Int.zero_add]
    constructor
    · change sign (e ((u+d : Nat) : Int)) + mass (past e ((u+d : Nat) : Int) d) =
        signSum e 0 (u+d) + sign (e ((u+d : Nat) : Int)) - signSum e 0 u
      omega
    · have hcast : ((u+d+1 : Nat) : Int) = ((u+d : Nat) : Int)+1 := by omega
      rw [hcast]
      grind

/-- This is the exact pair looked up by the C++ diagnostic, with no lag
cutoff and with the absolute weighted prefix indexed from zero. -/
theorem P2_iff_prefix_key (e : Int → Bool) (u d : Nat) :
    ShortPeriodicSupply.P2 e ((u+d : Nat) : Int) d ↔
      signSum e 0 u = signSum e 0 (u+d)-1 ∧
        weightedPrefix e u = weightedPrefix e (u+d)-((u+d : Nat) : Int) := by
  rw [← past_p2_iff]
  have h := window_prefix_identities e u d
  unfold LeadingRunSupply.P2
  constructor
  · rintro ⟨hm,hM⟩
    rw [hm] at h
    simp only [Int.mul_one] at h
    constructor <;> omega
  · rintro ⟨hP,hW⟩
    have hm : mass (past e ((u+d : Nat) : Int) d) = 1 := by omega
    refine ⟨hm,?_⟩
    rw [hm] at h
    simp only [Int.mul_one] at h
    omega

theorem canonical_value_prefix (n : Nat) :
    (a n : Int) = signSum canonicalSign 0 n + weightedPrefix canonicalSign n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [signSum,weightedPrefix,Int.zero_add,canonicalSign_nat]
    by_cases hcan : CanSubtract (n+1) (stateAt n)
    · have hv := a_succ_of_canSubtract hcan
      have hlo : n+1 < a n := hcan.1
      simp [hcan,sign]
      omega
    · have hv := a_succ_of_not_canSubtract hcan
      simp [hcan,sign]
      omega

/-- Finite P2 is an actual historical blocker with cumulative sign difference
one. General blockers need not satisfy this additional condition. -/
theorem canonical_P2_iff_height_one_blocker (u d : Nat) :
    ShortPeriodicSupply.P2 canonicalSign ((u+d : Nat) : Int) d ↔
      signSum canonicalSign 0 (u+d) - signSum canonicalSign 0 u = 1 ∧
        a (u+d) = a u + (u+d) + 1 := by
  rw [P2_iff_prefix_key]
  have ht := canonical_value_prefix (u+d)
  have hu := canonical_value_prefix u
  constructor <;> intro h <;> constructor <;> omega

theorem finite_P2_forces_A (u d : Nat)
    (hP : ShortPeriodicSupply.P2 canonicalSign ((u+d : Nat) : Int) d) : canonicalSign ((u+d : Nat) : Int) = true := by
  have hv := ((canonical_P2_iff_height_one_blocker u d).mp hP).2
  have hmem : a u ∈ valuesThrough (u+d) := mem_valuesThrough_iff.mpr ⟨u,by omega,rfl⟩
  have hnot : ¬ CanSubtract (u+d+1) (stateAt (u+d)) := by
    intro hcan
    have hfresh : a (u+d)-(u+d+1) ∉ valuesThrough (u+d) := hcan.2
    have hcandidate : a (u+d)-(u+d+1) = a u := by omega
    rw [hcandidate] at hfresh
    exact hfresh hmem
  rw [canonicalSign_nat]
  exact decide_eq_true hnot

/-- Positive historical obstruction at t5 is real, but no finite P2 window
exists there. This rules out reading the census as all blocker coverage. -/
theorem blocker_without_finite_P2_certificate :
    a 5 = 7 ∧ a 1 = 1 ∧ a 5-6 = a 1 ∧
    canonicalSign 5 = true ∧
    ∀ d : Fin 6, ¬ ShortPeriodicSupply.P2 canonicalSign 5 d.val := by
  unfold ShortPeriodicSupply.P2
  decide

theorem finite_P2_positive_certificate :
    ShortPeriodicSupply.P2 canonicalSign 6 3 ∧ a 6 = a 3+7 ∧ canonicalSign 6 = true := by
  unfold ShortPeriodicSupply.P2
  decide

end Recaman.FiniteP2Semantics
