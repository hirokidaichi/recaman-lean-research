import Recaman.OneSSChargeCounterexample
import Recaman.FiniteP2Semantics
import Recaman.CanonicalOneSSWindow

namespace Recaman.CanonicalOneSSCounterexample

open LeadingRunSupply CanonicalSSFreeSupply OneSSChargeCounterexample
open ShortPeriodicSupply ShortReservoirCapacity ShortLocalParityCapacity
open CanonicalOneSSWindow

/-! The same centered-map collision occurs on the actual standard orbit.
The kernel checks the finite canonical sign window directly. -/

theorem canonical_window_signs (i : Nat) (hi : 0 < i) (hi15 : i ≤ 15) :
    canonicalSign (1352-(i : Int)) = witness (9-(i : Int)) := by
  have hw : past canonicalSign 1352 15 = past witness 9 15 :=
    canonical_window_certificate.trans window_certificate.1.symm
  have hil : i-1 < 15 := by omega
  have h : (past canonicalSign 1352 15)[i-1]'(by simpa [past] using hil) =
      (past witness 9 15)[i-1]'(by simpa [past] using hil) := by simp only [hw]
  rw [past_get canonicalSign 1352 15 (i-1) hil,past_get witness 9 15 (i-1) hil] at h
  have hindex : i-1+1 = i := by omega
  rwa [hindex] at h

theorem P2_congr (e f : Int → Bool) (t u : Int) (d : Nat)
    (h : ∀ i : Nat, 0 < i → i ≤ d → e (t-i) = f (u-i)) :
    ShortPeriodicSupply.P2 e t d ↔ ShortPeriodicSupply.P2 f u d := by
  have hpast : past e t d = past f u d := by
    unfold past
    apply List.map_congr_left
    intro i hi
    exact h (i+1) (by omega) (by have := List.mem_range.mp hi; omega)
  rw [← past_p2_iff,← past_p2_iff,hpast]

theorem canonical_old_signs (i : Nat) (hi : 0 < i) (hi11 : i ≤ 11) :
    canonicalSign (1350-(i : Int)) = witness (7-(i : Int)) := by
  have h := canonical_window_signs (i+2) (by omega) (by omega)
  have ht : (1352 : Int)-((i+2 : Nat) : Int) = 1350-i := by omega
  have hu : (9 : Int)-((i+2 : Nat) : Int) = 7-i := by omega
  exact (congrArg canonicalSign ht).symm.trans (h.trans (congrArg witness hu))

theorem canonical_minimum_lags :
    P2 canonicalSign 1352 15 ∧ P2 canonicalSign 1350 7 ∧
    (∀ d : Fin 15, ¬ P2 canonicalSign 1352 d.val) ∧
    (∀ d : Fin 7, ¬ P2 canonicalSign 1350 d.val) := by
  have h15 := minimum_lags_certificate.2.2.2.2.2.1
  have h7 := minimum_lags_certificate.2.2.2.2.1
  have hn7 := minimum_lags_certificate.2.2.2.2.2.2.1
  have hn15 := minimum_lags_certificate.2.2.2.2.2.2.2
  refine ⟨(P2_congr canonicalSign witness 1352 9 15 canonical_window_signs).mpr h15,
    (P2_congr canonicalSign witness 1350 7 7
      (fun i hi hil => canonical_old_signs i hi (by omega))).mpr h7,?_,?_⟩
  · intro d hP
    exact hn15 d ((P2_congr canonicalSign witness 1352 9 d.val
      (fun i hi hil => canonical_window_signs i hi (by omega))).mp hP)
  · intro d hP
    exact hn7 d ((P2_congr canonicalSign witness 1350 7 d.val
      (fun i hi hil => canonical_old_signs i hi (by omega))).mp hP)

/-- Sign times1350 and1352 (steps1351 and1353) collide at sign time1343
(the actual subtraction step1344). Both current additions follow from P2. -/
theorem canonical_centered_collision :
    canonicalSign 1350 = true ∧ canonicalSign 1352 = true ∧
    shortOff canonicalSign 1350 = 7 ∧ centeredOff canonicalSign 1352 15 = 9 ∧
    (1350 : Int)-shortOff canonicalSign 1350 = 1343 ∧
    (1352 : Int)-centeredOff canonicalSign 1352 15 = 1343 ∧
    canonicalSign 1343 = false := by
  have hmin := canonical_minimum_lags
  have hA1350 := FiniteP2Semantics.finite_P2_forces_A 1343 7 hmin.2.1
  have hA1352 := FiniteP2Semantics.finite_P2_forces_A 1337 15 hmin.1
  have hoff : shortOff canonicalSign 1350 = 7 := by
    have h := offsetAt_congr canonicalSign witness 1350 7 canonical_old_signs
    change shortOff canonicalSign 1350 = shortOff witness 7 at h
    exact h.trans centered_charge_collision.1
  have hS : canonicalSign 1343 = false := by
    have h := canonical_window_signs 9 (by decide) (by decide)
    exact h.trans centered_charge_collision.2.2.2.2
  have hcenter : centeredOff canonicalSign 1352 15 = 9 := by
    simp [centeredOff,hS]
  exact ⟨hA1350,hA1352,hoff,hcenter,by rw [hoff]; decide,by rw [hcenter]; decide,hS⟩

end Recaman.CanonicalOneSSCounterexample
