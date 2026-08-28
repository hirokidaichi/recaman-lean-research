import Recaman.Basic

namespace Recaman

/-- The intermediate value required by the two-subtraction exact gate. -/
def gateIntermediate (u m : Nat) : Nat := u + m + 2

/-- Exact-gate lemma.

If the value at time u is 2u+m+3, both the intermediate value and m are
fresh, and m is positive, then steps u+1 and u+2 land exactly on m. -/
theorem exactGate_sufficient {u m : Nat} {state : State}
    (hmpos : 0 < m)
    (hvalue : state.value = 2 * u + m + 3)
    (hintermediate : gateIntermediate u m ∉ state.seen)
    (hmfresh : m ∉ state.seen) :
    (step (u + 2) (step (u + 1) state)).value = m := by
  have hsub1 : state.value - (u + 1) = gateIntermediate u m := by
    simp [gateIntermediate]
    omega
  have hcan1 : CanSubtract (u + 1) state := by
    constructor
    · omega
    · simpa [hsub1] using hintermediate
  rw [step_of_subtract hcan1, hsub1]
  have hsub2 : gateIntermediate u m - (u + 2) = m := by
    simp [gateIntermediate]
  have hcan2 : CanSubtract (u + 2)
      ⟨gateIntermediate u m, gateIntermediate u m :: state.seen⟩ := by
    constructor
    · simp [gateIntermediate]
      omega
    · rw [hsub2]
      simp only [List.mem_cons, not_or]
      constructor
      · simp [gateIntermediate]
        omega
      · exact hmfresh
  rw [step_of_subtract hcan2]
  simp [hsub2]

end Recaman
