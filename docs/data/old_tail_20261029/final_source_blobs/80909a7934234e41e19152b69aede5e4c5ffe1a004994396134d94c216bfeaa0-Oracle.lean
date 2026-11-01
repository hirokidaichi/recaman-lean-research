import Recaman.Basic
import Recaman.Coordinates

namespace Recaman

def escapeBlocker (s m : Nat) : Nat := s + m + 6
def escapeX1 (s m : Nat) : Nat := 2 * s + m + 5
def escapeX2 (s m : Nat) : Nat := s + m + 3
def escapeAfterAddition (s m : Nat) : Nat := 3 * s + m + 6

/-- Local membership assumptions that force the +--- escape pattern. -/
structure EscapeAssumptions (s m : Nat) (state : State) : Prop where
  m_pos : 0 < m
  s_large : m + 9 < s
  value_eq : state.value = 2 * s + m + 6
  blocker_seen : escapeBlocker s m ∈ state.seen
  x1_fresh : escapeX1 s m ∉ state.seen
  x2_fresh : escapeX2 s m ∉ state.seen
  m_fresh : m ∉ state.seen

/-- Under the local oracle assumptions, the next four signs are +--- and the
fourth step lands on m.  The conjunction records all intermediate values. -/
theorem localEscape_trace {s m : Nat} {state : State}
    (h : EscapeAssumptions s m state) :
    (step s state).value = escapeAfterAddition s m ∧
    (step (s + 1) (step s state)).value = escapeX1 s m ∧
    (step (s + 2) (step (s + 1) (step s state))).value = escapeX2 s m ∧
    (step (s + 3)
      (step (s + 2) (step (s + 1) (step s state)))).value = m := by
  have hsub0 : state.value - s = escapeBlocker s m := by
    rw [h.value_eq]
    simp [escapeBlocker]
    omega
  have hseen0 : state.value - s ∈ state.seen := by
    rw [hsub0]
    exact h.blocker_seen
  have hstep0 : step s state =
      ⟨escapeAfterAddition s m, escapeAfterAddition s m :: state.seen⟩ := by
    rw [step_of_seen hseen0]
    rw [h.value_eq]
    simp [escapeAfterAddition]
    omega

  have hsub1 : escapeAfterAddition s m - (s + 1) = escapeX1 s m := by
    simp [escapeAfterAddition, escapeX1]
    omega
  have hcan1 : CanSubtract (s + 1)
      ⟨escapeAfterAddition s m, escapeAfterAddition s m :: state.seen⟩ := by
    constructor
    · simp [escapeAfterAddition]
      omega
    · rw [hsub1]
      simp only [List.mem_cons, not_or]
      constructor
      · simp [escapeAfterAddition, escapeX1]
        omega
      · exact h.x1_fresh
  have hstep1 : step (s + 1)
      ⟨escapeAfterAddition s m, escapeAfterAddition s m :: state.seen⟩ =
      ⟨escapeX1 s m,
        escapeX1 s m :: escapeAfterAddition s m :: state.seen⟩ := by
    rw [step_of_subtract hcan1, hsub1]

  have hsub2 : escapeX1 s m - (s + 2) = escapeX2 s m := by
    simp [escapeX1, escapeX2]
    omega
  have hcan2 : CanSubtract (s + 2)
      ⟨escapeX1 s m,
        escapeX1 s m :: escapeAfterAddition s m :: state.seen⟩ := by
    constructor
    · simp [escapeX1]
      omega
    · rw [hsub2]
      simp only [List.mem_cons, not_or]
      constructor
      · simp [escapeX1, escapeX2]
        omega
      · constructor
        · simp [escapeAfterAddition, escapeX2]
          omega
        · exact h.x2_fresh
  have hstep2 : step (s + 2)
      ⟨escapeX1 s m,
        escapeX1 s m :: escapeAfterAddition s m :: state.seen⟩ =
      ⟨escapeX2 s m,
        escapeX2 s m :: escapeX1 s m ::
          escapeAfterAddition s m :: state.seen⟩ := by
    rw [step_of_subtract hcan2, hsub2]

  have hsub3 : escapeX2 s m - (s + 3) = m := by
    simp [escapeX2]
  have hcan3 : CanSubtract (s + 3)
      ⟨escapeX2 s m,
        escapeX2 s m :: escapeX1 s m ::
          escapeAfterAddition s m :: state.seen⟩ := by
    constructor
    · simp [escapeX2]
      have hmpos := h.m_pos
      omega
    · rw [hsub3]
      simp only [List.mem_cons, not_or]
      constructor
      · simp [escapeX2]
        omega
      · constructor
        · simp [escapeX1]
          omega
        · constructor
          · simp [escapeAfterAddition]
            omega
          · exact h.m_fresh
  have hstep3 : step (s + 3)
      ⟨escapeX2 s m,
        escapeX2 s m :: escapeX1 s m ::
          escapeAfterAddition s m :: state.seen⟩ =
      ⟨m, m :: escapeX2 s m :: escapeX1 s m ::
        escapeAfterAddition s m :: state.seen⟩ := by
    rw [step_of_subtract hcan3, hsub3]

  rw [hstep0, hstep1, hstep2, hstep3]
  simp

/-- The endpoint form of the local escape theorem. -/
theorem localEscape_lands {s m : Nat} {state : State}
    (h : EscapeAssumptions s m state) :
    (step (s + 3)
      (step (s + 2) (step (s + 1) (step s state)))).value = m :=
  (localEscape_trace h).2.2.2

/-- The coordinate jump attached to the same local family. -/
theorem localEscape_coordinate_jump {s m : Nat} {state : State}
    (h : EscapeAssumptions s m state) :
    QuotRem (s - 1) state.value 2 (m + 8) ∧
      potential 2 (m + 8) = Int.ofNat (m + 5) ∧
    QuotRem s (escapeAfterAddition s m) 3 (m + 6) ∧
      potential 3 (m + 6) = Int.ofNat m := by
  constructor
  · rw [h.value_eq]
    exact preEscape_quotRem h.s_large
  · exact ⟨preEscape_potential m,
      postAddition_quotRem h.s_large, postAddition_potential m⟩

end Recaman
