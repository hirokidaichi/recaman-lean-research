import Recaman.History

namespace Recaman

/-- Total amount removed by j consecutive subtraction steps beginning after
time f: jf + U(j). -/
def descentDrop (f j : Nat) : Nat := j * f + upperTri j

theorem descentDrop_succ (f j : Nat) :
    descentDrop f (j + 1) = descentDrop f j + (f + j + 1) := by
  simp [descentDrop, upperTri, Nat.succ_mul]
  omega

theorem upperTri_mono {i j : Nat} (hij : i ≤ j) :
    upperTri i ≤ upperTri j := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with heq | hlt
      · subst i
        exact Nat.le_refl _
      · have hprev := ih (Nat.le_of_lt_succ hlt)
        simp [upperTri]
        omega

theorem descentDrop_mono (f : Nat) {i j : Nat} (hij : i ≤ j) :
    descentDrop f i ≤ descentDrop f j := by
  have hmul : i * f ≤ j * f := Nat.mul_le_mul_right f hij
  have htri : upperTri i ≤ upperTri j := upperTri_mono hij
  simp only [descentDrop]
  omega

theorem a_succ_of_canSubtract {n : Nat}
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    a (n + 1) = a n - (n + 1) := by
  simp [a, stateAt, step_of_subtract hcan]

/-- A legal subtraction always lands on a genuinely new value, so the next
time is its first occurrence. -/
theorem firstAt_succ_of_canSubtract {n : Nat}
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    FirstAt a (a (n + 1)) (n + 1) := by
  have hnext := a_succ_of_canSubtract hcan
  constructor
  · rfl
  · intro u hu hua
    apply hcan.2
    apply mem_valuesThrough_iff.mpr
    exact ⟨u, Nat.le_of_lt_succ hu, hua.trans hnext⟩

/-- An actual initial segment of consecutive subtraction steps on the Recamán
orbit, starting from value v at time f. -/
structure DescentRun (f v length : Nat) : Prop where
  start_value : a f = v
  subtracts : ∀ i, i < length →
    CanSubtract (f + i + 1) (stateAt (f + i))

/-- A legal subtraction immediately before a descent run extends the run by
one step backwards. -/
theorem DescentRun.prepend {f length : Nat}
    (run : DescentRun f (a f) length)
    (hf : 0 < f)
    (hprevious : CanSubtract f (stateAt (f - 1))) :
    DescentRun (f - 1) (a (f - 1)) (length + 1) := by
  constructor
  · rfl
  · intro i hi
    cases f with
    | zero => omega
    | succ u =>
        cases i with
        | zero =>
            simpa using hprevious
        | succ j =>
            have hj : j < length := by omega
            have hstep := run.subtracts j hj
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep

/-- Every finite descent run has a maximal backward extension ending at the
same time.  The extension either reaches time zero or begins immediately
after a forced addition. -/
theorem DescentRun.maximal_backward_extension {f length : Nat}
    (run : DescentRun f (a f) length) :
    ∃ start totalLength,
      start + totalLength = f + length ∧
      length ≤ totalLength ∧
      DescentRun start (a start) totalLength ∧
      (start = 0 ∨ ¬ CanSubtract start (stateAt (start - 1))) := by
  induction f using Nat.strongRecOn generalizing length with
  | ind f ih =>
      by_cases hfzero : f = 0
      · subst f
        exact ⟨0, length, by omega, by omega, run, Or.inl rfl⟩
      · have hfpos : 0 < f := by omega
        by_cases hprevious : CanSubtract f (stateAt (f - 1))
        · have hrun := run.prepend hfpos hprevious
          rcases ih (f - 1) (by omega) hrun with
            ⟨start, totalLength, hend, hlength, hmaxrun, hmaximal⟩
          exact ⟨start, totalLength, by omega, by omega,
            hmaxrun, hmaximal⟩
        · exact ⟨f, length, by omega, by omega, run, Or.inr hprevious⟩

/-- Exact triangular-number formula at every point of an actual descent. -/
theorem DescentRun.equation_at {f v length : Nat}
    (run : DescentRun f v length) {i : Nat} (hi : i ≤ length) :
    a (f + i) + descentDrop f i = v := by
  induction i with
  | zero =>
      simpa [descentDrop, upperTri] using run.start_value
  | succ i ih =>
      have hi_lt : i < length := by omega
      have hcan := run.subtracts i hi_lt
      have hpositive : f + i + 1 < a (f + i) := by
        simpa [a] using hcan.1
      have hprevious := ih (by omega)
      have hstep := a_succ_of_canSubtract hcan
      have hdrop := descentDrop_succ f i
      change a ((f + i) + 1) + descentDrop f (i + 1) = v
      omega

/-- The first blocked subtraction immediately following an actual descent.
The blocker candidate is positive and was already present in the real stored
history, so the Recamán rule will add instead of subtracting. -/
structure ActualBlocker (f v length y : Nat) : Prop where
  first_v : FirstAt a v f
  run : DescentRun f v length
  blocker_positive : f + length + 1 < a (f + length)
  blocker_candidate : a (f + length) - (f + length + 1) = y
  blocker_seen : y ∈ valuesThrough (f + length)

theorem ActualBlocker.y_pos {f v length y : Nat}
    (blocker : ActualBlocker f v length y) : 0 < y := by
  have hpositive := blocker.blocker_positive
  have hcandidate := blocker.blocker_candidate
  omega

/-- The abstract blocker equation is derived from actual consecutive Recamán
subtractions, rather than assumed independently. -/
theorem ActualBlocker.blocker_eq_drop {f v length y : Nat}
    (blocker : ActualBlocker f v length y) :
    y + descentDrop f (length + 1) = v := by
  have hfinal := blocker.run.equation_at (i := length) (Nat.le_refl _)
  have hdrop := descentDrop_succ f length
  have hpositive := blocker.blocker_positive
  have hcandidate := blocker.blocker_candidate
  omega

/-- Every value in the current descending interval is strictly above the
eventual blocker candidate. -/
theorem ActualBlocker.above_during_descent {f v length y : Nat}
    (blocker : ActualBlocker f v length y) :
    ∀ t, f ≤ t → t < f + (length + 1) → y < a t := by
  intro t hft htend
  let i := t - f
  have htime : f + i = t := by
    simp [i]
    omega
  have hi : i ≤ length := by
    simp [i]
    omega
  have heq_i := blocker.run.equation_at (i := i) hi
  rw [htime] at heq_i
  have heq_final := blocker.run.equation_at
    (i := length) (Nat.le_refl _)
  have hdrop_le : descentDrop f i ≤ descentDrop f length :=
    descentDrop_mono f hi
  have hy_final : y < a (f + length) := by
    have hpositive := blocker.blocker_positive
    have hcandidate := blocker.blocker_candidate
    omega
  omega

theorem ActualBlocker.seen_before_block {f v length y : Nat}
    (blocker : ActualBlocker f v length y) :
    SeenBefore a y (f + (length + 1)) := by
  simpa [Nat.add_assoc] using
    (seenBefore_succ_iff (x := y) (n := f + length)).mpr blocker.blocker_seen

/-- The certified blocker really forces the addition branch of the Recamán
recurrence at the next step. -/
theorem ActualBlocker.forces_addition {f v length y : Nat}
    (blocker : ActualBlocker f v length y) :
    a (f + (length + 1)) =
      a (f + length) + (f + length + 1) := by
  have hseen :
      (stateAt (f + length)).value - (f + length + 1) ∈
        (stateAt (f + length)).seen := by
    change a (f + length) - (f + length + 1) ∈
      valuesThrough (f + length)
    rw [blocker.blocker_candidate]
    exact blocker.blocker_seen
  have hstep := step_of_seen hseen
  have hvalue := congrArg State.value hstep
  simpa [a, stateAt, Nat.add_assoc] using hvalue

/-- Main bridge theorem: every actual blocker configuration constructs the
abstract certificate used by the double-descent and well-foundedness results. -/
theorem ActualBlocker.exists_certificate {f v length y : Nat}
    (blocker : ActualBlocker f v length y) :
    ∃ certificate : BlockerCertificate a,
      certificate.v = v ∧ certificate.y = y ∧
      certificate.f = f ∧ certificate.k = length + 1 := by
  rcases history_member_has_firstAt blocker.blocker_seen with
    ⟨fy, _, hfirst_y⟩
  let certificate : BlockerCertificate a := {
    v := v
    y := y
    f := f
    fy := fy
    k := length + 1
    first_v := blocker.first_v
    first_y := hfirst_y
    k_pos := by omega
    y_pos := blocker.y_pos
    blocker_eq := by
      simpa [descentDrop] using blocker.blocker_eq_drop
    seen_before_block := blocker.seen_before_block
    above_during_descent := blocker.above_during_descent
  }
  exact ⟨certificate, rfl, rfl, rfl, rfl⟩

/-- Concrete double descent on the real Recamán orbit. -/
theorem ActualBlocker.doubleDescent {f v length y : Nat}
    (blocker : ActualBlocker f v length y) :
    y < v ∧ ∃ fy, FirstAt a y fy ∧ fy < f := by
  rcases blocker.exists_certificate with
    ⟨certificate, hv, hy, hf, _⟩
  have hvalue := certificate.value_decreases
  have htime := certificate.first_time_decreases
  have hfirst : FirstAt a y certificate.fy := by
    simpa [hy] using certificate.first_y
  constructor
  · simpa [hv, hy] using hvalue
  · exact ⟨certificate.fy, hfirst, by simpa [hf] using htime⟩

end Recaman
