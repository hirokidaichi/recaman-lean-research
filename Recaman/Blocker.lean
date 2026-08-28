import Recaman.Coordinates

namespace Recaman

/-- x occurs for the first time at t in seq. -/
def FirstAt (seq : Nat → Nat) (x t : Nat) : Prop :=
  seq t = x ∧ ∀ u, u < t → seq u ≠ x

/-- x has occurred strictly before time t. -/
def SeenBefore (seq : Nat → Nat) (x t : Nat) : Prop :=
  ∃ u, u < t ∧ seq u = x

theorem upperTri_pos {k : Nat} (hk : 0 < k) : 0 < upperTri k := by
  cases k with
  | zero => omega
  | succ j =>
      simp [upperTri]

/-- Abstract certificate for a blocker met during a descending run.

The equation is the subtraction arithmetic y = v - kf - U(k), written
without truncated subtraction.  The interval condition says that y did not
occur inside the current descent before becoming the blocker. -/
structure BlockerCertificate (seq : Nat → Nat) where
  v : Nat
  y : Nat
  f : Nat
  fy : Nat
  k : Nat
  first_v : FirstAt seq v f
  first_y : FirstAt seq y fy
  k_pos : 0 < k
  y_pos : 0 < y
  blocker_eq : y + (k * f + upperTri k) = v
  seen_before_block : SeenBefore seq y (f + k)
  above_during_descent : ∀ t, f ≤ t → t < f + k → y < seq t

theorem BlockerCertificate.value_decreases {seq : Nat → Nat}
    (certificate : BlockerCertificate seq) : certificate.y < certificate.v := by
  have htri : 0 < upperTri certificate.k :=
    upperTri_pos certificate.k_pos
  have hdrop : 0 < certificate.k * certificate.f + upperTri certificate.k := by
    omega
  calc
    certificate.y < certificate.y +
        (certificate.k * certificate.f + upperTri certificate.k) :=
      Nat.lt_add_of_pos_right hdrop
    _ = certificate.v := certificate.blocker_eq

/-- A genuine blocker was first seen before the first occurrence of the
current value.  This is the time component of the double-descent lemma. -/
theorem BlockerCertificate.first_time_decreases {seq : Nat → Nat}
    (certificate : BlockerCertificate seq) : certificate.fy < certificate.f := by
  rcases certificate.seen_before_block with ⟨u, hu_before, hu_value⟩
  have hfy_le_u : certificate.fy ≤ u := by
    apply Nat.le_of_not_gt
    intro hu_lt_fy
    exact (certificate.first_y.2 u hu_lt_fy) hu_value
  have hfy_before_block : certificate.fy < certificate.f + certificate.k :=
    Nat.lt_of_le_of_lt hfy_le_u hu_before
  have hnot : ¬ certificate.f ≤ certificate.fy := by
    intro hf_le_fy
    have habove := certificate.above_during_descent certificate.fy
      hf_le_fy hfy_before_block
    rw [certificate.first_y.1] at habove
    exact (Nat.lt_irrefl certificate.y) habove
  exact Nat.lt_of_not_ge hnot

/-- A node carrying both quantities decreased by a blocker. -/
structure Occurrence where
  value : Nat
  time : Nat
deriving Repr, DecidableEq

def EarlierSmaller (child parent : Occurrence) : Prop :=
  child.value < parent.value ∧ child.time < parent.time

/-- No infinite blocker ancestry is possible: value alone is already a
well-founded measure, while every blocker edge also decreases time. -/
theorem earlierSmaller_wellFounded : WellFounded EarlierSmaller := by
  apply Subrelation.wf (r := (measure Occurrence.value).rel)
  · intro child parent h
    exact h.1
  · exact (measure Occurrence.value).wf

theorem BlockerCertificate.earlierSmaller {seq : Nat → Nat}
    (certificate : BlockerCertificate seq) :
    EarlierSmaller ⟨certificate.y, certificate.fy⟩
      ⟨certificate.v, certificate.f⟩ := by
  exact ⟨certificate.value_decreases, certificate.first_time_decreases⟩

end Recaman
