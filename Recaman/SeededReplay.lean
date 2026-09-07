import Recaman.Basic

namespace Recaman.SeededReplay

/-- Actual greedy continuation from an arbitrary finite state at clock b. -/
def run (b : Nat) (s : State) : Nat → State
  | 0 => s
  | t+1 => step (b+t+1) (run b s t)

def value (b : Nat) (s : State) (t : Nat) : Int := (run b s t).value

def Seen (b : Nat) (s : State) (t : Nat) (y : Int) : Prop :=
  ∃ z ∈ (run b s t).seen, (z : Int) = y

theorem seen_succ (b : Nat) (s : State) (t : Nat) (y : Int) :
    Seen b s (t+1) y ↔ y = value b s (t+1) ∨ Seen b s t y := by
  constructor
  · rintro ⟨z, hz, heq⟩
    change z ∈ nextValue (b+t+1) (run b s t) :: (run b s t).seen at hz
    rcases List.mem_cons.mp hz with hz | hz
    · left
      subst z
      exact heq.symm
    · exact Or.inr ⟨z, hz, heq⟩
  · rintro (heq | ⟨z, hz, heq⟩)
    · exact ⟨(run b s (t+1)).value, step_value_mem_seen _ _, heq.symm⟩
    · exact ⟨z, List.mem_cons.mpr (Or.inr hz), heq⟩

theorem seen_mono {b : Nat} {s : State} {i j : Nat} {y : Int}
    (hij : i ≤ j) (hy : Seen b s i y) : Seen b s j y := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    simpa [this] using hy
  | succ j ih =>
    by_cases h : i ≤ j
    · exact (seen_succ b s j y).mpr (Or.inr (ih h))
    · have : i = j+1 := by omega
      simpa [this] using hy

theorem seen_value {b : Nat} {s : State} (h : s.value ∈ s.seen) (t : Nat) :
    Seen b s t (value b s t) := by
  cases t with
  | zero => exact ⟨s.value, h, rfl⟩
  | succ t => exact (seen_succ b s t _).mpr (Or.inl rfl)

/-- Integer equations are checked against the real natural-number step. -/
theorem subtract {b : Nat} {s : State} {t : Nat} {z : Int}
    (hz : 0 < z) (hv : value b s t = z + (b+t+1 : Nat))
    (hfresh : ¬ Seen b s t z) : value b s (t+1) = z := by
  have hzt : (z.toNat : Int) = z := Int.toNat_of_nonneg (by omega)
  have hv' : ((run b s t).value : Int) = z + (b+t+1 : Nat) := hv
  have hc : CanSubtract (b+t+1) (run b s t) := by
    constructor
    · omega
    · intro hm
      apply hfresh
      refine ⟨(run b s t).value - (b+t+1), hm, ?_⟩
      omega
  have hs := step_of_subtract hc
  change ((step (b+t+1) (run b s t)).value : Int) = z
  rw [hs]
  dsimp
  omega

theorem add {b : Nat} {s : State} {t : Nat}
    (h : value b s t ≤ (b+t+1 : Nat) ∨
      Seen b s t (value b s t - (b+t+1 : Nat))) :
    value b s (t+1) = value b s t + (b+t+1 : Nat) := by
  have hnot : ¬ CanSubtract (b+t+1) (run b s t) := by
    rintro ⟨hp, hf⟩
    rcases h with h | ⟨z, hz, heq⟩
    · change ((run b s t).value : Int) ≤ (b+t+1 : Nat) at h
      omega
    · change (z : Int) = ((run b s t).value : Int) - (b+t+1 : Nat) at heq
      have he : (run b s t).value - (b+t+1) = z := by omega
      exact hf (he ▸ hz)
  change ((step (b+t+1) (run b s t)).value : Int) = _
  simp only [step, nextValue, if_neg hnot, Int.natCast_add]
  rfl

/-- Positive blocked candidates are exactly the additions of the actual step. -/
theorem seen_iff_add {b : Nat} {s : State} {t : Nat}
    (hn : 0<b+t+1) (hp : (b+t+1 : Nat)<value b s t) :
    Seen b s t (value b s t-(b+t+1 : Nat)) ↔
      value b s (t+1)=value b s t+(b+t+1 : Nat) := by
  constructor
  · intro h
    exact add (Or.inr h)
  · intro he
    apply Classical.byContradiction
    intro hf
    have hs := subtract (b := b) (s := s) (t := t)
      (z := value b s t-(b+t+1 : Nat)) (by omega) (by omega) hf
    omega

end Recaman.SeededReplay
