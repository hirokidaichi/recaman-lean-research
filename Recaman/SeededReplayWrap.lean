import Recaman.SeededReplay

namespace Recaman.SeededReplay

theorem numeric_step (b : Nat) (s : State) (t : Nat) :
    value b s (t+1)=value b s t+(b+t+1 : Nat) ∨
    (value b s t>(b+t+1 : Nat) ∧ value b s (t+1)=value b s t-(b+t+1 : Nat)) := by
  by_cases hc : CanSubtract (b+t+1) (run b s t)
  · right
    have hs := step_of_subtract hc
    have hp := hc.1
    change ((run b s t).value : Int) > (b+t+1 : Nat) ∧
      ((step (b+t+1) (run b s t)).value : Int)=((run b s t).value : Int)-(b+t+1 : Nat)
    rw [hs]
    dsimp
    omega
  · left
    change ((step (b+t+1) (run b s t)).value : Int)=((run b s t).value : Int)+(b+t+1 : Nat)
    simp [step, nextValue, hc]

theorem triangular_bound {b : Nat} {s : State}
    (hstart : 2*(s.value : Int) ≤ (b : Int)*(b+1)) (t : Nat) :
    2*value b s t ≤ (b+t : Nat)*(b+t+1 : Nat) := by
  induction t with
  | zero => simpa [value, run] using hstart
  | succ t ih =>
    have hs := numeric_step b s t
    have hn : 0 ≤ (b+t+1 : Nat) := by omega
    simp only [Int.natCast_add, Int.natCast_one] at *
    rcases hs with hs | ⟨hp, hs⟩ <;> grind

private theorem quotient_bound {x n : Int} (hn : 0<n) (hx : 0≤x)
    (ht : 2*x≤n*(n+1)) : 0≤x/n ∧ x/n≤n := by
  have hp := Int.mul_pos hn (show 0<n+1 by omega)
  have hlt : x<(n+1)*n := by grind
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr hlt
  exact ⟨Int.ediv_nonneg hx (by omega), by omega⟩

/-- Before a wrap, the residue loses exactly the old level. -/
theorem residue_transition {x y n : Int} (hn : 0<n) (hx : 0≤x)
    (ht : 2*x≤n*(n+1))
    (hy : y=x+(n+1) ∨ y=x-(n+1))
    (hnw : y%(n+1)≤x%n) : y%(n+1)=x%n-x/n := by
  have hq := quotient_bound hn hx ht
  have hr := Int.emod_nonneg x (show n≠0 by omega)
  have hrn := Int.emod_lt_of_pos x hn
  have he := Int.emod_add_ediv_mul x n
  have hm : y%(n+1)=(x%n-x/n)%(n+1) := by
    have hm' : y%(n+1)=x%(n+1) := by
      rcases hy with hy | hy <;> rw [hy] <;> simp
    rw [hm']
    have hex : x=(x%n-x/n)+(n+1)*(x/n) := by grind
    calc
      x%(n+1)=((x%n-x/n)+(n+1)*(x/n))%(n+1) := congrArg (fun z => z%(n+1)) hex
      _ = _ := by rw [Int.add_mul_emod_self_left]
  by_cases h : x/n≤x%n
  · rw [hm, Int.emod_eq_of_lt (by omega) (by omega)]
  · have hlow : 0 ≤ x%n-x/n+(n+1) := by omega
    have hhi : x%n-x/n+(n+1)<n+1 := by omega
    have heq := Int.emod_eq_of_lt hlow hhi
    rw [Int.add_emod_right] at heq
    omega

 theorem zero_level_next {b : Nat} {s : State} {t : Nat}
    (hb : 0<b+t) (hq : value b s t/(b+t : Nat)=0) :
    value b s (t+1)/(b+t+1 : Nat)=1 := by
  have hx : 0≤value b s t := by unfold value; omega
  have hn : (0 : Int)<(b+t : Nat) := by omega
  have hlt := (Int.ediv_lt_iff_lt_mul hn).mp (show value b s t/(b+t : Nat)<1 by omega)
  have hs := numeric_step b s t
  have hy : value b s (t+1)=value b s t+(b+t+1 : Nat) := by
    rcases hs with h | ⟨hp, h⟩
    · exact h
    · simp only [Int.one_mul] at hlt
      omega
  have he : value b s t+(b+t+1 : Nat)=value b s t+(b+t+1 : Nat)*1 := by omega
  rw [hy, he, Int.add_mul_ediv_left _ _ (by omega)]
  have hz : value b s t/(b+t+1 : Nat)=0 := Int.ediv_eq_zero_of_lt hx (by omega)
  omega

/-- A finite triangularly bounded greedy state cannot remain forever in one no-wrap arc. -/
theorem exists_later_wrap {b : Nat} {s : State} (hb : 0<b)
    (hstart : 2*(s.value : Int) ≤ (b : Int)*(b+1)) (L : Nat) :
    ∃ t, L≤t ∧ value b s t%(b+t : Nat)<value b s (t+1)%(b+t+1 : Nat) := by
  apply Classical.byContradiction
  intro h
  have hnw (t : Nat) (ht : L≤t) :
      value b s (t+1)%(b+t+1 : Nat)≤value b s t%(b+t : Nat) := by
    apply Classical.byContradiction
    intro hh
    apply h
    exact ⟨t, ht, by omega⟩
  have hdrop (t : Nat) (ht : L≤t) :
      value b s (t+2)%(b+t+2 : Nat)+1≤value b s t%(b+t : Nat) := by
    have hx : 0≤value b s t := by unfold value; omega
    have hx' : 0≤value b s (t+1) := by unfold value; omega
    have hs := numeric_step b s t
    have hs' := numeric_step b s (t+1)
    have he := residue_transition (x := value b s t) (y := value b s (t+1))
      (n := (b+t : Nat)) (by omega) hx (triangular_bound hstart t)
      (by rcases hs with hs | ⟨_, hs⟩ <;> simp only [Int.natCast_add, Int.natCast_one] at * <;> omega)
      (by simpa only [Int.natCast_add, Int.natCast_one] using hnw t ht)
    have he' := residue_transition (x := value b s (t+1)) (y := value b s (t+2))
      (n := (b+t+1 : Nat)) (by omega) hx' (by simpa [Nat.add_assoc, Int.add_assoc] using triangular_bound hstart (t+1))
      (by rcases hs' with hs' | ⟨_, hs'⟩ <;> simp [Nat.add_assoc, Int.add_assoc] at * <;> omega)
      (by simpa [Nat.add_assoc, Int.add_assoc] using hnw (t+1) (by omega))
    have hq := Int.ediv_nonneg hx (show (0 : Int)≤(b+t : Nat) by omega)
    have hq' := Int.ediv_nonneg hx' (show (0 : Int)≤(b+t+1 : Nat) by omega)
    by_cases hz : value b s t/(b+t : Nat)=0
    · have hz' := zero_level_next (b := b) (s := s) (t := t) (by omega) hz
      simp [Nat.add_assoc, Int.add_assoc] at *
      omega
    · simp [Nat.add_assoc, Int.add_assoc] at *
      omega
  have hiter (k : Nat) : value b s (L+2*k)%(b+(L+2*k) : Nat)+(k : Int) ≤
      value b s L%(b+L : Nat) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hdrop (L+2*k) (by omega)
      have he : L+2*(k+1)=(L+2*k)+2 := by omega
      rw [he]
      simp [Nat.add_assoc] at *
      omega
  let r := value b s L%(b+L : Nat)
  have hr : 0≤r := Int.emod_nonneg _ (by omega)
  have hr' : (r.toNat : Int)=r := Int.toNat_of_nonneg hr
  have hh := hiter (r.toNat+1)
  have hpos := Int.emod_nonneg (value b s (L+2*(r.toNat+1)))
    (show ((b+(L+2*(r.toNat+1)) : Nat) : Int)≠0 by omega)
  omega

end Recaman.SeededReplay
