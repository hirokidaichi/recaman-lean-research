import Recaman.LeadingRunSupply
import Recaman.SuffixHallOwnerMap

namespace Recaman.CleanWindowCapacity

open Recaman.LeadingRunSupply
open Recaman.SuffixHallOwnerMap (clocks mem_clocks clocks_nodup nodup_map_of_inj)
open ShortPeriodicSupply (sign)

/-! # The Clean Window Theorem

For a window `[b-L, b-1]` with base clock `t = b-L`, the walk
`G(t+j) = mass (past e (t+j) j)` measures the level relative to `F(t)` and
`moment (past e (t+j) j)` is the area potential. A window is *clean* when every
return of the walk to the base level strictly inside the window has strictly
negative area potential.

The main theorem `clean_capacity` says: on an interval `[q, q+n)`, any family of
additions each owning a clean P2 window lying at or after `q` is no larger than
the number of subtractions in the interval. So the line capacity conjecture H
(E-369) holds on every interval all of whose endable clocks have a clean
(minimal) window. On paper every minimal window with at most one adjacent SS
pair is clean, so this extends the E-128 endpoint injection (window end ↦
window start); that implication is not formalized here. Conjecture H in
general is NOT proved here.
-/

/-- Every return of the walk to the base level strictly inside the window
`[b-L, b-1]` has strictly negative area potential. -/
def Clean (e : Int → Bool) (b : Int) (L : Nat) : Prop :=
  ∀ j : Nat, 0 < j → j < L →
    mass (past e (b - (L : Int) + (j : Int)) j) = 0 →
      moment (past e (b - (L : Int) + (j : Int)) j) < 0

/-! ## A pure walk lemma -/

/-- From a base index `k` where the level and area are both at least one, the
walk either returns to level zero with area at least one, or stays at level
at least one with area at least one. -/
theorem walk_return (g m : Nat → Int)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (k : Nat) (hg : 1 ≤ g k) (hm : 1 ≤ m k) :
    ∀ n : Nat, (∃ i, i ≤ n ∧ g (k+i) = 0 ∧ 1 ≤ m (k+i)) ∨
      (1 ≤ g (k+n) ∧ 1 ≤ m (k+n))
  | 0 => Or.inr ⟨hg, hm⟩
  | n+1 => by
      rcases walk_return g m hstep harea k hg hm n with ⟨i, hi, h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inl ⟨i, by omega, h0, h1⟩
      · have hs := hstep (k+n)
        have ha := harea (k+n)
        have e1 : k + (n+1) = k + n + 1 := by omega
        by_cases hz : g (k+n+1) = 0
        · refine Or.inl ⟨n+1, Nat.le_refl _, ?_, ?_⟩ <;> rw [e1] <;> omega
        · refine Or.inr ⟨?_, ?_⟩ <;> rw [e1] <;> omega

/-- If the walk starts with level and area at least one at `k ≤ N`, ends at
level one with area zero at `N`, then some strict interior return `j`
(`k ≤ j < N`) has level zero and positive area. -/
theorem walk_bad_return (g m : Nat → Int)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (k N : Nat) (hkN : k ≤ N) (hg : 1 ≤ g k) (hm : 1 ≤ m k)
    (hgN : g N = 1) (hmN : m N = 0) :
    ∃ j, k ≤ j ∧ j < N ∧ g j = 0 ∧ 1 ≤ m j := by
  have hN : k + (N - k) = N := by omega
  rcases walk_return g m hstep harea k hg hm (N - k) with ⟨i, hi, h0, h1⟩ | ⟨_, h1⟩
  · refine ⟨k+i, by omega, ?_, h0, h1⟩
    by_cases heq : k + i = N
    · rw [heq] at h0; omega
    · omega
  · rw [hN] at h1; omega

/-! ## The window walk -/

theorem past_succ (e : Int → Bool) (t : Int) (j : Nat) :
    past e (t + ((j+1 : Nat) : Int)) (j+1) = e (t + (j : Int)) :: past e (t + (j : Int)) j := by
  rw [Nat.add_comm j 1, past_append]
  have h1 : past e (t + ((1+j : Nat) : Int)) 1 = [e (t + (j : Int))] := by
    simp only [past, List.range_one, List.map_cons, List.map_nil]
    congr 2
    omega
  have h2 : t + ((1+j : Nat) : Int) - ((1 : Nat) : Int) = t + (j : Int) := by omega
  rw [h1, h2]
  rfl

theorem sign_cases (b : Bool) : sign b = 1 ∨ sign b = -1 := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem window_step (e : Int → Bool) (t : Int) (j : Nat) :
    mass (past e (t + ((j+1 : Nat) : Int)) (j+1)) =
        mass (past e (t + (j : Int)) j) + 1 ∨
      mass (past e (t + ((j+1 : Nat) : Int)) (j+1)) =
        mass (past e (t + (j : Int)) j) - 1 := by
  rw [past_succ, mass_cons]
  rcases sign_cases (e (t + (j : Int))) with h | h <;> rw [h] <;> omega

theorem window_area (e : Int → Bool) (t : Int) (j : Nat) :
    moment (past e (t + ((j+1 : Nat) : Int)) (j+1)) =
      moment (past e (t + (j : Int)) j) + mass (past e (t + ((j+1 : Nat) : Int)) (j+1)) := by
  rw [past_succ, mass_cons]
  show sign _ + mass _ + moment _ = _
  omega

theorem window_mass_A (e : Int → Bool) (t : Int) (j : Nat) (h : e (t + (j : Int)) = true) :
    mass (past e (t + ((j+1 : Nat) : Int)) (j+1)) = mass (past e (t + (j : Int)) j) + 1 := by
  rw [past_succ, mass_cons, h]
  show (1 : Int) + _ = _
  omega

theorem past_rebase (e : Int → Bool) (b t : Int) (L : Nat) (h : b = t + (L : Int)) :
    past e b L = past e (t + (L : Int)) L := by rw [h]

theorem p2_pos (w : List Bool) (h : P2 w) : 0 < w.length := by
  cases w with
  | nil => exact absurd h.1 (by simp)
  | cons _ _ => simp

/-! ## Lemma A and Lemma B -/

/-- Lemma A: a clean P2 window starts with a subtraction. -/
theorem clean_start_S (e : Int → Bool) (b : Int) (L : Nat)
    (hp : P2 (past e b L)) (hc : Clean e b L) : e (b - (L : Int)) = false := by
  apply Classical.byContradiction
  intro hne
  have hA : e (b - (L : Int)) = true := by
    cases h : e (b - (L : Int))
    · exact absurd h hne
    · rfl
  have hL : 0 < L := by have := p2_pos _ hp; simpa [past] using this
  let t : Int := b - (L : Int)
  let g : Nat → Int := fun j => mass (past e (t + (j : Int)) j)
  let m : Nat → Int := fun j => moment (past e (t + (j : Int)) j)
  have hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1 := fun j => window_step e t j
  have harea : ∀ j, m (j+1) = m j + g (j+1) := fun j => window_area e t j
  have hg0 : g 0 = 0 := by simp [g, past]
  have hm0 : m 0 = 0 := by simp [m, past, moment]
  have hg1 : g 1 = 1 := by
    have := window_mass_A e t 0 (by simpa [t] using hA)
    simp only [g]; rw [this]; exact (by have := hg0; simp only [g] at this; omega)
  have hm1 : m 1 = 1 := by have := harea 0; simp only [Nat.zero_add] at this; omega
  have hreb := past_rebase e b t L (by simp [t])
  have hgN : g L = 1 := by simp only [g]; rw [← hreb]; exact hp.1
  have hmN : m L = 0 := by simp only [m]; rw [← hreb]; exact hp.2
  obtain ⟨j, hj1, hjN, hgj, hmj⟩ :=
    walk_bad_return g m hstep harea 1 L hL (by omega) (by omega) hgN hmN
  have hrw : b - (L : Int) + (j : Int) = t + (j : Int) := rfl
  have := hc j (by omega) hjN (by rw [hrw]; exact hgj)
  rw [hrw] at this
  simp only [m] at hmj
  omega

/-- Lemma B: if an addition `b` ends a P2 window and a later clock `b'` ends a
P2 window with the same start, then the later window is not clean. -/
theorem clean_not_shared (e : Int → Bool) (b b' : Int) (L L' : Nat)
    (hlt : b < b') (hstart : b - (L : Int) = b' - (L' : Int))
    (hp : P2 (past e b L)) (hA : e b = true) (hp' : P2 (past e b' L')) :
    ¬ Clean e b' L' := by
  intro hc
  let t : Int := b - (L : Int)
  let g : Nat → Int := fun j => mass (past e (t + (j : Int)) j)
  let m : Nat → Int := fun j => moment (past e (t + (j : Int)) j)
  have hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1 := fun j => window_step e t j
  have harea : ∀ j, m (j+1) = m j + g (j+1) := fun j => window_area e t j
  have hreb := past_rebase e b t L (by simp [t])
  have hreb' := past_rebase e b' t L' (by simp only [t]; omega)
  have hgL : g L = 1 := by simp only [g]; rw [← hreb]; exact hp.1
  have hmL : m L = 0 := by simp only [m]; rw [← hreb]; exact hp.2
  have hgN : g L' = 1 := by simp only [g]; rw [← hreb']; exact hp'.1
  have hmN : m L' = 0 := by simp only [m]; rw [← hreb']; exact hp'.2
  have hgL1 : g (L+1) = 2 := by
    have := window_mass_A e t L (by simp only [t]; rw [show b - (L : Int) + (L : Int) = b by omega]; exact hA)
    simp only [g]; rw [this]; simp only [g] at hgL; omega
  have hmL1 : m (L+1) = 2 := by have := harea L; omega
  obtain ⟨j, _, hjN, hgj, hmj⟩ :=
    walk_bad_return g m hstep harea (L+1) L' (by omega) (by omega) (by omega) hgN hmN
  have hj0 : 0 < j := by omega
  have hrw : b' - (L' : Int) + (j : Int) = t + (j : Int) := by simp only [t]; omega
  have := hc j hj0 hjN (by rw [hrw]; exact hgj)
  rw [hrw] at this
  simp only [m] at hmj
  omega

/-! ## The Clean Window Theorem -/

/-- **Clean Window Theorem.** Let `B` be a duplicate-free list of additions in
`[q, q+n)`, each `b` owning a clean P2 window of length `lag b` that lies at or
after `q`. Then `B` is no longer than the list of subtractions in `[q, q+n)`.

Hence the line capacity conjecture H (E-369) holds on every interval all of
whose endable clocks have a clean minimal window; this extends the E-128
endpoint injection `b ↦ b - lag b`. Conjecture H in general is NOT proved.
(No minimality of the windows is needed.) -/
theorem clean_capacity (e : Int → Bool) (q : Int) (n : Nat) (B : List Int)
    (hB : B.Nodup) (lag : Int → Nat)
    (h : ∀ b ∈ B, q ≤ b - (lag b : Int) ∧ b < q + (n : Int) ∧ e b = true ∧
      P2 (past e b (lag b)) ∧ Clean e b (lag b)) :
    B.length ≤ ((clocks q n).filter (fun c => e c = false)).length := by
  let start : Int → Int := fun b => b - (lag b : Int)
  have hinj : ∀ a ∈ B, ∀ b ∈ B, start a = start b → a = b := by
    intro a ha b hb hab
    obtain ⟨_, _, hAa, hpa, hca⟩ := h a ha
    obtain ⟨_, _, hAb, hpb, hcb⟩ := h b hb
    apply Classical.byContradiction
    intro hne
    by_cases hlt : a < b
    · exact clean_not_shared e a b (lag a) (lag b) hlt hab hpa hAa hpb hcb
    · exact clean_not_shared e b a (lag b) (lag a) (by omega) hab.symm hpb hAb hpa hca
  have hnd : (B.map start).Nodup := nodup_map_of_inj B start hB hinj
  have hsub : B.map start ⊆ (clocks q n).filter (fun c => e c = false) := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hq, hn, _, hp, hcl⟩ := h b hb
    have hL : 0 < lag b := by have := p2_pos _ hp; simpa [past] using this
    rw [List.mem_filter]
    refine ⟨(mem_clocks q _ n).mpr ⟨hq, by simp only [start]; omega⟩, ?_⟩
    simpa [start] using clean_start_S e b (lag b) hp hcl
  have := hnd.length_le_of_subset hsub
  simpa using this

end Recaman.CleanWindowCapacity
