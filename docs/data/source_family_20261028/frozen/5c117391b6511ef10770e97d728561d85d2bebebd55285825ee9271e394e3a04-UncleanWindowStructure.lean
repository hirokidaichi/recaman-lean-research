import Recaman.CleanWindowCapacity
import Recaman.LowSSCleanWindow

namespace Recaman.UncleanWindowStructure

open Recaman.LeadingRunSupply
open Recaman.CleanWindowCapacity
open Recaman.LowSSCleanWindow (sign_neg_false return_area_ne)
open ShortPeriodicSupply (sign)

/-! # Structure of unclean minimal P2 windows

Window `[b-L, b-1]`, base `t = b-L`, level `g j = mass (past e (t+j) j)`,
area `m j = moment (past e (t+j) j)`. A return is `0 < j < L` with `g j = 0`.

* `last_nonneg_return_is_S`: at a return (or the start `r = 0`) with `m r ≥ 0`
  after which every return has negative area, the clock `t+r` is a subtraction.
* `unclean_double_S`: if moreover `m r ≥ 1`, the clocks `t+r`, `t+r+1` are both
  subtractions.
* `unclean_has_double_S`: an unclean minimal P2 window has such a return.
* `deep_start`: before such a return there is a last clock `t+q` that is a
  subtraction from level one to level zero, after which the walk stays `≤ 0`
  up to `r`.
-/

/-! ## Pure walk lemmas -/

theorem walk_last_down (g m : Nat → Int)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (L : Nat) (hgL : g L = 1) (hmL : m L = 0)
    (r : Nat) (hrL : r < L) (hgr : g r = 0) (hmr : 0 ≤ m r)
    (hlater : ∀ j, r < j → j < L → g j = 0 → m j < 0) :
    g (r+1) = -1 := by
  rcases hstep r with hs | hs
  · exfalso
    have ha := harea r
    have hn : r + 1 + (L - (r+1)) = L := by omega
    rcases walk_return g m hstep harea (r+1) (by omega) (by omega) (L - (r+1)) with
      ⟨i, hi, h0, h1⟩ | ⟨_, h1⟩
    · have hne : r + 1 + i ≠ L := by
        intro h; rw [h] at h0; omega
      have := hlater (r+1+i) (by omega) (by omega) h0
      omega
    · rw [hn] at h1; omega
  · omega

theorem walk_double_down (g m : Nat → Int)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (L : Nat) (hgL : g L = 1) (hmL : m L = 0)
    (r : Nat) (hrL : r < L) (hgr : g r = 0) (hmr : 1 ≤ m r)
    (hlater : ∀ j, r < j → j < L → g j = 0 → m j < 0) :
    g (r+1) = -1 ∧ g (r+1+1) = -2 ∧ r + 2 < L := by
  have h1 := walk_last_down g m hstep harea L hgL hmL r hrL hgr (by omega) hlater
  have hr1 : r + 1 < L := by
    have : r + 1 ≠ L := by intro h; rw [h] at h1; omega
    omega
  have ha1 := harea r
  have ha2 := harea (r+1)
  rcases hstep (r+1) with hs | hs
  · exfalso
    have hne : r + 1 + 1 ≠ L := by intro h; rw [h] at hs; omega
    have := hlater (r+1+1) (by omega) (by omega) (by omega)
    omega
  · have hne : r + 1 + 1 ≠ L := by intro h; rw [h] at hs; omega
    exact ⟨h1, by omega, by omega⟩

theorem exists_last (Q : Nat → Prop) :
    ∀ L : Nat, (∃ j, j < L ∧ Q j) → ∃ r, r < L ∧ Q r ∧ ∀ j, r < j → j < L → ¬ Q j
  | 0, ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _)
  | L+1, ⟨j, hj, hq⟩ => by
      by_cases hL : Q L
      · exact ⟨L, Nat.lt_succ_self L, hL, fun i h1 h2 => absurd h2 (by omega)⟩
      · have hjL : j < L := by
          have : j ≠ L := by intro h; rw [h] at hq; exact hL hq
          omega
        obtain ⟨r, hr, hqr, hlast⟩ := exists_last Q L ⟨j, hjL, hq⟩
        refine ⟨r, by omega, hqr, fun i h1 h2 => ?_⟩
        by_cases hi : i = L
        · rw [hi]; exact hL
        · exact hlast i h1 (by omega)

theorem walk_deep_start (g m : Nat → Int)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (hg0 : g 0 = 0) (hm0 : m 0 = 0)
    (r : Nat) (hgr : g r = 0) (hmr : 1 ≤ m r) :
    ∃ q, 0 < q ∧ q < r ∧ g q = 1 ∧ g (q+1) = 0 ∧ ∀ j, q < j → j ≤ r → g j ≤ 0 := by
  have hex : ∃ j, j < r + 1 ∧ 1 ≤ g j := by
    apply Classical.byContradiction
    intro hno
    have hle : ∀ i, i ≤ r → m i ≤ 0 := by
      intro i
      induction i with
      | zero => intro _; omega
      | succ i ih =>
        intro hi
        have ha := harea i
        have hgi : ¬ 1 ≤ g (i+1) := fun h => hno ⟨i+1, by omega, h⟩
        have := ih (by omega)
        omega
    have := hle r (Nat.le_refl r)
    omega
  obtain ⟨q, hq, hgq, hlast⟩ := exists_last (fun j => 1 ≤ g j) (r+1) hex
  have hqr : q ≠ r := by intro h; rw [h] at hgq; omega
  have hq0 : q ≠ 0 := by intro h; rw [h] at hgq; omega
  have hnext : ¬ 1 ≤ g (q+1) := hlast (q+1) (by omega) (by omega)
  rcases hstep q with hs | hs
  · exact absurd (by omega) hnext
  · refine ⟨q, by omega, by omega, by omega, by omega, fun j h1 h2 => ?_⟩
    have := hlast j h1 (by omega)
    omega

/-! ## Transfer to the stream -/

theorem down_step_S (e : Int → Bool) (t : Int) (j : Nat)
    (h : mass (past e (t + ((j+1 : Nat) : Int)) (j+1)) = mass (past e (t + (j : Int)) j) - 1) :
    e (t + (j : Int)) = false := by
  rw [past_succ, mass_cons] at h
  exact sign_neg_false _ (by omega)

/-! ## Main theorems -/

/-- Lemma 1: at a return `r` (or at the start `r = 0`) with nonnegative area,
after which every return has negative area, the clock `b - L + r` is a
subtraction. -/
theorem last_nonneg_return_is_S (e : Int → Bool) (b : Int) (L : Nat)
    (hp : P2 (past e b L)) (r : Nat) (hrL : r < L)
    (hgr : mass (past e (b - (L : Int) + (r : Int)) r) = 0)
    (hmr : 0 ≤ moment (past e (b - (L : Int) + (r : Int)) r))
    (hlater : ∀ j : Nat, r < j → j < L →
      mass (past e (b - (L : Int) + (j : Int)) j) = 0 →
        moment (past e (b - (L : Int) + (j : Int)) j) < 0) :
    e (b - (L : Int) + (r : Int)) = false := by
  let t : Int := b - (L : Int)
  let g : Nat → Int := fun j => mass (past e (t + (j : Int)) j)
  let m : Nat → Int := fun j => moment (past e (t + (j : Int)) j)
  have hreb := past_rebase e b t L (by simp [t])
  have hgL : g L = 1 := by simp only [g]; rw [← hreb]; exact hp.1
  have hmL : m L = 0 := by simp only [m]; rw [← hreb]; exact hp.2
  have hgr' : g r = 0 := hgr
  have hmr' : 0 ≤ m r := hmr
  have h1 := walk_last_down g m (fun j => window_step e t j) (fun j => window_area e t j)
    L hgL hmL r hrL hgr' hmr' hlater
  exact down_step_S e t r (by simp only [g] at h1 hgr' ⊢; omega)

/-- Lemma B: if moreover the area at `r` is at least one, the clocks
`b - L + r` and `b - L + r + 1` are both subtractions, and `r + 2 < L`. -/
theorem unclean_double_S (e : Int → Bool) (b : Int) (L : Nat)
    (hp : P2 (past e b L)) (r : Nat) (hrL : r < L)
    (hgr : mass (past e (b - (L : Int) + (r : Int)) r) = 0)
    (hmr : 0 < moment (past e (b - (L : Int) + (r : Int)) r))
    (hlater : ∀ j : Nat, r < j → j < L →
      mass (past e (b - (L : Int) + (j : Int)) j) = 0 →
        moment (past e (b - (L : Int) + (j : Int)) j) < 0) :
    r + 2 < L ∧ e (b - (L : Int) + (r : Int)) = false ∧
      e (b - (L : Int) + (r : Int) + 1) = false := by
  let t : Int := b - (L : Int)
  let g : Nat → Int := fun j => mass (past e (t + (j : Int)) j)
  let m : Nat → Int := fun j => moment (past e (t + (j : Int)) j)
  have hreb := past_rebase e b t L (by simp [t])
  have hgL : g L = 1 := by simp only [g]; rw [← hreb]; exact hp.1
  have hmL : m L = 0 := by simp only [m]; rw [← hreb]; exact hp.2
  have hgr' : g r = 0 := hgr
  have hmr' : 1 ≤ m r := hmr
  obtain ⟨h1, h2, h3⟩ := walk_double_down g m (fun j => window_step e t j)
    (fun j => window_area e t j) L hgL hmL r hrL hgr' hmr' hlater
  refine ⟨h3, down_step_S e t r (by simp only [g] at h1 hgr' ⊢; omega), ?_⟩
  have := down_step_S e t (r+1) (by simp only [g] at h1 h2 ⊢; omega)
  rw [show t + ((r+1 : Nat) : Int) = b - (L : Int) + (r : Int) + 1 by simp only [t]; omega] at this
  exact this

/-- An unclean minimal P2 window has a return `r` with positive area after which
every return has negative area; at it, two consecutive subtractions start. -/
theorem unclean_has_double_S (e : Int → Bool) (b : Int) (L : Nat)
    (hp : P2 (past e b L))
    (hmin : ∀ d : Nat, 0 < d → d < L → ¬ P2 (past e b d))
    (hnc : ¬ Clean e b L) :
    ∃ r : Nat, 0 < r ∧ r + 2 < L ∧
      mass (past e (b - (L : Int) + (r : Int)) r) = 0 ∧
      0 < moment (past e (b - (L : Int) + (r : Int)) r) ∧
      (∀ j : Nat, r < j → j < L →
        mass (past e (b - (L : Int) + (j : Int)) j) = 0 →
          moment (past e (b - (L : Int) + (j : Int)) j) < 0) ∧
      e (b - (L : Int) + (r : Int)) = false ∧
      e (b - (L : Int) + (r : Int) + 1) = false := by
  let Q : Nat → Prop := fun j => 0 < j ∧
    mass (past e (b - (L : Int) + (j : Int)) j) = 0 ∧
    0 ≤ moment (past e (b - (L : Int) + (j : Int)) j)
  have hex : ∃ j, j < L ∧ Q j := by
    apply Classical.byContradiction
    intro hno
    apply hnc
    intro j hj hjL hg
    apply Classical.byContradiction
    intro hneg
    exact hno ⟨j, hjL, hj, hg, by omega⟩
  obtain ⟨r, hrL, ⟨hr0, hgr, hmr⟩, hlast⟩ := exists_last Q L hex
  have hlater : ∀ j : Nat, r < j → j < L →
      mass (past e (b - (L : Int) + (j : Int)) j) = 0 →
        moment (past e (b - (L : Int) + (j : Int)) j) < 0 := by
    intro j h1 h2 hg
    apply Classical.byContradiction
    intro hneg
    exact hlast j h1 h2 ⟨by omega, hg, by omega⟩
  have hne := return_area_ne e b L hp hmin r hr0 hrL hgr
  have hpos : 0 < moment (past e (b - (L : Int) + (r : Int)) r) := by omega
  obtain ⟨h3, h4, h5⟩ := unclean_double_S e b L hp r hrL hgr hpos hlater
  exact ⟨r, hr0, h3, hgr, hpos, hlater, h4, h5⟩

/-- Lemma Q: before a return `r` with positive area there is a clock `b - L + q`
(`0 < q < r`) that is a subtraction from level one to level zero, after which
the walk stays at level `≤ 0` up to `r`. -/
theorem deep_start (e : Int → Bool) (b : Int) (L : Nat) (r : Nat)
    (hgr : mass (past e (b - (L : Int) + (r : Int)) r) = 0)
    (hmr : 0 < moment (past e (b - (L : Int) + (r : Int)) r)) :
    ∃ q : Nat, 0 < q ∧ q < r ∧
      mass (past e (b - (L : Int) + (q : Int)) q) = 1 ∧
      mass (past e (b - (L : Int) + ((q+1 : Nat) : Int)) (q+1)) = 0 ∧
      e (b - (L : Int) + (q : Int)) = false ∧
      ∀ j : Nat, q < j → j ≤ r → mass (past e (b - (L : Int) + (j : Int)) j) ≤ 0 := by
  let t : Int := b - (L : Int)
  let g : Nat → Int := fun j => mass (past e (t + (j : Int)) j)
  let m : Nat → Int := fun j => moment (past e (t + (j : Int)) j)
  have hg0 : g 0 = 0 := by simp [g, past]
  have hm0 : m 0 = 0 := by simp [m, past, moment]
  have hgr' : g r = 0 := hgr
  have hmr' : 0 < m r := hmr
  obtain ⟨q, hq0, hqr, hgq, hgq1, hle⟩ := walk_deep_start g m (fun j => window_step e t j)
    (fun j => window_area e t j) hg0 hm0 r hgr' hmr'
  refine ⟨q, hq0, hqr, hgq, hgq1, down_step_S e t q (by simp only [g] at hgq hgq1 ⊢; omega), hle⟩

end Recaman.UncleanWindowStructure
