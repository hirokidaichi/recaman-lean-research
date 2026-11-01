import Recaman.CleanWindowCapacity
import Recaman.OneSSMultiplicity

namespace Recaman.LowSSCleanWindow

open Recaman.LeadingRunSupply
open Recaman.CleanWindowCapacity
open Recaman.OneSSMultiplicity (ssCount)
open ShortPeriodicSupply (sign)

/-! # Minimal P2 windows of depth one or with at most one SS pair are clean

For a window `[b-L, b-1]` with base `t = b-L`, write `g j = mass (past e (t+j) j)`
(level) and `m j = moment (past e (t+j) j)` (area). Minimality of the window
(no shorter P2 window ends at `b`) forces `m j ≠ 0` at every interior return
`g j = 0`. Two pure walk lemmas then give cleanness:

* `walk_depth_one`: if the walk never goes below `-1`;
* `walk_low_ss`: if the walk has at most one pair of consecutive down steps.
-/

/-! ## Pure walk lemmas -/

theorem walk_depth_one (g m : Nat → Int)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (L : Nat) (hgL : g L = 1) (hmL : m L = 0)
    (hdepth : ∀ j, j ≤ L → -1 ≤ g j)
    (hret : ∀ j, 0 < j → j < L → g j = 0 → m j ≠ 0) :
    ∀ j, 0 < j → j < L → g j = 0 → m j < 0 := by
  intro j0 hj0 hj0L hg0
  apply Classical.byContradiction
  intro hneg
  have hm0 : 1 ≤ m j0 := by have := hret j0 hj0 hj0L hg0; omega
  have inv : ∀ i, j0 + i ≤ L →
      (0 ≤ g (j0+i) → 1 ≤ m (j0+i)) ∧ (g (j0+i) = -1 → 0 ≤ m (j0+i)) := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.add_zero]; omega
    | succ i ih =>
      intro hle
      have ⟨h1, h2⟩ := ih (by omega)
      have hs := hstep (j0+i)
      have ha := harea (j0+i)
      have hd := hdepth (j0+i+1) (by omega)
      have e1 : j0 + (i+1) = j0 + i + 1 := by omega
      rw [e1]
      by_cases hz : g (j0+i+1) = 0 ∧ m (j0+i+1) = 0
      · exfalso
        have hlt : j0+i+1 < L := by
          by_cases h : j0+i+1 = L
          · rw [h] at hz; omega
          · omega
        exact hret (j0+i+1) (by omega) hlt hz.1 hz.2
      · by_cases hk : 0 ≤ g (j0+i)
        · have := h1 hk
          constructor <;> intro <;> omega
        · have hd' := hdepth (j0+i) (by omega)
          have := h2 (by omega)
          constructor <;> intro <;> omega
  have := inv (L - j0) (by omega)
  rw [show j0 + (L - j0) = L by omega] at this
  have := this.1 (by omega)
  omega

/-- Shape of an SS-free prefix of a walk started at level and area zero: it is
either still in the alternating `S A S A ...` regime (area `-k/2`), or it has
gone up and is in the regime where every return comes from level one. -/
theorem walk_prefix (g m : Nat → Int) (c : Nat → Nat)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (hcmono : ∀ j, c j ≤ c (j+1))
    (hss : ∀ p, g (p+1+1) = g (p+1) - 1 → g (p+1) = g p - 1 → c (p+1) + 1 ≤ c (p+1+1))
    (hg0 : g 0 = 0) (hm0 : m 0 = 0) :
    ∀ k, c k = 0 →
      ((g k = 0 ∧ 2 * m k = -(k : Int)) ∨
        (g k = -1 ∧ 2 * m k = -((k : Int) + 1) ∧ ∃ p, k = p+1 ∧ g p = 0)) ∨
      (0 ≤ g k ∧ (g k = 0 → ∃ p, k = p+1 ∧ g p = 1)) := by
  intro k
  induction k with
  | zero => intro _; left; left; refine ⟨hg0, ?_⟩; rw [hm0]; rfl
  | succ k ih =>
    intro hc
    have hck : c k = 0 := by have := hcmono k; omega
    have hs := hstep k
    have ha := harea k
    have hcast : ((k+1 : Nat) : Int) = (k : Int) + 1 := by omega
    rcases ih hck with (⟨h1, h2⟩ | ⟨h1, h2, p, hp, hgp⟩) | ⟨h1, h2⟩
    · rcases hs with hs | hs
      · right; exact ⟨by omega, fun h => by omega⟩
      · left; right; refine ⟨by omega, by rw [hcast]; omega, k, rfl, h1⟩
    · rcases hs with hs | hs
      · left; left; refine ⟨by omega, by rw [hcast]; omega⟩
      · exfalso
        subst hp
        have := hss p (by omega) (by omega)
        omega
    · by_cases hg1 : 1 ≤ g k
      · right; refine ⟨by omega, fun h => ⟨k, rfl, by omega⟩⟩
      · have hz : g k = 0 := by omega
        rcases hs with hs | hs
        · right; exact ⟨by omega, fun h => by omega⟩
        · exfalso
          obtain ⟨p, hp, hgp⟩ := h2 hz
          subst hp
          have := hss p (by omega) (by omega)
          omega

theorem walk_low_ss (g m : Nat → Int) (c : Nat → Nat)
    (hstep : ∀ j, g (j+1) = g j + 1 ∨ g (j+1) = g j - 1)
    (harea : ∀ j, m (j+1) = m j + g (j+1))
    (hcmono : ∀ j, c j ≤ c (j+1))
    (hss : ∀ p, g (p+1+1) = g (p+1) - 1 → g (p+1) = g p - 1 → c (p+1) + 1 ≤ c (p+1+1))
    (hg0 : g 0 = 0) (hm0 : m 0 = 0)
    (L : Nat) (hgL : g L = 1) (hmL : m L = 0) (hcL : c L ≤ 1)
    (hret : ∀ j, 0 < j → j < L → g j = 0 → m j ≠ 0) :
    ∀ j, 0 < j → j < L → g j = 0 → m j < 0 := by
  intro j0 hj0 hj0L hg0'
  apply Classical.byContradiction
  intro hneg
  have hm1 : 1 ≤ m j0 := by have := hret j0 hj0 hj0L hg0'; omega
  have hss' : ∀ p k, k = p+1 → g (k+1) = g k - 1 → g k = g p - 1 → c k + 1 ≤ c (k+1) := by
    intro p k h; subst h; exact hss p
  have hcup : ∀ k i, c k ≤ c (k+i) := by
    intro k i
    induction i with
    | zero => exact Nat.le_refl _
    | succ i ih => exact Nat.le_trans ih (hcmono (k+i))
  have hcle : ∀ k, k ≤ L → c k ≤ 1 := by
    intro k hk
    have := hcup k (L - k)
    rw [show k + (L - k) = L by omega] at this
    omega
  have hinit : c j0 = 0 → ∃ p, j0 = p+1 ∧ g p = 1 := by
    intro hc
    rcases walk_prefix g m c hstep harea hcmono hss hg0 hm0 j0 hc with
      (⟨_, h2⟩ | ⟨h1, _⟩) | ⟨_, h2⟩
    · exfalso; omega
    · exfalso; omega
    · exact h2 hg0'
  have inv : ∀ i, j0 + i ≤ L →
      -1 ≤ g (j0+i) ∧ (0 ≤ g (j0+i) → 1 ≤ m (j0+i)) ∧
      (g (j0+i) = -1 → 0 ≤ m (j0+i) ∧ 1 ≤ c (j0+i) ∧ ∃ p, j0+i = p+1 ∧ g p = 0) ∧
      (g (j0+i) = 0 → c (j0+i) = 0 → ∃ p, j0+i = p+1 ∧ g p = 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [Nat.add_zero]
      refine ⟨by omega, fun _ => hm1, fun h => by omega, fun _ hc => hinit hc⟩
    | succ i ih =>
      intro hle
      obtain ⟨h0, h1, h2, h3⟩ := ih (by omega)
      have hs := hstep (j0+i)
      have ha := harea (j0+i)
      have hmo := hcmono (j0+i)
      have hcK1 := hcle (j0+i+1) (by omega)
      have e1 : j0 + (i+1) = j0 + i + 1 := by omega
      rw [e1]
      by_cases hg1 : 1 ≤ g (j0+i)
      · have hm' := h1 (by omega)
        refine ⟨by omega, fun _ => by omega, fun h => by omega, fun h _ => ⟨j0+i, rfl, by omega⟩⟩
      · by_cases hgz : g (j0+i) = 0
        · have hm' := h1 (by omega)
          rcases hs with hs | hs
          · refine ⟨by omega, fun _ => by omega, fun h => by omega, fun h => by omega⟩
          · have hc1 : 1 ≤ c (j0+i+1) := by
              by_cases hc0 : c (j0+i) = 0
              · obtain ⟨p, hp, hgp⟩ := h3 hgz hc0
                have := hss' p (j0+i) hp (by omega) (by omega)
                omega
              · omega
            refine ⟨by omega, fun h => by omega,
              fun _ => ⟨by omega, hc1, j0+i, rfl, hgz⟩, fun h => by omega⟩
        · have hgm : g (j0+i) = -1 := by omega
          obtain ⟨hmK, hcK, p, hp, hgp⟩ := h2 hgm
          rcases hs with hs | hs
          · have hm' : 1 ≤ m (j0+i+1) := by
              by_cases hmz : m (j0+i+1) = 0
              · exfalso
                have hlt : j0+i+1 < L := by
                  by_cases h : j0+i+1 = L
                  · have hh := hgL; rw [← h] at hh; omega
                  · omega
                exact hret (j0+i+1) (by omega) hlt (by omega) hmz
              · omega
            refine ⟨by omega, fun _ => hm', fun h => by omega, fun _ h => by omega⟩
          · exfalso
            have := hss' p (j0+i) hp (by omega) (by omega)
            omega
  have := inv (L - j0) (by omega)
  rw [show j0 + (L - j0) = L by omega] at this
  have := this.2.1 (by omega)
  omega

/-! ## The stream walk -/

theorem sign_neg_false (x : Bool) (h : sign x = -1) : x = false := by
  cases x
  · rfl
  · exact absurd h (by decide)

theorem window_ss_mono (e : Int → Bool) (t : Int) (j : Nat) :
    ssCount (past e (t + (j : Int)) j) ≤ ssCount (past e (t + ((j+1 : Nat) : Int)) (j+1)) := by
  rw [past_succ]
  simp only [ssCount]
  exact Nat.le_add_left _ _

theorem window_ss_step (e : Int → Bool) (t : Int) (p : Nat)
    (h2 : mass (past e (t + ((p+1+1 : Nat) : Int)) (p+1+1)) =
      mass (past e (t + ((p+1 : Nat) : Int)) (p+1)) - 1)
    (h1 : mass (past e (t + ((p+1 : Nat) : Int)) (p+1)) =
      mass (past e (t + (p : Int)) p) - 1) :
    ssCount (past e (t + ((p+1 : Nat) : Int)) (p+1)) + 1 ≤
      ssCount (past e (t + ((p+1+1 : Nat) : Int)) (p+1+1)) := by
  have q1 := past_succ e t (p+1)
  have q0 := past_succ e t p
  rw [q1, mass_cons] at h2
  rw [q0, mass_cons] at h1
  have hx : e (t + ((p+1 : Nat) : Int)) = false := sign_neg_false _ (by omega)
  have hy : e (t + (p : Int)) = false := sign_neg_false _ (by omega)
  rw [q1, q0]
  simp only [ssCount, hx, hy, List.head?_cons]
  simp
  omega

/-- Splitting at an interior return: minimality forces nonzero area there. -/
theorem return_area_ne (e : Int → Bool) (b : Int) (L : Nat)
    (hp : P2 (past e b L))
    (hmin : ∀ d : Nat, 0 < d → d < L → ¬ P2 (past e b d)) :
    ∀ j : Nat, 0 < j → j < L →
      mass (past e (b - (L : Int) + (j : Int)) j) = 0 →
        moment (past e (b - (L : Int) + (j : Int)) j) ≠ 0 := by
  intro j hj hjL hg hm
  have hsplit := past_append e b (L - j) j
  rw [show L - j + j = L by omega] at hsplit
  have hb : b - ((L - j : Nat) : Int) = b - (L : Int) + (j : Int) := by omega
  rw [hb] at hsplit
  have hmass := hp.1
  have hmom := hp.2
  rw [hsplit, mass_append] at hmass
  rw [hsplit, moment_append] at hmom
  rw [hg] at hmass hmom
  rw [hm] at hmom
  apply hmin (L - j) (by omega) (by omega)
  refine ⟨by omega, ?_⟩
  simp at hmom
  omega

/-! ## Main theorems -/

/-- A minimal P2 window whose walk never drops below `-1` is clean. -/
theorem clean_of_depth_one (e : Int → Bool) (b : Int) (L : Nat)
    (hp : P2 (past e b L))
    (hmin : ∀ d : Nat, 0 < d → d < L → ¬ P2 (past e b d))
    (hdepth : ∀ j : Nat, j ≤ L → -1 ≤ mass (past e (b - (L : Int) + (j : Int)) j)) :
    Clean e b L := by
  let t : Int := b - (L : Int)
  let g : Nat → Int := fun j => mass (past e (t + (j : Int)) j)
  let m : Nat → Int := fun j => moment (past e (t + (j : Int)) j)
  have hreb := past_rebase e b t L (by simp [t])
  have hgL : g L = 1 := by simp only [g]; rw [← hreb]; exact hp.1
  have hmL : m L = 0 := by simp only [m]; rw [← hreb]; exact hp.2
  intro j hj hjL hgj
  exact walk_depth_one g m (fun j => window_step e t j) (fun j => window_area e t j)
    L hgL hmL hdepth (return_area_ne e b L hp hmin) j hj hjL hgj

/-- A minimal P2 window with at most one adjacent SS pair is clean. -/
theorem clean_of_low_ss (e : Int → Bool) (b : Int) (L : Nat)
    (hp : P2 (past e b L))
    (hmin : ∀ d : Nat, 0 < d → d < L → ¬ P2 (past e b d))
    (hss : ssCount (past e b L) ≤ 1) :
    Clean e b L := by
  let t : Int := b - (L : Int)
  let g : Nat → Int := fun j => mass (past e (t + (j : Int)) j)
  let m : Nat → Int := fun j => moment (past e (t + (j : Int)) j)
  let c : Nat → Nat := fun j => ssCount (past e (t + (j : Int)) j)
  have hreb := past_rebase e b t L (by simp [t])
  have hgL : g L = 1 := by simp only [g]; rw [← hreb]; exact hp.1
  have hmL : m L = 0 := by simp only [m]; rw [← hreb]; exact hp.2
  have hcL : c L ≤ 1 := by simp only [c]; rw [← hreb]; exact hss
  have hg0 : g 0 = 0 := by simp [g, past]
  have hm0 : m 0 = 0 := by simp [m, past, moment]
  intro j hj hjL hgj
  exact walk_low_ss g m c (fun j => window_step e t j) (fun j => window_area e t j)
    (fun j => window_ss_mono e t j) (fun p => window_ss_step e t p) hg0 hm0
    L hgL hmL hcL (return_area_ne e b L hp hmin) j hj hjL hgj

/-- Line capacity for minimal windows that have at most one SS pair or depth one
(an all-lag interval version of the E-128 endpoint injection, extended to depth-one
windows): on `[q, q+n)`, a family of additions each ending a minimal P2 window
inside the interval, every such window having `ssCount ≤ 1` or depth one, is no
larger than the number of subtractions in the interval. -/
theorem lowSS_capacity (e : Int → Bool) (q : Int) (n : Nat) (B : List Int)
    (hB : B.Nodup) (lag : Int → Nat)
    (h : ∀ b ∈ B, q ≤ b - (lag b : Int) ∧ b < q + (n : Int) ∧ e b = true ∧
      P2 (past e b (lag b)) ∧ (∀ d : Nat, 0 < d → d < lag b → ¬ P2 (past e b d)) ∧
      (ssCount (past e b (lag b)) ≤ 1 ∨
        ∀ j : Nat, j ≤ lag b → -1 ≤ mass (past e (b - (lag b : Int) + (j : Int)) j))) :
    B.length ≤ ((Recaman.SuffixHallOwnerMap.clocks q n).filter (fun c => e c = false)).length := by
  apply clean_capacity e q n B hB lag
  intro b hb
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h b hb
  refine ⟨h1, h2, h3, h4, ?_⟩
  rcases h6 with hs | hd
  · exact clean_of_low_ss e b (lag b) h4 h5 hs
  · exact clean_of_depth_one e b (lag b) h4 h5 hd

end Recaman.LowSSCleanWindow
