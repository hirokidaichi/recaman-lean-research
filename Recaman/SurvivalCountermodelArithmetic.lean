import Recaman.Basic

namespace Recaman.SurvivalFamily

/-! Arithmetic of the arbitrary-finite-prefix countermodel in issue #70.
The points below describe the explicit word, not an assumed actual orbit.
The replay module must still prove that `Basic.step` generates these points. -/

def tri (t : Int) : Int := t * (t + 1) / 2

theorem twice_tri (t : Int) : 2 * tri t = t * (t + 1) := by
  have hm : t * (t + 1) % 2 = 0 := by
    rw [Int.mul_emod, Int.add_emod]
    have : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases this with h | h <;> simp [h]
  unfold tri
  omega

@[simp] theorem tri_zero : tri 0 = 0 := by decide
@[simp] theorem tri_one : tri 1 = 1 := by decide
@[simp] theorem tri_two : tri 2 = 3 := by decide
@[simp] theorem tri_three : tri 3 = 6 := by decide

theorem tri_succ (t : Int) : tri (t + 1) = tri t + t + 1 := by
  have := twice_tri t
  have := twice_tri (t + 1)
  grind

/-- Coordinates and the strict rail-clearance condition of the paper family. -/
structure Geometry where
  w : Int
  d : Int
  j : Int
  c : Int
  w_pos : 0 < w
  d_ge : 10 ≤ d
  size_eq : 2 * j = d * d + w
  clearance : 8 * d + w < d * d
  clock_large : 40 * j < c

namespace Geometry
variable (g : Geometry)

theorem d_sq_ge : 100 ≤ g.d * g.d := by
  have hd := g.d_ge
  have := Int.mul_le_mul hd hd (by omega) (by omega)
  omega

theorem j_pos : 0 < g.j := by
  have := g.d_sq_ge
  have := g.size_eq
  have := g.w_pos
  omega

theorem c_pos : 0 < g.c := by
  have := g.j_pos
  have := g.clock_large
  omega

theorem gap_linear : g.w + 4 * g.d < g.j := by
  have := g.size_eq
  have := g.clearance
  omega

def addPoint (p : Int) : Int := p * g.c + 2 * g.j + tri p
def downOffset (q : Int) : Int := g.w + 2 * g.d * q - q * q + tri q
def downPoint (q : Int) : Int := q * g.c + g.downOffset q

theorem tri_bounds {p : Int} (hp : 0 ≤ p) (hpd : p ≤ g.d) :
    0 ≤ tri p ∧ tri p ≤ 2 * g.j := by
  have hs := twice_tri p
  have hp2 : 0 ≤ p * p := Int.mul_nonneg hp hp
  have hupper := Int.mul_le_mul hpd hpd hp (by have := g.d_ge; omega)
  have hself := Int.mul_le_mul_of_nonneg_right (show 1 ≤ g.d by have := g.d_ge; omega)
    (show 0 ≤ g.d by have := g.d_ge; omega)
  have hrel := g.size_eq
  have hw := g.w_pos
  have hd := g.d_ge
  grind

theorem down_bounds {q : Int} (hq : 0 ≤ q) (hqd : q ≤ g.d) :
    g.w ≤ g.downOffset q ∧ g.downOffset q ≤ 4 * g.j := by
  have ht := g.tri_bounds hq hqd
  have hpos := Int.mul_nonneg hq (show 0 ≤ 2 * g.d - q by have := g.d_ge; omega)
  have hsq := Int.mul_nonneg (show 0 ≤ g.d - q by omega)
    (show 0 ≤ g.d - q by omega)
  have hrel := g.size_eq
  unfold downOffset
  grind

theorem band_unique {p q u v : Int}
    (hu : -4 * g.j ≤ u) (hu' : u ≤ 6 * g.j)
    (hv : -4 * g.j ≤ v) (hv' : v ≤ 6 * g.j)
    (heq : p * g.c + u = q * g.c + v) : p = q := by
  have hc := g.c_pos
  have hj := g.j_pos
  have hlarge := g.clock_large
  by_cases h : p < q
  · have hm := Int.mul_le_mul_of_nonneg_right (show p + 1 ≤ q by omega) (show 0 ≤ g.c by omega)
    grind
  · by_cases h' : q < p
    · have hm := Int.mul_le_mul_of_nonneg_right (show q + 1 ≤ p by omega) (show 0 ≤ g.c by omega)
      grind
    · omega

theorem down_ge_w {q : Int} (hq : 0 ≤ q) (hqd : q ≤ g.d) :
    g.w ≤ g.downPoint q := by
  have := g.down_bounds hq hqd
  have := Int.mul_nonneg hq (show 0 ≤ g.c by have := g.c_pos; omega)
  unfold downPoint
  omega

/-- The entire initial seed, expressed as a membership predicate. F is supplied
separately; this predicate is exactly the five explicitly preloaded components. -/
def CoreSeed (y : Int) : Prop :=
  y = 0 ∨ y = 3 * g.c - g.j - 3 ∨ y = 2 * g.j - 1 ∨
  (∃ t : Int, 1 ≤ t ∧ t ≤ g.j ∧ y = 2 * g.j + 3 * t) ∨
  (∃ p : Int, 2 ≤ p ∧ p ≤ g.d - 2 ∧ y = g.addPoint p - 1)

/-- The two prelanding rails include the extra upper output of the initial SS. -/
def Rails (y : Int) : Prop :=
  (∃ k : Int, 0 ≤ k ∧ k ≤ g.j ∧ y = g.c + 2 * g.j + k) ∨
  (∃ k : Int, 1 ≤ k ∧ k ≤ g.j + 1 ∧ y = 2 * g.c + 2 * g.j - k)

theorem down_not_core {q : Int} (hq : 0 ≤ q) (hqd : q < g.d) :
    ¬ g.CoreSeed (g.downPoint q) := by
  have hj := g.j_pos
  have hw := g.w_pos
  have hd := g.d_ge
  have hrel := g.size_eq
  have hsq := g.d_sq_ge
  have hbound := g.down_bounds hq (by omega)
  have hge := g.down_ge_w hq (by omega)
  intro hm
  rcases hm with hz | hx | hv | ht | hp
  · omega
  · have heq : q * g.c + g.downOffset q = 3 * g.c + (-g.j-3) := by
      unfold downPoint at hx
      omega
    have he := g.band_unique (p := q) (q := 3) (by omega) (by omega)
      (by omega) (by omega) heq
    subst q
    unfold downPoint at hx
    omega
  · have he := g.band_unique (p := q) (q := 0) (u := g.downOffset q)
      (v := 2*g.j-1) (by omega) (by omega) (by omega) (by omega) (by simpa [downPoint] using hv)
    subst q
    simp [downPoint, downOffset] at hv
    omega
  · rcases ht with ⟨t, ht, htj, heq⟩
    have he := g.band_unique (p := q) (q := 0) (u := g.downOffset q)
      (v := 2*g.j+3*t) (by omega) (by omega) (by omega) (by omega) (by simpa [downPoint] using heq)
    subst q
    simp [downPoint, downOffset] at heq
    omega
  · rcases hp with ⟨p, hp, hpd, heq⟩
    have hb := g.tri_bounds (p := p) (by omega) (by omega)
    have he := g.band_unique (p := q) (q := p) (u := g.downOffset q)
      (v := 2*g.j+tri p-1) (by omega) (by omega) (by omega) (by omega)
      (by simpa [downPoint, addPoint, Int.add_sub_assoc, Int.add_assoc] using heq)
    subst p
    have hmul := Int.mul_le_mul (show 2 ≤ g.d-q by omega) (show 2 ≤ g.d-q by omega)
      (by omega) (by omega)
    unfold downPoint downOffset addPoint at heq
    grind

theorem down_not_rails {q : Int} (hq : 0 ≤ q) (hqd : q < g.d) :
    ¬ g.Rails (g.downPoint q) := by
  have hj := g.j_pos
  have hw := g.w_pos
  have hd := g.d_ge
  have hg := g.gap_linear
  have hb := g.down_bounds hq (by omega)
  intro hm
  rcases hm with ⟨k, hk, hkj, heq⟩ | ⟨k, hk, hkj, heq⟩
  · have he := g.band_unique (p := q) (q := 1) (u := g.downOffset q)
      (v := 2*g.j+k) (by omega) (by omega) (by omega) (by omega)
      (by simpa [downPoint, Int.add_assoc] using heq)
    subst q
    simp [downPoint, downOffset] at heq
    omega
  · have he := g.band_unique (p := q) (q := 2) (u := g.downOffset q)
      (v := 2*g.j-k) (by omega) (by omega) (by omega) (by omega)
      (by simpa [downPoint, Int.add_sub_assoc] using heq)
    subst q
    simp [downPoint, downOffset] at heq
    omega

theorem down_ne_add {q p : Int} (hq : 0 ≤ q) (hqd : q < g.d)
    (hp : 0 ≤ p) (hpd : p ≤ g.d) : g.downPoint q ≠ g.addPoint p := by
  have hj := g.j_pos
  have hw := g.w_pos
  have hrel := g.size_eq
  have hb := g.down_bounds hq (by omega)
  have ht := g.tri_bounds hp hpd
  intro heq
  have he := g.band_unique (p := q) (q := p) (u := g.downOffset q)
    (v := 2*g.j+tri p) (by omega) (by omega) (by omega) (by omega)
    (by simpa [downPoint, addPoint, Int.add_assoc] using heq)
  subst p
  have hm := Int.mul_le_mul (show 1 ≤ g.d-q by omega) (show 1 ≤ g.d-q by omega)
    (by omega) (by omega)
  unfold downPoint downOffset addPoint at heq
  grind

theorem down_injective {q p : Int} (hq : 0 ≤ q) (hqd : q ≤ g.d)
    (hp : 0 ≤ p) (hpd : p ≤ g.d) (heq : g.downPoint q = g.downPoint p) : q = p := by
  have hj := g.j_pos
  have hw := g.w_pos
  have hq' := g.down_bounds hq hqd
  have hp' := g.down_bounds hp hpd
  exact g.band_unique (by omega) (by omega) (by omega) (by omega) heq

def lower (k : Int) : Int := g.c + 2 * g.j + k
def upper (k : Int) : Int := 2 * g.c + 2 * g.j - k

theorem lower_not_core {k : Int} (hk : 0 ≤ k) (hkj : k ≤ g.j) :
    ¬ g.CoreSeed (g.lower k) := by
  have hj := g.j_pos
  have hc := g.clock_large
  have hw := g.w_pos
  intro hm
  rcases hm with hz | hx | hv | ⟨t, ht, htj, heq⟩ | ⟨p, hp, hpd, heq⟩
  · unfold lower at hz; omega
  · unfold lower at hx; omega
  · unfold lower at hv; omega
  · unfold lower at heq; omega
  · have hb := g.tri_bounds (p := p) (by omega) (by omega)
    have he := g.band_unique (p := 1) (q := p) (u := 2*g.j+k)
      (v := 2*g.j+tri p-1) (by omega) (by omega) (by omega) (by omega)
      (by simpa [lower, addPoint, Int.add_sub_assoc, Int.add_assoc] using heq)
    omega

theorem lower_ne_upper {k t : Int} (hk : 0 ≤ k) (hkj : k ≤ g.j)
    (_ht : 1 ≤ t) (htj : t ≤ g.j+1) : g.lower k ≠ g.upper t := by
  have := g.j_pos
  have := g.clock_large
  unfold lower upper
  omega

theorem middle_not_core : ¬ g.CoreSeed (g.upper (g.j+1)) := by
  have hj := g.j_pos
  have hc := g.clock_large
  have hw := g.w_pos
  intro hm
  rcases hm with hz | hx | hv | ⟨t, ht, htj, heq⟩ | ⟨p, hp, hpd, heq⟩
  · unfold upper at hz; omega
  · unfold upper at hx; omega
  · unfold upper at hv; omega
  · unfold upper at heq; omega
  · have hb := g.tri_bounds (p := p) (by omega) (by omega)
    have he := g.band_unique (p := 2) (q := p) (u := g.j-1)
      (v := 2*g.j+tri p-1) (by omega) (by omega) (by omega) (by omega)
      (by unfold upper addPoint at heq; omega)
    subst p
    simp [upper, addPoint] at heq
    omega

theorem landing_not_core : ¬ g.CoreSeed (2*g.j) := by
  have hj := g.j_pos
  have hc := g.clock_large
  intro hm
  rcases hm with hz | hx | hv | ⟨t, ht, htj, heq⟩ | ⟨p, hp, hpd, heq⟩
  · omega
  · omega
  · omega
  · omega
  · have hb := g.tri_bounds (p := p) (by omega) (by omega)
    have he := g.band_unique (p := 0) (q := p) (u := 2*g.j)
      (v := 2*g.j+tri p-1) (by omega) (by omega) (by omega) (by omega)
      (by simpa [addPoint, Int.add_sub_assoc, Int.add_assoc] using heq)
    omega

theorem landing_not_rails : ¬ g.Rails (2*g.j) := by
  have hj := g.j_pos
  have hc := g.clock_large
  intro hm
  rcases hm with ⟨k, hk, hkj, heq⟩ | ⟨k, hk, hkj, heq⟩ <;> omega

theorem addPoint_nonneg {p : Int} (hp : 0 ≤ p) (hpd : p ≤ g.d) :
    0 < g.addPoint p := by
  have := g.tri_bounds hp hpd
  have := Int.mul_nonneg hp (show 0 ≤ g.c by have := g.c_pos; omega)
  have := g.j_pos
  unfold addPoint
  omega

theorem core_nonneg {y : Int} (h : g.CoreSeed y) : 0 ≤ y := by
  have hj := g.j_pos
  have hc := g.clock_large
  rcases h with hz | hx | hv | ⟨t, ht, htj, heq⟩ | ⟨p, hp, hpd, heq⟩
  · omega
  · omega
  · omega
  · omega
  · have := g.addPoint_nonneg (p := p) (by omega) (by omega)
    omega

theorem add_succ (p : Int) :
    g.addPoint (p+1) = g.addPoint p + (g.c+p+1) := by
  have := tri_succ p
  unfold addPoint
  grind

theorem add_candidate (p : Int) :
    g.addPoint p - (g.c+p+1) = g.addPoint (p-1) - 1 := by
  have := tri_succ (p-1)
  have h : tri (p-1+1) = tri p := by congr 1; omega
  rw [h] at this
  unfold addPoint
  grind

theorem down_start : g.downPoint g.d = g.addPoint g.d := by
  have := g.size_eq
  unfold downPoint downOffset addPoint
  grind

theorem down_step (q : Int) :
    g.downPoint (q+1) = g.downPoint q + (g.c+2*g.d-q) := by
  have := tri_succ q
  unfold downPoint downOffset
  grind

@[simp] theorem down_zero : g.downPoint 0 = g.w := by simp [downPoint, downOffset]

def upResidue (p : Int) : Int := 2*g.j+tri p-p*p

theorem up_residue_bounds {p : Int} (hp : 0 ≤ p) (hpd : p ≤ g.d) :
    g.w ≤ g.upResidue p ∧ g.upResidue p ≤ 4*g.j := by
  have ht := g.tri_bounds hp hpd
  have hd := g.d_ge
  have hs := g.size_eq
  have hm := Int.mul_le_mul hpd hpd hp (by omega)
  have hn := Int.mul_nonneg hp hp
  unfold upResidue
  omega

theorem up_residue_succ (p : Int) : g.upResidue (p+1) = g.upResidue p-p := by
  have := tri_succ p
  unfold upResidue
  grind

theorem up_decomp (p : Int) : g.addPoint p = p*(g.c+p)+g.upResidue p := by
  unfold addPoint upResidue
  grind

theorem down_decomp (q : Int) : g.downPoint q = q*(g.c+2*g.d-q)+(g.w+tri q) := by
  unfold downPoint downOffset
  grind

theorem down_residue_bounds {q : Int} (hq : 0 ≤ q) (hqd : q ≤ g.d) :
    0 < g.w+tri q ∧ g.w+tri q < g.c := by
  have := g.tri_bounds hq hqd
  have := g.w_pos
  have := g.gap_linear
  have := g.d_ge
  have := g.clock_large
  have := g.j_pos
  omega

theorem add_injective {p q : Int} (hp : 0 ≤ p) (hpd : p ≤ g.d)
    (hq : 0 ≤ q) (hqd : q ≤ g.d) (heq : g.addPoint p = g.addPoint q) : p = q := by
  have hb := g.tri_bounds hp hpd
  have hb' := g.tri_bounds hq hqd
  have hj := g.j_pos
  apply g.band_unique (u := 2*g.j+tri p) (v := 2*g.j+tri q)
    (by omega) (by omega) (by omega) (by omega)
  simpa [addPoint, Int.add_assoc] using heq

/-- The first genuine new obligation in #70: every intended descending output
is fresh against F, the complete seed, both rails, every addition output, and
all preceding descending outputs. No freshness/reachability premise is used. -/
theorem descent_fresh {F : List Nat} (hF : ∀ z ∈ F, (z : Int) < g.w)
    {q : Int} (hq : 0 ≤ q) (hqd : q < g.d) :
    (∀ z ∈ F, g.downPoint q ≠ (z : Int)) ∧
    ¬ g.CoreSeed (g.downPoint q) ∧ ¬ g.Rails (g.downPoint q) ∧
    (∀ p, 0 ≤ p → p ≤ g.d → g.downPoint q ≠ g.addPoint p) ∧
    (∀ p, q < p → p ≤ g.d → g.downPoint q ≠ g.downPoint p) := by
  refine ⟨?_, g.down_not_core hq hqd, g.down_not_rails hq hqd, ?_, ?_⟩
  · intro z hz
    have := hF z hz
    have := g.down_ge_w hq (by omega)
    omega
  · intro p hp hpd
    exact g.down_ne_add hq hqd hp hpd
  · intro p hqp hpd heq
    have := g.down_injective hq (by omega) (by omega) hpd heq
    omega

end Geometry
end Recaman.SurvivalFamily
