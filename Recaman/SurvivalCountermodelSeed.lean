import Recaman.SurvivalCountermodelResidue

namespace Recaman.SurvivalFamily

/-- A concrete cofinal choice; a larger D than the smallest admissible one is harmless. -/
def parameterJ (m : Nat) : Int := 2*((m : Int)+10)*((m : Int)+10)+(m : Int)+1

def parameters (m : Nat) : Geometry where
  w := 2*((m : Int)+1)
  d := 2*((m : Int)+10)
  j := parameterJ m
  c := 82*parameterJ m+17+2*((5*parameterJ m+1)%2)
  w_pos := by omega
  d_ge := by omega
  size_eq := by dsimp [parameterJ]; grind
  clearance := by
    have hm : 0 ≤ (m : Int) := by omega
    have := Int.mul_nonneg hm hm
    grind
  clock_large := by
    have hm : 0 ≤ (m : Int) := by omega
    have := Int.mul_nonneg hm hm
    have hr : 0 ≤ (5*parameterJ m+1)%2 := Int.emod_nonneg _ (by decide)
    dsimp [parameterJ] at *
    grind

/-- Including the list length lets the result cover lists with repetitions as well as sets. -/
def scale (F : List Nat) : Nat := F.foldr max F.length

private theorem fold_max_base (F : List Nat) (a : Nat) : a ≤ F.foldr max a := by
  induction F with
  | nil => simp
  | cons x xs ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

private theorem fold_max_member {F : List Nat} {x a : Nat} (hx : x ∈ F) :
    x ≤ F.foldr max a := by
  induction F with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem scale_length (F : List Nat) : F.length ≤ scale F := fold_max_base F _
theorem scale_member {F : List Nat} {x : Nat} (hx : x ∈ F) : x ≤ scale F :=
  fold_max_member hx

theorem parameters_cover (F : List Nat) : ∀ x ∈ F, (x : Int) < (parameters (scale F)).w := by
  intro x hx
  have := scale_member hx
  change (x : Int) < 2*((scale F : Int)+1)
  omega

namespace Geometry

theorem d_le_j (g : Geometry) : g.d ≤ g.j := by
  have hd := g.d_ge
  have hs := g.size_eq
  have hw := g.w_pos
  have := Int.mul_le_mul_of_nonneg_right hd (show 0 ≤ g.d by omega)
  omega

theorem seed_length (g : Geometry) (F : List Nat) :
    (g.seed F).length = F.length+3+g.J+(g.D-3) := by
  simp [seed, coreListI]
  omega

theorem core_upper (g : Geometry) {y : Int} (hy : g.CoreSeed y) :
    y ≤ g.j*g.c+4*g.j := by
  have hj := g.j_pos
  have hc := g.c_pos
  have hd := g.d_ge
  have hdj := g.d_le_j
  have hj3 : 3 ≤ g.j := by omega
  rcases hy with h | h | h | ⟨t, ht, htj, h⟩ | ⟨p, hp, hpd, h⟩
  · have := Int.mul_nonneg (show 0 ≤ g.j by omega) (show 0 ≤ g.c by omega)
    omega
  · have := Int.mul_le_mul_of_nonneg_right hj3 (show 0 ≤ g.c by omega)
    omega
  · have := Int.mul_nonneg (show 0 ≤ g.j by omega) (show 0 ≤ g.c by omega)
    omega
  · have hlarge := g.clock_large
    have := Int.mul_le_mul_of_nonneg_right (show 1 ≤ g.c by omega) (show 0 ≤ g.j by omega)
    grind
  · have ht := g.tri_bounds (p := p) (by omega) (by omega)
    have := Int.mul_le_mul_of_nonneg_right (show p ≤ g.j by omega) (show 0 ≤ g.c by omega)
    dsimp [addPoint] at h
    omega

end Geometry

 theorem parameters_clock (m : Nat) :
    ((parameters m).B : Int)=80*parameterJ m+14+2*((5*parameterJ m+1)%2) := by
  have h := (parameters m).cast_B
  change ((parameters m).B : Int) = _
  change ((parameters m).B : Int) =
    (82*parameterJ m+17+2*((5*parameterJ m+1)%2))-2*parameterJ m-3 at h
  omega

 theorem parameters_range (m : Nat) :
    2*((parameters m).j*(parameters m).c+4*(parameters m).j) ≤
      ((parameters m).B : Int)*((parameters m).B+1) := by
  have hj := (parameters m).j_pos
  have hr : 0 ≤ (5*parameterJ m+1)%2 := Int.emod_nonneg _ (by decide)
  have hj' : 0 ≤ parameterJ m := by exact Int.le_of_lt hj
  have := Int.mul_nonneg hj' hj'
  have := Int.mul_nonneg hr hr
  have := Int.mul_nonneg hj' hr
  rw [parameters_clock]
  change 2*(parameterJ m*(82*parameterJ m+17+2*((5*parameterJ m+1)%2))+4*parameterJ m) ≤ _
  grind

 theorem seed_payload (F : List Nat) :
    let g := parameters (scale F)
    (∀ x ∈ F, x ∈ g.seed F) ∧ 0 ∈ g.seed F ∧ g.X ∈ g.seed F ∧
    (g.seed F).length ≤ g.B+1 ∧
    (∀ x ∈ g.seed F, 2*x ≤ g.B*(g.B+1)) := by
  dsimp only
  let g := parameters (scale F)
  have hF := parameters_cover F
  have hj := g.j_pos
  have hd := g.d_le_j
  have hlen := scale_length F
  have hb := parameters_clock (scale F)
  have hJ := g.cast_J
  have hD := g.cast_D
  have hr : 0 ≤ (5*parameterJ (scale F)+1)%2 := Int.emod_nonneg _ (by decide)
  have hmj : (scale F : Int) ≤ g.j := by
    have hm : 0 ≤ (scale F : Int) := by omega
    have := Int.mul_nonneg hm hm
    dsimp [g, parameters, parameterJ]
    grind
  refine ⟨?_, ?_, g.initial_mem F, ?_, ?_⟩
  · intro x hx
    exact List.mem_append_left _ hx
  · have h : g.CoreSeed 0 := Or.inl rfl
    have hh := (g.seen_zero F 0).mpr (Or.inr h)
    rcases hh with ⟨z, hz, he⟩
    have : z=0 := by omega
    change z ∈ g.seed F at hz
    simpa [this] using hz
  · rw [g.seed_length]
    change _ ≤ g.B+1
    change (g.B : Int)=80*g.j+14+2*((5*g.j+1)%2) at hb
    omega
  · intro x hx
    have hy : Geometry.InF F (x : Int) ∨ g.CoreSeed (x : Int) :=
      (g.seen_zero F (x : Int)).mp ⟨x, hx, rfl⟩
    have hbound : (x : Int) ≤ g.j*g.c+4*g.j := by
      rcases hy with hf | hc
      · have hlt := g.inF_lt hF hf
        have hg := g.gap_linear
        have hh := Int.mul_nonneg (show 0 ≤ g.j by omega) (show 0 ≤ g.c by have := g.c_pos; omega)
        omega
      · exact g.core_upper hc
    have hh := parameters_range (scale F)
    change 2*(g.j*g.c+4*g.j) ≤ (g.B : Int)*(g.B+1) at hh
    have hh' : ((2*x : Nat) : Int) ≤ ((g.B*(g.B+1) : Nat) : Int) := by
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one]
      omega
    exact Int.ofNat_le.mp hh'

 theorem parameters_parity (m : Nat) :
    (parameters m).X % 2 = ((parameters m).B*((parameters m).B+1)/2)%2 := by
  let g := parameters m
  have hb := parameters_clock m
  have hx := g.cast_X
  change (g.B : Int)=80*g.j+14+2*((5*g.j+1)%2) at hb
  change (g.X : Int)=3*(82*g.j+17+2*((5*g.j+1)%2))-g.j-3 at hx
  have hj : 0 ≤ g.j := Int.le_of_lt g.j_pos
  have hr : (5*g.j+1)%2=0 ∨ (5*g.j+1)%2=1 := by omega
  have hp := Int.mul_emod (g.B : Int) ((g.B : Int)+1) 4
  have htri := twice_tri (g.B : Int)
  have he : (g.X : Int)%2=tri (g.B : Int)%2 := by
    rcases hr with hr | hr
    · have hb4 : (g.B : Int)%4=2 := by omega
      have hb4' : ((g.B : Int)+1)%4=3 := by omega
      rw [hb4, hb4'] at hp
      omega
    · have hb4 : (g.B : Int)%4=0 := by omega
      have hb4' : ((g.B : Int)+1)%4=1 := by omega
      rw [hb4, hb4'] at hp
      omega
  have he' : ((g.X%2 : Nat) : Int) = ((g.B*(g.B+1)/2%2 : Nat) : Int) := by
    simpa only [Int.natCast_emod, Int.natCast_ediv, Int.natCast_mul,
      Int.natCast_add, Int.natCast_one, tri, show ((2 : Nat) : Int)=2 from rfl] using he
  exact Int.ofNat_inj.mp he'

 theorem parameters_even (m : Nat) :
    (parameters m).w%2=0 ∧ (parameters m).d%2=0 := by
  change (2*((m : Int)+1))%2=0 ∧ (2*((m : Int)+10))%2=0
  omega

 theorem parameters_paper_clock (m : Nat) :
    ((parameters m).B+2 : Nat) =
      16*(5*(parameters m).j+1)+2*((5*(parameters m).j+1)%2) := by
  have := parameters_clock m
  change ((parameters m).B : Int)=80*(parameters m).j+14+2*((5*(parameters m).j+1)%2) at this
  omega

end Recaman.SurvivalFamily
