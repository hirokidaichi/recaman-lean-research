import Recaman.SurvivalCountermodelReplay

namespace Recaman.SurvivalFamily

private theorem int_coordinates {x n q r : Int} (hx : x=q*n+r)
    (hr : 0 ≤ r) (hrn : r<n) : x/n=q ∧ x%n=r := by
  have hn : n ≠ 0 := by omega
  have he : q*n+r=r+n*q := by grind
  rw [hx, he]
  constructor
  · rw [Int.add_mul_ediv_left _ _ hn, Int.ediv_eq_zero_of_lt hr hrn]
    omega
  · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr hrn]

namespace Geometry
variable (g : Geometry) {F : List Nat}

def level (F : List Nat) (t : Nat) : Int := g.val F t / (g.B+t : Nat)
def residue (F : List Nat) (t : Nat) : Int := g.val F t % (g.B+t : Nat)

theorem residue_nat (F : List Nat) (t : Nat) :
    g.residue F t = ((g.orbit F t).value % (g.B+t) : Nat) := by
  simp only [residue, orbit, val, SeededReplay.value, Int.natCast_emod]

theorem level_nat (F : List Nat) (t : Nat) :
    g.level F t = ((g.orbit F t).value / (g.B+t) : Nat) := by
  simp only [level, orbit, val, SeededReplay.value, Int.natCast_ediv]

theorem coordinates {t : Nat} {q r : Int}
    (hx : g.val F t=q*(g.B+t : Nat)+r) (hr : 0 ≤ r) (hrn : r<(g.B+t : Nat)) :
    g.level F t=q ∧ g.residue F t=r := int_coordinates hx hr hrn

theorem initial_coordinates (F : List Nat) :
    g.level F 0=3 ∧ g.residue F 0=5*g.j+6 := by
  have hb := g.cast_B
  have hj := g.j_pos
  have hc := g.clock_large
  apply g.coordinates
  · rw [g.val_zero F]
    grind
  · omega
  · omega

theorem middle_coordinates (hF : ∀ z ∈ F, (z : Int) < g.w) :
    g.level F 1=2 ∧ g.residue F 1=5*g.j+3 := by
  have hb := g.cast_B
  have hj := g.j_pos
  have hc := g.clock_large
  apply g.coordinates
  · rw [g.middle_value hF]
    unfold upper
    omega
  · omega
  · omega

theorem lower_coordinates (hF : ∀ z ∈ F, (z : Int) < g.w)
    {i : Nat} (hi : i ≤ g.J) :
    g.level F (2+2*i)=1 ∧ g.residue F (2+2*i)=5*g.j+1-3*i := by
  have hb := g.cast_B
  have hj := g.j_pos
  have hc := g.clock_large
  have hJ := g.cast_J
  apply g.coordinates
  · rw [(g.prefix_invariant hF hi).1]
    unfold lower
    omega
  · omega
  · omega

theorem upper_coordinates (hF : ∀ z ∈ F, (z : Int) < g.w)
    {i : Nat} (hi : i < g.J) :
    g.level F (3+2*i)=2 ∧ g.residue F (3+2*i)=5*g.j-3*i := by
  have hb := g.cast_B
  have hj := g.j_pos
  have hc := g.clock_large
  have hJ := g.cast_J
  apply g.coordinates
  · rw [g.prefix_upper_value hF hi]
    unfold upper
    omega
  · omega
  · omega

theorem rise_coordinates (hF : ∀ z ∈ F, (z : Int) < g.w)
    {p : Nat} (hp : p ≤ g.D) :
    g.level F (g.T+p)=p ∧ g.residue F (g.T+p)=g.upResidue p := by
  have hb := g.boundary_comb
  have hc := g.cast_C
  have hd := g.cast_D
  have hw := g.w_pos
  have hj := g.j_pos
  have hlarge := g.clock_large
  have hr := g.up_residue_bounds (p := p) (by omega) (by omega)
  apply g.coordinates
  · rw [(g.rise_invariant hF hp).1]
    have he := g.up_decomp (p : Int)
    have ht : ((g.B+(g.T+p) : Nat) : Int)=g.c+(p : Int) := by omega
    rw [ht]
    exact he
  · omega
  · omega

theorem fall_coordinates (hF : ∀ z ∈ F, (z : Int) < g.w)
    {k : Nat} (hk : k ≤ g.D) :
    g.level F (g.T+g.D+k)=g.d-k ∧
    g.residue F (g.T+g.D+k)=g.w+tri (g.d-k) := by
  have hb := g.boundary_comb
  have hc := g.cast_C
  have hd := g.cast_D
  have hw := g.w_pos
  have hj := g.j_pos
  have hlarge := g.clock_large
  have hr := g.down_residue_bounds (q := g.d-k) (by omega) (by omega)
  apply g.coordinates
  · rw [(g.down_invariant hF hk).1]
    have he := g.down_decomp (g.d-k)
    have ht : ((g.B+(g.T+g.D+k) : Nat) : Int)=g.c+2*g.d-(g.d-k) := by omega
    rw [ht]
    exact he
  · omega
  · have hd' := g.d_ge
    omega

/-- Every adjacent residue comparison, including phase boundaries. -/
theorem no_wrap (hF : ∀ z ∈ F, (z : Int) < g.w)
    {t : Nat} (ht : t < g.T+2*g.D) : g.residue F (t+1) ≤ g.residue F t := by
  by_cases h0 : t=0
  · subst t
    have h := (g.initial_coordinates F).2
    have h' := (g.middle_coordinates hF).2
    change g.residue F 1 ≤ g.residue F 0
    omega
  by_cases h1 : t=1
  · subst t
    have h := (g.middle_coordinates hF).2
    have h' := (g.lower_coordinates hF (i := 0) (by omega)).2
    simpa using (show g.residue F (2+2*0) ≤ g.residue F 1 by omega)
  by_cases hpre : t < g.T
  · have htdef : g.T = 3+2*g.J := rfl
    by_cases hlast : t=2+2*g.J
    · subst t
      have h := (g.lower_coordinates hF (Nat.le_refl g.J)).2
      have h' := (g.rise_coordinates hF (p := 0) (by omega)).2
      simp only [Nat.add_zero, Int.natCast_zero, upResidue, tri_zero, Int.zero_mul,
        Int.add_zero, Int.sub_zero] at h'
      have hJ := g.cast_J
      have he : 2+2*g.J+1=g.T := by omega
      rw [he]
      omega
    · have hp : t=2+2*((t-2)/2) ∨ t=3+2*((t-2)/2) := by omega
      rcases hp with hp | hp
      · have hi : (t-2)/2 < g.J := by omega
        have h := (g.lower_coordinates hF (Nat.le_of_lt hi)).2
        have h' := (g.upper_coordinates hF hi).2
        have he : t+1=3+2*((t-2)/2) := by omega
        have heq := congrArg (g.residue F) he
        have hpq := congrArg (g.residue F) hp
        omega
      · have hi : (t-2)/2 < g.J := by omega
        have h := (g.upper_coordinates hF hi).2
        have h' := (g.lower_coordinates hF (i := (t-2)/2+1) (by omega)).2
        have he : t+1=2+2*((t-2)/2+1) := by omega
        have heq := congrArg (g.residue F) he
        have hpq := congrArg (g.residue F) hp
        omega
  by_cases hrise : t < g.T+g.D
  · let p := t-g.T
    have hp : p < g.D := by dsimp [p]; omega
    have he : t=g.T+p := by dsimp [p]; omega
    have he' : t+1=g.T+(p+1) := by omega
    have h := (g.rise_coordinates hF (Nat.le_of_lt hp)).2
    have h' := (g.rise_coordinates hF (p := p+1) (by omega)).2
    have hh := g.up_residue_succ (p : Int)
    rw [he', he]
    simp only [Int.natCast_add, Int.natCast_one] at h'
    omega
  · let k := t-(g.T+g.D)
    have hk : k < g.D := by dsimp [k]; omega
    have he : t=g.T+g.D+k := by dsimp [k]; omega
    have he' : t+1=g.T+g.D+(k+1) := by omega
    have h := (g.fall_coordinates hF (Nat.le_of_lt hk)).2
    have h' := (g.fall_coordinates hF (k := k+1) (by omega)).2
    have hd := g.cast_D
    have hh := tri_succ (g.d-(k : Int)-1)
    have ha : g.d-(k : Int)-1+1 = g.d-k := by omega
    rw [ha] at hh
    have ha' : g.d-((k+1 : Nat) : Int)=g.d-k-1 := by omega
    rw [ha'] at h'
    rw [he', he]
    omega

theorem first_late_landing (hF : ∀ z ∈ F, (z : Int) < g.w) :
    g.val F (g.T+2*g.D) = g.w ∧
    g.val F (g.T+2*g.D) < (g.B+(g.T+2*g.D) : Nat) ∧
    (∀ t, g.T < t → t < g.T+2*g.D → (g.B+t : Nat) ≤ g.val F t) := by
  have hd := g.cast_D
  have hc := g.cast_C
  have hb := g.boundary_comb
  have hg := g.gap_linear
  have hlarge := g.clock_large
  have hj := g.j_pos
  have hd' := g.d_ge
  have hv := (g.actual_word hF).2.2.2.2.2.2
  refine ⟨hv, ?_, ?_⟩
  · rw [hv]
    omega
  · intro t ht ht'
    by_cases hr : t ≤ g.T+g.D
    · let p := t-g.T
      have hp : 1 ≤ p ∧ p ≤ g.D := by dsimp [p]; omega
      have he : t=g.T+p := by dsimp [p]; omega
      have hcoord := g.rise_coordinates hF hp.2
      have hlevel : 1 ≤ g.level F t := by rw [he, hcoord.1]; omega
      rw [g.level_nat F t] at hlevel
      have : 0 < g.B+t := by omega
      have hh := Nat.div_mul_le_self (g.orbit F t).value (g.B+t)
      have hm := Nat.mul_le_mul_right (g.B+t)
        (show 1 ≤ (g.orbit F t).value/(g.B+t) by omega)
      change (g.B+t : Nat) ≤ ((g.orbit F t).value : Int)
      omega
    · let k := t-(g.T+g.D)
      have hk : k < g.D := by dsimp [k]; omega
      have he : t=g.T+g.D+k := by dsimp [k]; omega
      have hcoord := g.fall_coordinates hF (Nat.le_of_lt hk)
      have hlevel : 1 ≤ g.level F t := by rw [he, hcoord.1]; omega
      rw [g.level_nat F t] at hlevel
      have hh := Nat.div_mul_le_self (g.orbit F t).value (g.B+t)
      have hm := Nat.mul_le_mul_right (g.B+t)
        (show 1 ≤ (g.orbit F t).value/(g.B+t) by omega)
      change (g.B+t : Nat) ≤ ((g.orbit F t).value : Int)
      omega

end Geometry
end Recaman.SurvivalFamily
