import Recaman.SurvivalCountermodelArithmetic
import Recaman.SeededReplay

namespace Recaman.SurvivalFamily
open SeededReplay

private theorem mem_range_int {N : Nat} {f : Int → Int} {y : Int} :
    y ∈ (List.range N).map (fun (i : Nat) => f (i : Int)) ↔
      ∃ i : Int, 0 ≤ i ∧ i < (N : Int) ∧ f i = y := by
  constructor
  · rintro hm
    rcases List.mem_map.mp hm with ⟨i, hi, heq⟩
    exact ⟨i, by omega, by have := List.mem_range.mp hi; omega, heq⟩
  · rintro ⟨i, hi, hiN, heq⟩
    have he : (i.toNat : Int) = i := Int.toNat_of_nonneg hi
    exact List.mem_map.mpr ⟨i.toNat, List.mem_range.mpr (by omega), by simpa [he] using heq⟩

namespace Geometry
variable (g : Geometry)

def J : Nat := g.j.toNat
def D : Nat := g.d.toNat
def C : Nat := g.c.toNat
def B : Nat := g.C - 2*g.J - 3
def X : Nat := (3*g.c-g.j-3).toNat

@[simp] theorem cast_J : (g.J : Int) = g.j :=
  Int.toNat_of_nonneg (by have := g.j_pos; omega)
@[simp] theorem cast_D : (g.D : Int) = g.d :=
  Int.toNat_of_nonneg (by have := g.d_ge; omega)
@[simp] theorem cast_C : (g.C : Int) = g.c :=
  Int.toNat_of_nonneg (by have := g.c_pos; omega)
@[simp] theorem cast_B : (g.B : Int) = g.c-2*g.j-3 := by
  have := g.cast_C
  have := g.cast_J
  have := g.clock_large
  have := g.j_pos
  unfold B
  omega
@[simp] theorem cast_X : (g.X : Int) = 3*g.c-g.j-3 :=
  Int.toNat_of_nonneg (by have := g.clock_large; have := g.j_pos; omega)

def coreListI : List Int :=
  [0, 3*g.c-g.j-3, 2*g.j-1] ++
    (List.range g.J).map (fun (i : Nat) => 2*g.j+3*((i : Int)+1)) ++
    (List.range (g.D-3)).map (fun (i : Nat) => g.addPoint ((i : Int)+2)-1)

theorem mem_coreListI {y : Int} : y ∈ g.coreListI ↔ g.CoreSeed y := by
  have hj := g.cast_J
  have hd := g.cast_D
  have hd' := g.d_ge
  have hdm : ((g.D-3 : Nat) : Int) = g.d-3 := by omega
  simp only [coreListI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rw [mem_range_int (f := fun i => 2*g.j+3*(i+1)),
    mem_range_int (f := fun i => g.addPoint (i+2)-1)]
  simp only [hj, hdm, CoreSeed]
  constructor
  · rintro ((h | h) | h)
    · rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases h with ⟨i, hi, hiJ, heq⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i+1, by omega, by omega, heq.symm⟩)))
    · rcases h with ⟨i, hi, hiD, heq⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i+2, by omega, by omega, heq.symm⟩)))
  · rintro (h | h | h | ⟨t, ht, htJ, heq⟩ | ⟨p, hp, hpD, heq⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
    · left; right
      refine ⟨t-1, by omega, by omega, ?_⟩
      omega
    · right
      refine ⟨p-2, by omega, by omega, ?_⟩
      simpa using heq.symm

def seed (F : List Nat) : List Nat := F ++ g.coreListI.map Int.toNat
def start (F : List Nat) : State := ⟨g.X, g.seed F⟩
def orbit (F : List Nat) (t : Nat) : State := SeededReplay.run g.B (g.start F) t
abbrev val (F : List Nat) (t : Nat) : Int := SeededReplay.value g.B (g.start F) t
abbrev seen (F : List Nat) (t : Nat) (y : Int) : Prop := SeededReplay.Seen g.B (g.start F) t y

def InF (F : List Nat) (y : Int) : Prop := ∃ z ∈ F, (z : Int) = y

theorem seen_zero (F : List Nat) (y : Int) :
    g.seen F 0 y ↔ InF F y ∨ g.CoreSeed y := by
  constructor
  · rintro ⟨z, hz, heq⟩
    change z ∈ F ++ g.coreListI.map Int.toNat at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact Or.inl ⟨z, hz, heq⟩
    · rcases List.mem_map.mp hz with ⟨x, hx, hxz⟩
      have hm := g.mem_coreListI.mp hx
      have hn := g.core_nonneg hm
      have he : (x.toNat : Int) = x := Int.toNat_of_nonneg hn
      have : x = y := by omega
      exact Or.inr (this ▸ hm)
  · rintro (⟨z, hz, heq⟩ | hm)
    · exact ⟨z, List.mem_append.mpr (Or.inl hz), heq⟩
    · have hn := g.core_nonneg hm
      exact ⟨y.toNat, List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨y, g.mem_coreListI.mpr hm, rfl⟩)), Int.toNat_of_nonneg hn⟩

theorem core_seen (F : List Nat) {y : Int} (hy : g.CoreSeed y) (t : Nat) :
    g.seen F t y :=
  SeededReplay.seen_mono (Nat.zero_le _) ((g.seen_zero F y).mpr (Or.inr hy))

theorem initial_mem (F : List Nat) : (g.start F).value ∈ (g.start F).seen := by
  have : g.seen F 0 (3*g.c-g.j-3) := g.core_seen F (Or.inr (Or.inl rfl)) 0
  rcases this with ⟨z, hz, heq⟩
  have : z = g.X := by have := g.cast_X; omega
  simpa [start, SeededReplay.run, this] using hz

@[simp] theorem val_zero (F : List Nat) : g.val F 0 = 3*g.c-g.j-3 := g.cast_X

theorem seen_succ (F : List Nat) (t : Nat) (y : Int) :
    g.seen F (t+1) y ↔ y = g.val F (t+1) ∨ g.seen F t y :=
  SeededReplay.seen_succ g.B (g.start F) t y

theorem sub_value {F : List Nat} {t : Nat} {z : Int}
    (hz : 0 < z) (hv : g.val F t = z + (g.B+t+1 : Nat))
    (hf : ¬ g.seen F t z) : g.val F (t+1) = z := SeededReplay.subtract hz hv hf

theorem add_value {F : List Nat} {t : Nat}
    (h : g.val F t ≤ (g.B+t+1 : Nat) ∨ g.seen F t (g.val F t-(g.B+t+1 : Nat))) :
    g.val F (t+1) = g.val F t + (g.B+t+1 : Nat) := SeededReplay.add h

variable {F : List Nat}

theorem inF_lt (hF : ∀ z ∈ F, (z : Int) < g.w) {y : Int} (hy : InF F y) : y < g.w := by
  rcases hy with ⟨z, hz, rfl⟩
  exact hF z hz

def PrefixHistory (F : List Nat) (k y : Int) : Prop :=
  InF F y ∨ g.CoreSeed y ∨
  (∃ t : Int, 1 ≤ t ∧ t ≤ g.j+1 ∧ y = g.upper t) ∨
  (∃ t : Int, k ≤ t ∧ t ≤ g.j ∧ y = g.lower t)

def PrefixInv (F : List Nat) (i : Nat) : Prop :=
  g.val F (2+2*i) = g.lower (g.j-i) ∧
  ∀ y, g.seen F (2+2*i) y → g.PrefixHistory F (g.j-i) y

theorem prefix_mono {k l y : Int} (hlk : l ≤ k) (hy : g.PrefixHistory F k y) :
    g.PrefixHistory F l y := by
  rcases hy with hy | hy | hy | ⟨t, ht, htj, heq⟩
  · exact Or.inl hy
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr (Or.inl hy))
  · exact Or.inr (Or.inr (Or.inr ⟨t, by omega, htj, heq⟩))

theorem prefix_fresh (hF : ∀ z ∈ F, (z : Int) < g.w)
    {k : Int} (hk : 1 ≤ k) (hkj : k ≤ g.j) :
    ¬ g.PrefixHistory F k (g.lower (k-1)) := by
  have hj := g.j_pos
  have hc := g.clock_large
  have hw := g.gap_linear
  have hd := g.d_ge
  intro hm
  rcases hm with hm | hm | ⟨t, ht, htj, heq⟩ | ⟨t, ht, htj, heq⟩
  · have := g.inF_lt hF hm
    unfold lower at this
    omega
  · exact g.lower_not_core (by omega) (by omega) hm
  · exact g.lower_ne_upper (by omega) (by omega) ht htj heq
  · unfold lower at heq
    omega

theorem middle_value (hF : ∀ z ∈ F, (z : Int) < g.w) :
    g.val F 1 = g.upper (g.j+1) := by
  have hj := g.j_pos
  have hc := g.clock_large
  have hg := g.gap_linear
  have hd := g.d_ge
  have hb := g.cast_B
  apply g.sub_value (t := 0)
  · unfold upper; omega
  · rw [g.val_zero F]
    unfold upper
    omega
  · intro hs
    rcases (g.seen_zero F _).mp hs with hf | hh
    · have := g.inF_lt hF hf
      unfold upper at this
      omega
    · exact g.middle_not_core hh

theorem prefix_zero (hF : ∀ z ∈ F, (z : Int) < g.w) : g.PrefixInv F 0 := by
  have hj := g.j_pos
  have hc := g.clock_large
  have hg := g.gap_linear
  have hd := g.d_ge
  have hb := g.cast_B
  have hmid := g.middle_value hF
  have hlo : g.val F 2 = g.lower g.j := by
    apply g.sub_value (t := 1)
    · unfold lower; omega
    · rw [hmid]
      unfold upper lower
      omega
    · intro hs
      rcases (g.seen_succ F 0 _).mp hs with he | hs
      · rw [hmid] at he
        exact g.lower_ne_upper (by omega) (by omega) (by omega) (by omega) he
      · rcases (g.seen_zero F _).mp hs with hf | hh
        · have := g.inF_lt hF hf
          unfold lower at this
          omega
        · exact g.lower_not_core (by omega) (by omega) hh
  constructor
  · simpa using hlo
  · intro y hy
    simp only [Int.natCast_zero, Int.sub_zero]
    rcases (g.seen_succ F 1 y).mp hy with he | hs
    · rw [hlo] at he
      exact Or.inr (Or.inr (Or.inr ⟨g.j, by omega, by omega, he⟩))
    · rcases (g.seen_succ F 0 y).mp hs with he | hs
      · rw [hmid] at he
        exact Or.inr (Or.inr (Or.inl ⟨g.j+1, by omega, by omega, he⟩))
      · rcases (g.seen_zero F y).mp hs with hf | hh
        · exact Or.inl hf
        · exact Or.inr (Or.inl hh)

theorem prefix_pair (hF : ∀ z ∈ F, (z : Int) < g.w)
    {i : Nat} (hi : i < g.J) (hprev : g.PrefixInv F i) :
    g.val F (3+2*i) = g.upper (g.j-i) ∧ g.PrefixInv F (i+1) := by
  have hJ := g.cast_J
  have hb := g.cast_B
  have hj := g.j_pos
  have hc := g.clock_large
  have hk : 1 ≤ g.j-(i : Int) := by omega
  have hki : g.j-(i : Int) ≤ g.j := by omega
  have htime : ((g.B+(2+2*i)+1 : Nat) : Int) = g.c-2*(g.j-i) := by omega
  have hn := g.core_seen F (y := 2*g.j+3*(g.j-i))
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨g.j-i, hk, hki, rfl⟩)))) (2+2*i)
  have hcan : g.seen F (2+2*i)
      (g.val F (2+2*i)-(g.B+(2+2*i)+1 : Nat)) := by
    rw [hprev.1, htime]
    have he : g.lower (g.j-i)-(g.c-2*(g.j-i)) = 2*g.j+3*(g.j-i) := by unfold lower; omega
    rw [he]
    exact hn
  have hAraw := g.add_value (Or.inr hcan)
  have htA : 2+2*i+1 = 3+2*i := by omega
  rw [htA, hprev.1, htime] at hAraw
  have hA : g.val F (3+2*i) = g.upper (g.j-i) := by
    unfold upper lower at *
    omega
  have hAhist : ∀ y, g.seen F (3+2*i) y → g.PrefixHistory F (g.j-i) y := by
    intro y hy
    rw [← htA] at hy
    rcases (g.seen_succ F (2+2*i) y).mp hy with he | hs
    · rw [htA, hA] at he
      exact Or.inr (Or.inr (Or.inl ⟨g.j-i, hk, by omega, he⟩))
    · exact hprev.2 y hs
  have hS : g.val F ((3+2*i)+1) = g.lower (g.j-i-1) := by
    apply g.sub_value
    · unfold lower; omega
    · rw [hA]
      unfold lower upper
      omega
    · intro hs
      exact g.prefix_fresh hF hk hki (hAhist _ hs)
  have htS : 3+2*i+1 = 2+2*(i+1) := by omega
  have heK : g.j-(i : Int)-1 = g.j-((i+1 : Nat) : Int) := by omega
  refine ⟨hA, ?_, ?_⟩
  · simpa [htS, heK] using hS
  · intro y hy
    rw [← htS] at hy
    rcases (g.seen_succ F (3+2*i) y).mp hy with he | hs
    · rw [hS, heK] at he
      exact Or.inr (Or.inr (Or.inr ⟨g.j-(i+1 : Nat), by omega, by omega, he⟩))
    · exact g.prefix_mono (by omega) (hAhist y hs)

theorem prefix_invariant (hF : ∀ z ∈ F, (z : Int) < g.w)
    {i : Nat} (hi : i ≤ g.J) : g.PrefixInv F i := by
  induction i with
  | zero => exact g.prefix_zero hF
  | succ i ih => exact (g.prefix_pair hF (by omega) (ih (by omega))).2

theorem prefix_upper_value (hF : ∀ z ∈ F, (z : Int) < g.w)
    {i : Nat} (hi : i < g.J) : g.val F (3+2*i) = g.upper (g.j-i) :=
  (g.prefix_pair hF hi (g.prefix_invariant hF (by omega))).1

def T : Nat := 3+2*g.J
@[simp] theorem cast_T : (g.T : Int) = 3+2*g.j := by simp [T]

theorem boundary_comb : g.B+g.T = g.C := by
  have := g.cast_B
  have := g.cast_C
  have := g.cast_T
  omega

theorem seen_current (F : List Nat) (t : Nat) : g.seen F t (g.val F t) :=
  SeededReplay.seen_value (g.initial_mem F) t

theorem seen_after {F : List Nat} {i k : Nat} {y : Int}
    (hik : i ≤ k) (hy : g.seen F i y) : g.seen F k y := SeededReplay.seen_mono hik hy

def FullHistory (F : List Nat) (y : Int) : Prop := InF F y ∨ g.CoreSeed y ∨ g.Rails y

theorem prefix_full {k y : Int} (hk : 0 ≤ k) (hy : g.PrefixHistory F k y) :
    g.FullHistory F y := by
  rcases hy with h | h | ⟨t, ht, htj, heq⟩ | ⟨t, ht, htj, heq⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr ⟨t, ht, htj, heq⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨t, by omega, htj, heq⟩))

def RiseInv (F : List Nat) (p : Nat) : Prop :=
  g.val F (g.T+p) = g.addPoint p ∧
  ∀ y, g.seen F (g.T+p) y →
    g.FullHistory F y ∨ ∃ q : Int, 0 ≤ q ∧ q ≤ p ∧ y = g.addPoint q

theorem last_lower (hF : ∀ z ∈ F, (z : Int) < g.w) :
    g.val F (2+2*g.J) = g.lower 0 := by
  have h := (g.prefix_invariant hF (Nat.le_refl g.J)).1
  simpa using h

theorem comb_value (hF : ∀ z ∈ F, (z : Int) < g.w) : g.val F g.T = 2*g.j := by
  have hpre := g.prefix_invariant hF (Nat.le_refl g.J)
  have hv := g.last_lower hF
  have hb := g.cast_B
  have hJ := g.cast_J
  have hj := g.j_pos
  have hc := g.clock_large
  have hg := g.gap_linear
  have hd := g.d_ge
  have hs : g.val F ((2+2*g.J)+1) = 2*g.j := by
    apply g.sub_value
    · omega
    · rw [hv]
      unfold lower
      omega
    · intro hy
      have hm := g.prefix_full (by simp) (hpre.2 _ hy)
      rcases hm with hf | hh | hr
      · have := g.inF_lt hF hf
        omega
      · exact g.landing_not_core hh
      · exact g.landing_not_rails hr
  have ht : 2+2*g.J+1 = g.T := by unfold T; omega
  simpa [ht] using hs

theorem rise_zero (hF : ∀ z ∈ F, (z : Int) < g.w) : g.RiseInv F 0 := by
  have hv := g.comb_value hF
  have hp := g.prefix_invariant hF (Nat.le_refl g.J)
  have ht : 2+2*g.J+1 = g.T := by unfold T; omega
  constructor
  · simpa [addPoint] using hv
  · intro y hy
    simp only [Nat.add_zero] at hy
    rw [← ht] at hy
    rcases (g.seen_succ F (2+2*g.J) y).mp hy with he | hs
    · right
      refine ⟨0, by omega, by omega, ?_⟩
      rw [ht, hv] at he
      simpa [addPoint] using he
    · exact Or.inl (g.prefix_full (by simp) (hp.2 y hs))

theorem rise_step (hF : ∀ z ∈ F, (z : Int) < g.w)
    {p : Nat} (hp : p < g.D) (hprev : g.RiseInv F p) : g.RiseInv F (p+1) := by
  have hD := g.cast_D
  have hb := g.boundary_comb
  have hC := g.cast_C
  have hj := g.j_pos
  have hc := g.clock_large
  have htime : ((g.B+(g.T+p)+1 : Nat) : Int) = g.c+(p : Int)+1 := by omega
  have hforced : g.val F (g.T+p) ≤ (g.B+(g.T+p)+1 : Nat) ∨
      g.seen F (g.T+p) (g.val F (g.T+p)-(g.B+(g.T+p)+1 : Nat)) := by
    by_cases hp0 : p = 0
    · left
      rw [hprev.1, hp0]
      simp only [Int.natCast_zero, addPoint, Int.zero_mul, Int.zero_add, tri_zero, Int.add_zero]
      omega
    · right
      rw [hprev.1, htime, g.add_candidate]
      by_cases hp1 : p = 1
      · subst p
        have he : g.addPoint ((1 : Nat)-1)-1 = 2*g.j-1 := by simp [addPoint]
        simpa [addPoint] using g.core_seen F (Or.inr (Or.inr (Or.inl rfl))) (g.T+1)
      · by_cases hp2 : p = 2
        · subst p
          have hv := g.last_lower hF
          have hs := g.seen_current F (2+2*g.J)
          rw [hv] at hs
          have hs' := g.seen_after (show 2+2*g.J ≤ g.T+2 by unfold T; omega) hs
          simpa [addPoint, lower] using hs'
        · exact g.core_seen F
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨(p : Int)-1, by omega, by omega, rfl⟩)))) _
  have ha := g.add_value hforced
  have ht : g.T+p+1 = g.T+(p+1) := by omega
  rw [ht, hprev.1, htime] at ha
  have hv : g.val F (g.T+(p+1)) = g.addPoint (p+1 : Nat) := by
    have he := g.add_succ (p : Int)
    simpa only [Int.natCast_add, Int.natCast_one] using ha.trans he.symm
  refine ⟨hv, ?_⟩
  intro y hy
  rw [← ht] at hy
  rcases (g.seen_succ F (g.T+p) y).mp hy with he | hs
  · right
    rw [ht, hv] at he
    exact ⟨(p+1 : Nat), by omega, by omega, he⟩
  · rcases hprev.2 y hs with hh | ⟨q, hq, hqp, he⟩
    · exact Or.inl hh
    · exact Or.inr ⟨q, hq, by omega, he⟩

theorem rise_invariant (hF : ∀ z ∈ F, (z : Int) < g.w)
    {p : Nat} (hp : p ≤ g.D) : g.RiseInv F p := by
  induction p with
  | zero => exact g.rise_zero hF
  | succ p ih => exact g.rise_step hF (by omega) (ih (by omega))

def DownInv (F : List Nat) (k : Nat) : Prop :=
  g.val F (g.T+g.D+k) = g.downPoint (g.d-k) ∧
  ∀ y, g.seen F (g.T+g.D+k) y →
    g.FullHistory F y ∨
    (∃ p : Int, 0 ≤ p ∧ p ≤ g.d ∧ y = g.addPoint p) ∨
    (∃ p : Int, g.d-k ≤ p ∧ p ≤ g.d ∧ y = g.downPoint p)

theorem down_initial (hF : ∀ z ∈ F, (z : Int) < g.w) : g.DownInv F 0 := by
  have h := g.rise_invariant hF (Nat.le_refl g.D)
  constructor
  · simpa [g.down_start] using h.1
  · intro y hy
    rcases h.2 y hy with h | ⟨p, hp, hpD, he⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨p, hp, by simpa using hpD, he⟩)

theorem down_successor (hF : ∀ z ∈ F, (z : Int) < g.w)
    {k : Nat} (hk : k < g.D) (hprev : g.DownInv F k) : g.DownInv F (k+1) := by
  have hD := g.cast_D
  have hB := g.boundary_comb
  have hC := g.cast_C
  have hw := g.w_pos
  have hq : 0 ≤ g.d-(k : Int)-1 := by omega
  have hqd : g.d-(k : Int)-1 < g.d := by omega
  have hf := g.descent_fresh hF hq hqd
  have hv : g.val F ((g.T+g.D+k)+1) = g.downPoint (g.d-k-1) := by
    apply g.sub_value
    · have := g.down_ge_w hq (by omega)
      omega
    · rw [hprev.1]
      have he := g.down_step (g.d-k-1)
      have harg : g.d-(k : Int)-1+1 = g.d-k := by omega
      rw [harg] at he
      have htime : ((g.B+(g.T+g.D+k)+1 : Nat) : Int) = g.c+2*g.d-(g.d-k-1) := by omega
      rw [htime]
      exact he
    · intro hs
      rcases hprev.2 _ hs with (hin | hcore | hrails) | ⟨p,hp,hpd,he⟩ | ⟨p,hqp,hpd,he⟩
      · rcases hin with ⟨z,hz,he⟩
        exact hf.1 z hz he.symm
      · exact hf.2.1 hcore
      · exact hf.2.2.1 hrails
      · exact hf.2.2.2.1 p hp hpd he
      · exact hf.2.2.2.2 p (by omega) hpd he
  have ht : g.T+g.D+k+1 = g.T+g.D+(k+1) := by omega
  have harg : g.d-(k : Int)-1 = g.d-((k+1 : Nat) : Int) := by omega
  refine ⟨?_, ?_⟩
  · simpa [ht, harg] using hv
  · intro y hy
    rw [← ht] at hy
    rcases (g.seen_succ F (g.T+g.D+k) y).mp hy with he | hs
    · right; right
      rw [hv, harg] at he
      exact ⟨g.d-(k+1 : Nat), by omega, by omega, he⟩
    · rcases hprev.2 y hs with hh | hh | ⟨p,hp,hpd,he⟩
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ⟨p,by omega,hpd,he⟩)

theorem down_invariant (hF : ∀ z ∈ F, (z : Int) < g.w)
    {k : Nat} (hk : k ≤ g.D) : g.DownInv F k := by
  induction k with
  | zero => exact g.down_initial hF
  | succ k ih => exact g.down_successor hF (by omega) (ih (by omega))

/-- Both landings and the complete prescribed runs are outputs of `Basic.step`;
none of the history/freshness decisions is assumed. -/
theorem actual_word (hF : ∀ z ∈ F, (z : Int) < g.w) :
    g.val F 1 = g.upper (g.j+1) ∧
    (∀ i, i ≤ g.J → g.val F (2+2*i) = g.lower (g.j-i)) ∧
    (∀ i, i < g.J → g.val F (3+2*i) = g.upper (g.j-i)) ∧
    g.val F g.T = 2*g.j ∧
    (∀ p, p ≤ g.D → g.val F (g.T+p) = g.addPoint p) ∧
    (∀ k, k ≤ g.D → g.val F (g.T+g.D+k) = g.downPoint (g.d-k)) ∧
    g.val F (g.T+2*g.D) = g.w := by
  refine ⟨g.middle_value hF, ?_, ?_, g.comb_value hF, ?_, ?_, ?_⟩
  · intro i hi; exact (g.prefix_invariant hF hi).1
  · intro i hi; exact g.prefix_upper_value hF hi
  · intro p hp; exact (g.rise_invariant hF hp).1
  · intro k hk; exact (g.down_invariant hF hk).1
  · have h := (g.down_invariant hF (Nat.le_refl g.D)).1
    have ht : g.T+g.D+g.D = g.T+2*g.D := by omega
    simpa [ht] using h

end Geometry
end Recaman.SurvivalFamily
