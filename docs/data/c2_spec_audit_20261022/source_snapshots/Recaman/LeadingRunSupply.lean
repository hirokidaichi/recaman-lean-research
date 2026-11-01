import Recaman.ShortPeriodicSupply

namespace Recaman.LeadingRunSupply

/-! A sharp, lag-independent obstruction for P2 supply after a long A run.

Words are newest-first. The bound concerns the unchanged P2 sum and moment,
not actual-orbit reachability or the full periodic capacity conjecture.
-/

open ShortPeriodicSupply (sign)

def ones : List Bool → Int
  | [] => 0
  | b :: w => (if b then 1 else 0) + ones w

def positions : List Bool → Int
  | [] => 0
  | b :: w => (if b then 1 else 0) + ones w + positions w

def mass (w : List Bool) : Int := (w.map sign).sum

def moment : List Bool → Int
  | [] => 0
  | b :: w => sign b + mass w + moment w

def P2 (w : List Bool) : Prop := mass w = 1 ∧ moment w = 0

@[simp] theorem mass_nil : mass [] = 0 := rfl
@[simp] theorem mass_cons (b : Bool) (w : List Bool) :
    mass (b :: w) = sign b + mass w := by simp [mass]

theorem ones_bounds (w : List Bool) : 0 ≤ ones w ∧ ones w ≤ w.length := by
  induction w with
  | nil => simp [ones]
  | cons b w ih => cases b <;> simp [ones, List.length_cons] <;> omega

theorem mass_eq (w : List Bool) : mass w = 2 * ones w - w.length := by
  induction w with
  | nil => simp [ones]
  | cons b w ih => cases b <;> simp [ones, sign, List.length_cons, ih] <;> omega

theorem twice_moment (w : List Bool) :
    2 * moment w = 4 * positions w - (w.length : Int) * (w.length + 1) := by
  induction w with
  | nil => simp [moment, positions]
  | cons b w ih =>
    have hm := mass_eq w
    cases b <;> simp [moment, positions, sign, List.length_cons] <;> grind

theorem ones_append (u v : List Bool) : ones (u ++ v) = ones u + ones v := by
  induction u with
  | nil => simp [ones]
  | cons b u ih => cases b <;> simp [ones, ih] <;> omega

theorem positions_append (u v : List Bool) :
    positions (u ++ v) = positions u + positions v + (u.length : Int) * ones v := by
  induction u with
  | nil => simp [positions]
  | cons b u ih =>
    cases b <;> simp [positions, ones_append, ih, List.length_cons] <;> grind

theorem mass_append (u v : List Bool) : mass (u ++ v) = mass u + mass v := by
  simp [mass, List.map_append, List.sum_append]

theorem moment_append (u v : List Bool) :
    moment (u ++ v) = moment u + moment v + (u.length : Int) * mass v := by
  induction u with
  | nil => simp [moment]
  | cons b u ih => simp [moment, mass_append, ih, List.length_cons]; grind

@[simp] theorem ones_replicate_A (m : Nat) : ones (List.replicate m true) = m := by
  induction m with
  | zero => simp [ones]
  | succ m ih => simp [List.replicate_succ, ones, ih]; omega

theorem positions_replicate_A (m : Nat) :
    2 * positions (List.replicate m true) = (m : Int) * (m + 1) := by
  induction m with
  | zero => simp [positions]
  | succ m ih => simp [List.replicate_succ, positions, ones_replicate_A]; grind

/-- Among words of fixed length and A count, A positions have largest sum
when all A signs are placed last. -/
theorem positions_upper (w : List Bool) :
    2 * positions w ≤ ones w * (2 * (w.length : Int) - ones w + 1) := by
  induction w with
  | nil => simp [positions, ones]
  | cons b w ih =>
    have hb := ones_bounds w
    cases b <;> simp [positions, ones, List.length_cons] <;> grind

theorem p2_count_identities (w : List Bool) (h : P2 w) :
    (w.length : Int) = 2 * ones w - 1 ∧
    2 * positions w = 2 * (ones w * ones w) - ones w ∧ ones w % 2 = 0 := by
  have hs := mass_eq w
  have hm := twice_moment w
  obtain ⟨h1, h0⟩ := h
  have hlen : (w.length : Int) = 2 * ones w - 1 := by omega
  have hp : 2 * positions w = 2 * (ones w * ones w) - ones w := by grind
  exact ⟨hlen, hp, by omega⟩

/-- No finite lag upper bound is assumed. -/
theorem leading_run_bound (m : Nat) (tail : List Bool) (hm : 3 ≤ m)
    (h : P2 (List.replicate m true ++ tail)) :
    4 * m ≤ (List.replicate m true ++ tail).length + 1 := by
  have hc := p2_count_identities _ h
  have ht := positions_upper tail
  have hb := ones_bounds tail
  have hp := positions_replicate_A m
  simp only [ones_append, ones_replicate_A, positions_append,
    List.length_append, List.length_replicate, Int.natCast_add] at hc
  have hn : (tail.length : Int) = m + 2 * ones tail - 1 := by omega
  rw [hn] at ht
  have hcalc :
      ones tail * (2 * ((m : Int) + 2 * ones tail - 1) - ones tail + 1) -
        2 * positions tail = ones tail * ones tail - (m : Int) * m + 2 * m := by
    grind
  have hquad : 0 ≤ ones tail * ones tail - (m : Int) * m + 2 * m := by omega
  have hq : (m : Int) ≤ ones tail := by
    by_cases hle : (m : Int) ≤ ones tail
    · exact hle
    · have hsmall : ones tail ≤ (m : Int) - 2 := by omega
      have hsquare := Int.mul_le_mul hsmall hsmall hb.1 (by omega)
      have hid : ((m : Int) - 2) * (m - 2) = (m : Int)*m - 4*m + 4 := by grind
      omega
  have hlen : (List.replicate m true ++ tail).length = m + tail.length := by simp
  omega

def past (e : Int → Bool) (t : Int) (d : Nat) : List Bool :=
  (List.range d).map fun i => e (t - ((i+1 : Nat) : Int))

theorem moment_map_range (f : Nat → Bool) (d : Nat) :
    moment ((List.range d).map f) =
      ((List.range d).map fun i => ((i+1 : Nat) : Int) * sign (f i)).sum := by
  induction d with
  | zero => simp [moment]
  | succ d ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, moment_append]
    simp [moment, ih, Int.natCast_add]
    grind

theorem past_p2_iff (e : Int → Bool) (t : Int) (d : Nat) :
    P2 (past e t d) ↔ ShortPeriodicSupply.P2 e t d := by
  unfold P2 past ShortPeriodicSupply.P2
  rw [moment_map_range]
  simp [mass, List.map_map, Function.comp_def]

theorem take_leading (w : List Bool) (m : Nat) (hm : m ≤ w.length)
    (ha : ∀ i (hi : i < m), w[i]'(by omega) = true) :
    w.take m = List.replicate m true := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    have him : i < m := by simpa using hj
    simpa using ha i him

/-- Semantic bridge to the original integer-clock P2 predicate. -/
theorem stream_leading_run_bound (e : Int → Bool) (t : Int) (d m : Nat)
    (hm : 3 ≤ m) (hmd : m ≤ d)
    (ha : ∀ i, i < m → e (t - ((i+1 : Nat) : Int)) = true)
    (h : ShortPeriodicSupply.P2 e t d) : 4 * m ≤ d + 1 := by
  have hlen : (past e t d).length = d := by simp [past]
  have ht : (past e t d).take m = List.replicate m true := by
    apply take_leading _ _ (by omega)
    intro i hi
    simpa [past] using ha i hi
  have hsplit : past e t d = List.replicate m true ++ (past e t d).drop m := by
    rw [← ht]
    exact (List.take_append_drop _ _).symm
  have hp := (past_p2_iff e t d).mpr h
  rw [hsplit] at hp
  have hb := leading_run_bound m _ hm hp
  rw [← hsplit, hlen] at hb
  exact hb

@[simp] theorem ones_replicate_S (m : Nat) : ones (List.replicate m false) = 0 := by
  induction m with
  | zero => simp [ones]
  | succ m ih => simp [List.replicate_succ, ones, ih]

@[simp] theorem positions_replicate_S (m : Nat) : positions (List.replicate m false) = 0 := by
  induction m with
  | zero => simp [positions]
  | succ m ih => simp [List.replicate_succ, positions, ih]

theorem not_p2_all_A (d : Nat) : ¬ P2 (List.replicate d true) := by
  intro h
  have hs := mass_eq (List.replicate d true)
  simp at hs
  have hd : d = 1 := by have := h.1; omega
  subst d
  have := h.2
  simp [moment, mass, sign] at this

def sharpFamily (m : Nat) : List Bool :=
  List.replicate m true ++ List.replicate (m-1) false ++ [true] ++
    List.replicate m false ++ List.replicate (m-1) true

theorem sharpFamily_length (m : Nat) (hm : 1 ≤ m) :
    (sharpFamily m).length = 4*m-1 := by
  simp [sharpFamily]
  omega

theorem sharpFamily_ones (m : Nat) (hm : 1 ≤ m) :
    ones (sharpFamily m) = 2*m := by
  simp [sharpFamily, ones_append, ones]
  omega

theorem sharpFamily_positions (m : Nat) (hm : 1 ≤ m) :
    positions (sharpFamily m) = (m : Int) * (4*m-1) := by
  have hp := positions_replicate_A m
  have hp1 := positions_replicate_A (m-1)
  have hsub : ((m-1 : Nat) : Int) = (m : Int)-1 := by omega
  simp only [hsub] at hp1
  simp only [sharpFamily, positions_append, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil, Int.natCast_add,
    ones_replicate_A, ones_replicate_S, positions_replicate_S, positions, ones,
    hsub]
  grind

theorem sharpFamily_p2 (m : Nat) (hm : 1 ≤ m) : P2 (sharpFamily m) := by
  have hc := sharpFamily_ones m hm
  have hl := sharpFamily_length m hm
  have hp := sharpFamily_positions m hm
  have hs := mass_eq (sharpFamily m)
  have ht := twice_moment (sharpFamily m)
  have hlen : ((sharpFamily m).length : Int) = 4*(m : Int)-1 := by omega
  constructor
  · omega
  · rw [hlen, hp] at ht
    grind

theorem sharpFamily_take_leading (m d : Nat) (hd : d ≤ m) :
    (sharpFamily m).take d = List.replicate d true := by
  have hs : sharpFamily m = List.replicate m true ++
      (List.replicate (m-1) false ++ [true] ++
        List.replicate m false ++ List.replicate (m-1) true) := by
    simp [sharpFamily, List.append_assoc]
  rw [hs, List.take_append_of_le_length (by simpa using hd)]
  simp [List.take_replicate, Nat.min_eq_left hd]

theorem leading_run_bound_of_take (w : List Bool) (m : Nat) (hm : 3 ≤ m)
    (ht : w.take m = List.replicate m true) (h : P2 w) : 4*m ≤ w.length+1 := by
  have hs : w = List.replicate m true ++ w.drop m := by
    rw [← ht]
    exact (List.take_append_drop _ _).symm
  rw [hs] at h ⊢
  exact leading_run_bound m _ hm h

/-- The sharp family has no shorter supply, for every m ≥ 3. -/
theorem sharpFamily_minimal (m d : Nat) (hm : 3 ≤ m) (hd : d < 4*m-1) :
    ¬ P2 ((sharpFamily m).take d) := by
  intro h
  by_cases hdm : d ≤ m
  · rw [sharpFamily_take_leading _ _ hdm] at h
    exact not_p2_all_A d h
  · have ht : ((sharpFamily m).take d).take m = List.replicate m true := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
      exact sharpFamily_take_leading m m (by omega)
    have hb := leading_run_bound_of_take _ m hm ht h
    simp only [List.length_take] at hb
    omega

/-- The lower bound is attained at arbitrarily long lags. -/
theorem sharpFamily_certificate (m : Nat) (hm : 3 ≤ m) :
    (sharpFamily m).length = 4*m-1 ∧
    (sharpFamily m).take m = List.replicate m true ∧
    P2 (sharpFamily m) ∧
    ∀ d, d < (sharpFamily m).length → ¬ P2 ((sharpFamily m).take d) := by
  refine ⟨sharpFamily_length m (by omega), sharpFamily_take_leading m m (by omega),
    sharpFamily_p2 m (by omega), ?_⟩
  intro d hd
  rw [sharpFamily_length m (by omega)] at hd
  exact sharpFamily_minimal m d hm hd

theorem p2_length_ge_three (w : List Bool) (h : P2 w) : 3 ≤ w.length := by
  have hc := p2_count_identities w h
  omega

theorem mass_replicate_A (k : Nat) : mass (List.replicate k true) = k := by
  have h := mass_eq (List.replicate k true)
  simp at h
  omega

theorem twice_moment_replicate_A (k : Nat) :
    2 * moment (List.replicate k true) = (k : Int) * (k+1) := by
  have hm := twice_moment (List.replicate k true)
  have hp := positions_replicate_A k
  simp at hm
  omega

/-- The extremal moment of a tail with signed mass -k. -/
theorem moment_upper_of_mass (w : List Bool) (k : Int) (hm : mass w = -k) :
    4 * moment w ≤ (w.length : Int) * w.length - 2 * w.length * k - k*k - 2*k := by
  have hp := positions_upper w
  have ht := twice_moment w
  have hs := mass_eq w
  have heq :
      (w.length : Int) * w.length - 2 * w.length * k - k*k - 2*k - 4 * moment w =
        4 * (ones w * (2 * (w.length : Int) - ones w + 1) - 2 * positions w) := by
    grind
  omega

/-- Uniform quadratic separation for nested P2 windows across k A steps. -/
theorem nested_supply_gap (w v : List Bool) (k : Nat) (hw : P2 w)
    (hnew : P2 (List.replicate k true ++ w ++ v)) :
    4 * (k : Int) * (w.length - 1) ≤
      ((k : Int) + v.length) * ((v.length : Int) - 3*k) := by
  have hs := hnew.1
  simp only [mass_append, mass_replicate_A, hw.1] at hs
  have hv : mass v = -(k : Int) := by omega
  have ht := hnew.2
  simp only [moment_append, List.length_append, List.length_replicate,
    Int.natCast_add, hw.1, hw.2, hv] at ht
  have hk := twice_moment_replicate_A k
  have hmoment : 2 * moment v = 2*(k : Int)*(w.length+k) - (k : Int)*(k+3) := by
    grind
  have hu := moment_upper_of_mass v (k : Int) hv
  have heq :
      (v.length : Int)*v.length - 2*v.length*k - (k : Int)*k - 2*k - 4*moment v =
        ((k : Int)+v.length)*((v.length : Int)-3*k) - 4*(k : Int)*(w.length-1) := by
    grind
  omega

theorem nested_supply_strict_gap (w v : List Bool) (k : Nat) (hk : 1 ≤ k)
    (hw : P2 w) (hnew : P2 (List.replicate k true ++ w ++ v)) :
    3*k < v.length := by
  have hg := nested_supply_gap w v k hw hnew
  have hd := p2_length_ge_three w hw
  have hpos : 0 < 4 * (k : Int) * (w.length - 1) :=
    Int.mul_pos (by omega) (by omega)
  by_cases hle : v.length ≤ 3*k
  · have hnonneg := Int.mul_nonneg
      (show 0 ≤ 3*(k : Int)-(v.length : Int) by omega)
      (show 0 ≤ (k : Int)+(v.length : Int) by omega)
    have heq : (3*(k : Int)-(v.length : Int))*((k : Int)+v.length) =
        -(((k : Int)+v.length)*((v.length : Int)-3*k)) := by grind
    omega
  · omega

theorem past_append (e : Int → Bool) (t : Int) (a b : Nat) :
    past e t (a+b) = past e t a ++ past e (t-a) b := by
  simp only [past, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  change e (t - ((a+i+1 : Nat) : Int)) = e (t-a-((i+1 : Nat) : Int))
  congr 1
  omega

theorem past_A_run (e : Int → Bool) (t : Int) (k : Nat)
    (ha : ∀ i, i < k → e (t+i) = true) :
    past e (t+k) k = List.replicate k true := by
  apply List.ext_getElem
  · simp [past]
  · intro i hi hj
    have hi' : i < k := by simpa using hj
    have hq : k-1-i < k := by omega
    have hv := ha (k-1-i) hq
    have heq : t + k - ((i : Int)+1) = t + ((k-1-i : Nat) : Int) := by omega
    simpa [past, heq] using hv

/-- A later supply window that contains the earlier one must grow by more
than four times the number of intervening A steps. -/
theorem stream_nested_supply_strict_gap (e : Int → Bool) (t : Int)
    (d d₂ k : Nat) (hk : 1 ≤ k) (hcontain : d+k ≤ d₂)
    (ha : ∀ i, i < k → e (t+i) = true)
    (hw : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t+k) d₂) : d+4*k < d₂ := by
  let ell := d₂-d-k
  have hell : d₂ = k+(d+ell) := by dsimp [ell]; omega
  have hp := (past_p2_iff e (t+k) d₂).mpr hnew
  rw [hell, past_append, past_A_run e t k ha] at hp
  have heq : t + (k : Int) - k = t := by omega
  rw [heq, past_append] at hp
  rw [← List.append_assoc] at hp
  have hgap := nested_supply_strict_gap (past e t d) (past e (t-d) ell) k hk
    ((past_p2_iff e t d).mpr hw) hp
  simp only [past, List.length_map, List.length_range] at hgap
  omega

/-- In an A run, a second sharp supply at the corresponding larger leading
run length is impossible. This is not a statement about non-nested lags. -/
theorem sharp_supply_no_second (e : Int → Bool) (t : Int) (m k : Nat)
    (hm : 3 ≤ m) (hk : 1 ≤ k)
    (ha : ∀ i, i < k → e (t+i) = true)
    (hw : ShortPeriodicSupply.P2 e t (4*m-1)) :
    ¬ ShortPeriodicSupply.P2 e (t+k) (4*(m+k)-1) := by
  intro hn
  have hg := stream_nested_supply_strict_gap e t (4*m-1) (4*(m+k)-1) k hk
    (by omega) ha hw hn
  omega

/-- A word whose A positions are close to their maximum must begin with S.
This is an extremal-position lemma, not an orbit potential. -/
theorem deficit_forces_S_prefix (w : List Bool) (k b : Nat)
    (hspace : (k : Int) + b + ones w ≤ w.length)
    (hdef : ones w * (2*(w.length : Int)-ones w+1) - 2*positions w ≤ 2*b) :
    w.take k = List.replicate k false := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    cases w with
    | nil => simp [ones] at hspace; omega
    | cons bit w =>
      cases bit with
      | false =>
        have hs : (k : Int)+b+ones w ≤ w.length := by
          simp [ones, List.length_cons] at hspace
          omega
        have heq : ones (false::w) *
            (2*((false::w).length : Int)-ones (false::w)+1) -
            2*positions (false::w) =
            ones w*(2*(w.length : Int)-ones w+1)-2*positions w := by
          simp [ones, positions, List.length_cons]
          grind
        rw [heq] at hdef
        simpa [List.replicate_succ] using congrArg (List.cons false) (ih w hs hdef)
      | true =>
        have hu := positions_upper w
        have heq : ones (true::w) *
            (2*((true::w).length : Int)-ones (true::w)+1) -
            2*positions (true::w) =
            ones w*(2*(w.length : Int)-ones w+1)-2*positions w +
              2*((w.length : Int)-ones w) := by
          simp [ones, positions, List.length_cons]
          grind
        rw [heq] at hdef
        simp [ones, List.length_cons] at hspace
        omega

/-- Every sharp window has an S block of length at least m-1 immediately
behind its leading A block. -/
theorem sharp_middle_S_block (m : Nat) (tail : List Bool) (hm : 3 ≤ m)
    (hlen : (List.replicate m true ++ tail).length = 4*m-1)
    (hp : P2 (List.replicate m true ++ tail)) :
    tail.take (m-1) = List.replicate (m-1) false := by
  have hc := p2_count_identities _ hp
  have hr := positions_replicate_A m
  have htlen : (tail.length : Int) = 3*(m : Int)-1 := by
    simp only [List.length_append, List.length_replicate] at hlen
    omega
  simp only [ones_append, ones_replicate_A, positions_append, List.length_append,
    List.length_replicate, Int.natCast_add] at hc
  have hones : ones tail = m := by omega
  have hdef : ones tail*(2*(tail.length : Int)-ones tail+1)-2*positions tail = 2*m := by
    grind
  apply deficit_forces_S_prefix tail (m-1) m
  · omega
  · omega

theorem p2_two_runs (a b : Nat) (h : P2 (List.replicate a true ++ List.replicate b false)) :
    a = 2 ∧ b = 1 := by
  have hc := p2_count_identities _ h
  have hp := positions_replicate_A a
  simp only [ones_append, ones_replicate_A, ones_replicate_S, positions_append,
    positions_replicate_S, List.length_append, List.length_replicate,
    Int.natCast_add] at hc
  have hpoly : (a : Int) * ((a : Int)-2) = 0 := by grind
  have ha0 : (a : Int) ≠ 0 := by omega
  have ha2 := (Int.mul_eq_zero.mp hpoly).resolve_left ha0
  omega

/-- The forced S block is about the actual past stream, not an unrelated word. -/
theorem stream_sharp_S_block (e : Int → Bool) (t : Int) (m : Nat) (hm : 3 ≤ m)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hp : ShortPeriodicSupply.P2 e t (4*m-1)) :
    ∀ i : Nat, i < m-1 → e (t-((m+1+i : Nat) : Int)) = false := by
  have ht : (past e t (4*m-1)).take m = List.replicate m true := by
    apply take_leading _ _ (by simp [past]; omega)
    intro i hi
    simpa [past] using ha i hi
  have hsplit : past e t (4*m-1) =
      List.replicate m true ++ (past e t (4*m-1)).drop m := by
    rw [← ht]
    exact (List.take_append_drop _ _).symm
  have hw := (past_p2_iff e t (4*m-1)).mpr hp
  rw [hsplit] at hw
  have hb := sharp_middle_S_block m _ hm (by rw [← hsplit]; simp [past]) hw
  intro i hi
  have hv := congrArg (fun w : List Bool => w[i]?) hb
  simpa [past, List.getElem?_take, hi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Int.add_assoc,
    show m+i < 4*m-1 by omega] using hv

theorem past_two_runs (e : Int → Bool) (q : Int) (L j d : Nat)
    (hj : 2 ≤ j) (hjL : j ≤ L) (hd : d ≤ L)
    (hs : ∀ i : Nat, i < L → e (q+1-i) = false)
    (ha : ∀ i : Nat, i < L → e (q+2+i) = true) :
    past e (q+j) d = List.replicate (min d (j-2)) true ++
      List.replicate (d-min d (j-2)) false := by
  apply List.ext_getElem
  · simp [past]; omega
  · intro i hi hi'
    have hid : i < d := by simpa [past] using hi
    by_cases hia : i < min d (j-2)
    · have hidx : j-3-i < L := by omega
      have he := ha (j-3-i) hidx
      have hpos : q+(j : Int)-((i : Int)+1) = q+2+(j-3-i : Nat) := by omega
      simpa [past, List.getElem_append, hia, hpos] using he
    · have hidx : i+2-j < L := by omega
      have he := hs (i+2-j) hidx
      have hpos : q+(j : Int)-((i : Int)+1) = q+1-(i+2-j : Nat) := by omega
      simpa [past, List.getElem_append, hia, hpos] using he

/-- In a long S-to-A transition, the only supplied A within L steps of
the penultimate S is the AAS contact, four steps after that S. -/
theorem protected_S_contact (e : Int → Bool) (q : Int) (L j d : Nat)
    (hj : 1 ≤ j) (hjL : j ≤ L) (hd : d ≤ L)
    (hs : ∀ i : Nat, i < L → e (q+1-i) = false)
    (ha : ∀ i : Nat, i < L → e (q+2+i) = true)
    (hcur : e (q+j) = true) (hp : ShortPeriodicSupply.P2 e (q+j) d) :
    j = 4 ∧ d = 3 := by
  have hj2 : 2 ≤ j := by
    by_cases hj1 : j = 1
    · subst j
      have he := hs 0 (by omega)
      simp at he
      simp [he] at hcur
    · omega
  have hw := (past_p2_iff e (q+j) d).mpr hp
  rw [past_two_runs e q L j d hj2 hjL hd hs ha] at hw
  have ht := p2_two_runs _ _ hw
  omega

/-- The penultimate S forced by a sufficiently long sharp window can meet
only the lag-3 short contact, whose usual charge is the following S. -/
theorem sharp_protected_contact (e : Int → Bool) (t : Int) (m L j d : Nat)
    (hm : 3 ≤ m) (hL : L+1 ≤ m)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hp : ShortPeriodicSupply.P2 e t (4*m-1))
    (hj : 1 ≤ j) (hjL : j ≤ L) (hd : d ≤ L)
    (hcur : e (t-m-2+j) = true)
    (hshort : ShortPeriodicSupply.P2 e (t-m-2+j) d) : j = 4 ∧ d = 3 := by
  apply protected_S_contact e (t-m-2) L j d hj hjL hd _ _ hcur hshort
  · intro i hi
    have hs := stream_sharp_S_block e t m hm ha hp i (by omega)
    have heq : t-(m : Int)-2+1-i = t-((m+1+i : Nat) : Int) := by omega
    rw [heq]
    exact hs
  · intro i hi
    have he := ha (m-i-1) (by omega)
    have heq : t-(m : Int)-2+2+i = t-((m-i-1+1 : Nat) : Int) := by omega
    rw [heq]
    exact he

/-- Any short charging rule of backward radius L which assigns lag 3 to
offset 3 avoids the penultimate S of a sharp window with m≥L+1. -/
theorem sharp_protected_charge (e : Int → Bool) (t u : Int) (m L d j : Nat)
    (hm : 3 ≤ m) (hL : L+1 ≤ m)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hp : ShortPeriodicSupply.P2 e t (4*m-1))
    (hj : 1 ≤ j) (hjL : j ≤ L) (hd : d ≤ L)
    (hcur : e u = true) (hshort : ShortPeriodicSupply.P2 e u d)
    (hlag3 : ShortPeriodicSupply.P2 e u 3 → j = 3) :
    u-j ≠ t-m-2 := by
  intro heq
  have hu : u = t-m-2+j := by omega
  have hcontact := sharp_protected_contact e t m L j d hm hL ha hp hj hjL hd
    (by rw [← hu]; exact hcur) (by rw [← hu]; exact hshort)
  obtain ⟨hj4, hd3⟩ := hcontact
  subst d
  have := hlag3 hshort
  omega

theorem sharp_charge_ordered_ne (e : Int → Bool) (t u : Int) (m n : Nat)
    (hm : 3 ≤ m) (hmn : m < n)
    (ha : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (ht : ShortPeriodicSupply.P2 e t (4*m-1))
    (hu : ShortPeriodicSupply.P2 e u (4*n-1)) :
    t-m-2 ≠ u-n-2 := by
  intro heq
  have htime : u = t+(n-m : Nat) := by omega
  have hrun : ∀ i, i < n-m → e (t+i) = true := by
    intro i hi
    have he := ha (n-m-i-1) (by omega)
    have hpos : u-((n-m-i-1+1 : Nat) : Int) = t+i := by omega
    rwa [hpos] at he
  have hno := sharp_supply_no_second e t m (n-m) hm (by omega) hrun ht
  have hsum : m+(n-m) = n := by omega
  rw [hsum, ← htime] at hno
  exact hno hu

/-- Equal penultimate-S charges force equal sharp-supply times. Periodicity
is deliberately absent; circular use first lifts equal phases to equal times. -/
theorem sharp_charge_injective (e : Int → Bool) (t u : Int) (m n : Nat)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (ht : ShortPeriodicSupply.P2 e t (4*m-1))
    (hu : ShortPeriodicSupply.P2 e u (4*n-1))
    (heq : t-m-2 = u-n-2) : t = u := by
  rcases Nat.lt_trichotomy m n with hlt | he | hgt
  · exact False.elim (sharp_charge_ordered_ne e t u m n hm hlt hau ht hu heq)
  · omega
  · exact False.elim (sharp_charge_ordered_ne e u t n m hn hgt hat hu ht heq.symm)

def nonnestedExample : List Bool :=
  (sharpFamily 4).drop 1 ++ List.replicate 4 true ++ [false, true] ++
    List.replicate 3 false

/-- Removing containment is false even with three leading A signs and
minimal old supply: one more A changes the minimum lag from 23 to 15. -/
theorem nonnested_lag_drop_certificate :
    nonnestedExample.length = 23 ∧
    nonnestedExample.take 3 = List.replicate 3 true ∧
    P2 nonnestedExample ∧
    (∀ d : Fin 23, ¬ P2 (nonnestedExample.take d.val)) ∧
    P2 ((true :: nonnestedExample).take 15) ∧
    (∀ d : Fin 15, ¬ P2 ((true :: nonnestedExample).take d.val)) := by
  unfold P2 mass
  decide

end Recaman.LeadingRunSupply
