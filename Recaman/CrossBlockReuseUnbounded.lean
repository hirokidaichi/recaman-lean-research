import Recaman.AdditionRankSlack

namespace Recaman.CrossBlockReuseUnbounded

open Recaman.SingleWindowEquality Recaman.AdditionRankSlack
open Recaman.ShortPeriodicSupply (sign)

/-! # Unbounded cross-block reuse of a lower-stage source bank

Refutes `H-20261126-01` (`2 * A_after_cut ≤ 3 * (F + O_c) - 3`) and every
constant-factor linear capacity `A_after_cut ≤ C * (F + O_c) + K` on the exact
multi-block staged grammar `U ++ S^m ++ V_1 ++ ... ++ V_R ++ AA`, for every
arbitrary original prehistory `U` (length `n`, origin kept at `0`, retaining
all old co-suppliers).

For `k ≥ 1`, set `H = 3 * k`, `a = k * (3 * k - 2)`, `bank = 3 * a + 2`,
`lift = a + 1`.  The single bank block
  `V₀ = stagedBlock (replicate (H - 2) 1 ++ [bank, 1, lift])`
followed by `R` copies of the balanced block
  `V = stagedBlock (replicate H 1 ++ [a])`
obeys `Fw(V) = 0` and `Ar(V) = |V| * (H - 1)` relative to cut height (zero shift
of the window invariant at source height `H - 1`).  Hence every stage-`H`
addition across all `R` copies of `V` (`R * a` additions total) is internally
supplied by an explicit peak of `V₀`'s stage-`(H - 2)` bank.
-/

/-! ## Exact staged-block word constructors (matching H-20261126-01) -/

def asRep : Nat → List Bool
  | 0 => []
  | m + 1 => [true, false] ++ asRep m

def stageWord (a : Nat) : List Bool :=
  asRep (a - 1) ++ [true]

def stagedBlock (stages : List Nat) : List Bool :=
  (stages.map stageWord).flatten ++ List.replicate stages.length false

def repeatWord : Nat → List Bool → List Bool
  | 0, _ => []
  | r + 1, w => w ++ repeatWord r w

def MatchesAt (f : Nat → Bool) (s : Nat) (w : List Bool) : Prop :=
  ∀ i, i < w.length → f (s + i) = w[i]!

/-- Internal supply after cut `c`: `q` is an addition with a `Win` source `u ≥ c`. -/
def InternalSupplied (f : Nat → Bool) (c q : Nat) : Prop :=
  f q = true ∧ ∃ u k, c ≤ u ∧ u + k = q ∧ Win f u k

/-- Exclusive-before-cut original supply: original `EndN f 0 q` with no internal supplier `u ≥ c`. -/
def ExclusiveOldSupplied (f : Nat → Bool) (c q : Nat) : Prop :=
  EndN f 0 q ∧ ¬ InternalSupplied f c q

noncomputable def internalSuppliedCount (f : Nat → Bool) (c len : Nat) : Nat :=
  cN (InternalSupplied f c) c len

noncomputable def exclusiveOldCount (f : Nat → Bool) (c len : Nat) : Nat :=
  cN (ExclusiveOldSupplied f c) c len

/-- Exact partition of post-cut additions into internal supply, exclusive-old supply,
and original free additions (retaining targets with both old and internal supply as internal). -/
theorem additions_partition_after_cut (f : Nat → Bool) (c len : Nat) :
    additions f c len =
      internalSuppliedCount f c len + (free f c len + exclusiveOldCount f c len) := by
  unfold additions internalSuppliedCount free exclusiveOldCount
  have h1 := cN_split (fun q => f q = true) (InternalSupplied f c) c len
  have hc1 : cN (fun q => f q = true ∧ InternalSupplied f c q) c len =
      cN (InternalSupplied f c) c len :=
    cN_congr _ _ c len (fun q _ _ => ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩)
  have h2 := cN_split (fun q => f q = true ∧ ¬ InternalSupplied f c q) (EndN f 0) c len
  have hc2 : cN (fun q => (f q = true ∧ ¬ InternalSupplied f c q) ∧ EndN f 0 q) c len =
      cN (ExclusiveOldSupplied f c) c len :=
    cN_congr _ _ c len (fun q _ _ => ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1⟩⟩)
  have hc3 : cN (fun q => (f q = true ∧ ¬ InternalSupplied f c q) ∧ ¬ EndN f 0 q) c len =
      cN (fun q => f q = true ∧ ¬ EndN f 0 q) c len := by
    apply cN_congr _ _ c len
    intro q _ _
    constructor
    · intro h; exact ⟨h.1.1, h.2⟩
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      rintro ⟨ha, u, k, _hcu, huk, hw⟩
      exact h.2 ⟨ha, u, k, Nat.zero_le u, huk, hw⟩
  omega

/-! ## Word length and `MatchesAt` decomposition helpers -/

@[simp] theorem asRep_length (m : Nat) : (asRep m).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [asRep, ih]; omega

@[simp] theorem stageWord_length (a : Nat) : (stageWord a).length = 2 * (a - 1) + 1 := by
  simp [stageWord]

@[simp] theorem repeatWord_length (r : Nat) (w : List Bool) :
    (repeatWord r w).length = r * w.length := by
  induction r with
  | zero => simp [repeatWord]
  | succ r ih => simp [repeatWord, ih, Nat.succ_mul]; omega

private theorem matchesAt_append {f : Nat → Bool} {s : Nat} {u v : List Bool}
    (h : MatchesAt f s (u ++ v)) :
    MatchesAt f s u ∧ MatchesAt f (s + u.length) v := by
  constructor
  · intro i hi
    have h' := h i (by simp; omega)
    have hget : (u ++ v)[i]! = u[i]! := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]
    rw [hget] at h'
    exact h'
  · intro i hi
    have h' := h (u.length + i) (by simp; omega)
    have hget : (u ++ v)[u.length + i]! = v[i]! := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right u.length i)]
    rw [hget] at h'
    simpa [Nat.add_assoc] using h'

private theorem matchesAt_replicate {f : Nat → Bool} {s p : Nat} {b : Bool}
    (h : MatchesAt f s (List.replicate p b)) :
    ∀ i, i < p → f (s + i) = b := by
  intro i hi
  have h' := h i (by simp [hi])
  have hget : (List.replicate p b)[i]! = b := by
    simp [hi]
  rw [hget] at h'
  exact h'

private theorem matchesAt_asRep {f : Nat → Bool} {s m : Nat}
    (h : MatchesAt f s (asRep m)) :
    ∀ i, i < m → f (s + 2 * i) = true ∧ f (s + 2 * i + 1) = false := by
  induction m generalizing s with
  | zero => intro i hi; omega
  | succ m ih =>
      have h' : MatchesAt f s ([true, false] ++ asRep m) := h
      obtain ⟨h1, h2⟩ := matchesAt_append h'
      intro i hi
      cases i with
      | zero =>
          exact ⟨by simpa using h1 0 (by decide), by simpa using h1 1 (by decide)⟩
      | succ i =>
          have ih' := ih h2 i (by omega)
          simpa [show s + 2 + 2 * i = s + 2 * (i + 1) by omega,
                 show s + 2 + 2 * i + 1 = s + 2 * (i + 1) + 1 by omega] using ih'

private theorem matchesAt_singleton {f : Nat → Bool} {s : Nat} {b : Bool}
    (h : MatchesAt f s [b]) : f s = b := by
  simpa using h 0 (by simp)

private theorem matchesAt_repeat_elem {f : Nat → Bool} {s R : Nat} {w : List Bool}
    (h : MatchesAt f s (repeatWord R w)) :
    ∀ r, r < R → MatchesAt f (s + r * w.length) w := by
  induction R generalizing s with
  | zero => intro r hr; omega
  | succ R ih =>
      obtain ⟨h1, h2⟩ := matchesAt_append h
      intro r hr
      cases r with
      | zero => simpa using h1
      | succ r =>
          have ih' := ih h2 r (by omega)
          have heq : s + w.length + r * w.length = s + (r + 1) * w.length := by
            rw [Nat.succ_mul]; omega
          simpa [heq] using ih'

private theorem flatten_map_replicate_one (p : Nat) :
    ((List.replicate p 1).map stageWord).flatten = List.replicate p true := by
  induction p with
  | zero => rfl
  | succ p ih =>
      simp [List.replicate_succ, stageWord, asRep]

/-! ## Walk and area algebra for `Ar` and primitive segments -/

theorem Ar_add (f : Nat → Bool) (t m : Nat) :
    ∀ n : Nat, Ar f t (m + n) =
      Ar f t m + Ar f (t + m) n + (n : Int) * (Fw f (t + m) - Fw f t)
  | 0 => by simp [Ar]
  | n + 1 => by
      have ih := Ar_add f t m n
      rw [show m + (n + 1) = (m + n) + 1 from rfl, Ar_succ, Ar_succ, ih]
      have hidx : t + (m + n) + 1 = t + m + n + 1 := by omega
      rw [hidx]
      simp only [Int.natCast_add, Int.natCast_one]
      grind only

private theorem fw_ar_allA (f : Nat → Bool) (t : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (t + i) = true) →
      Fw f (t + p) = Fw f t + (p : Int) ∧
      2 * Ar f t p = (p : Int) * ((p : Int) + 1)
  | 0, _ => by simp [Ar]
  | p + 1, h => by
      obtain ⟨hF, hA⟩ := fw_ar_allA f t p (fun i hi => h i (by omega))
      have hp : f (t + p) = true := h p (by omega)
      have hFp1 : Fw f (t + (p + 1)) = Fw f t + ((p + 1 : Nat) : Int) := by
        rw [show t + (p + 1) = t + p + 1 from rfl, Fw_succ, hp, hF]
        simp [sign]; omega
      refine ⟨hFp1, ?_⟩
      rw [Ar_succ, show t + p + 1 = t + (p + 1) from rfl, hFp1]
      simp only [Int.natCast_add, Int.natCast_one] at hA ⊢
      grind only

private theorem fw_ar_allS (f : Nat → Bool) (t : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (t + i) = false) →
      Fw f (t + p) = Fw f t - (p : Int) ∧
      2 * Ar f t p = -((p : Int) * ((p : Int) + 1))
  | 0, _ => by simp [Ar]
  | p + 1, h => by
      obtain ⟨hF, hA⟩ := fw_ar_allS f t p (fun i hi => h i (by omega))
      have hp : f (t + p) = false := h p (by omega)
      have hFp1 : Fw f (t + (p + 1)) = Fw f t - ((p + 1 : Nat) : Int) := by
        rw [show t + (p + 1) = t + p + 1 from rfl, Fw_succ, hp, hF]
        simp [sign]; omega
      refine ⟨hFp1, ?_⟩
      rw [Ar_succ, show t + p + 1 = t + (p + 1) from rfl, hFp1]
      simp only [Int.natCast_add, Int.natCast_one] at hA ⊢
      grind only

private theorem fw_ar_as (f : Nat → Bool) (t : Nat) :
    ∀ m : Nat, (∀ i, i < m → f (t + 2 * i) = true ∧ f (t + 2 * i + 1) = false) →
      Fw f (t + 2 * m) = Fw f t ∧ Ar f t (2 * m) = (m : Int)
  | 0, _ => by simp [Ar]
  | m + 1, h => by
      obtain ⟨hF, hA⟩ := fw_ar_as f t m (fun i hi => h i (by omega))
      obtain ⟨ha, hs⟩ := h m (by omega)
      have hF1 : Fw f (t + 2 * m + 1) = Fw f t + 1 := by
        rw [Fw_succ, ha, hF]; simp [sign]
      have hF2 : Fw f (t + 2 * (m + 1)) = Fw f t := by
        rw [show t + 2 * (m + 1) = t + 2 * m + 1 + 1 by omega, Fw_succ, hs, hF1]
        simp [sign]; omega
      refine ⟨hF2, ?_⟩
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Ar_succ, Ar_succ,
          show t + (2 * m + 1) + 1 = t + 2 * (m + 1) by omega, hF1, hF2, hA]
      simp only [Int.natCast_add, Int.natCast_one]
      omega

private theorem fw_ar_sa (f : Nat → Bool) (t : Nat) :
    ∀ m : Nat, (∀ i, i < m → f (t + 2 * i) = false ∧ f (t + 2 * i + 1) = true) →
      Fw f (t + 2 * m) = Fw f t ∧ Ar f t (2 * m) = -(m : Int)
  | 0, _ => by simp [Ar]
  | m + 1, h => by
      obtain ⟨hF, hA⟩ := fw_ar_sa f t m (fun i hi => h i (by omega))
      obtain ⟨hs, ha⟩ := h m (by omega)
      have hF1 : Fw f (t + 2 * m + 1) = Fw f t - 1 := by
        rw [Fw_succ, hs, hF]; simp [sign]; omega
      have hF2 : Fw f (t + 2 * (m + 1)) = Fw f t := by
        rw [show t + 2 * (m + 1) = t + 2 * m + 1 + 1 by omega, Fw_succ, ha, hF1]
        simp [sign]
      refine ⟨hF2, ?_⟩
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Ar_succ, Ar_succ,
          show t + (2 * m + 1) + 1 = t + 2 * (m + 1) by omega, hF1, hF2, hA]
      simp only [Int.natCast_add, Int.natCast_one]
      omega

private theorem count_allA_additions (f : Nat → Bool) (s : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (s + i) = true) → additions f s p = p
  | 0, _ => rfl
  | p + 1, h => by
      unfold additions
      rw [cN_succ_pos (fun x => f x = true) s p (h p (by omega))]
      have ih := count_allA_additions f s p (fun i hi => h i (by omega))
      unfold additions at ih
      omega

private theorem count_allS_additions (f : Nat → Bool) (s : Nat) :
    ∀ p : Nat, (∀ i, i < p → f (s + i) = false) → additions f s p = 0
  | 0, _ => rfl
  | p + 1, h => by
      unfold additions
      rw [cN_succ_neg (fun x => f x = true) s p (by rw [h p (by omega)]; decide)]
      exact count_allS_additions f s p (fun i hi => h i (by omega))

private theorem count_as_additions (f : Nat → Bool) (s : Nat) :
    ∀ m : Nat, (∀ i, i < m → f (s + 2 * i) = true ∧ f (s + 2 * i + 1) = false) →
      additions f s (2 * m) = m
  | 0, _ => rfl
  | m + 1, h => by
      obtain ⟨ha, hs⟩ := h m (by omega)
      have ih := count_as_additions f s m (fun i hi => h i (by omega))
      unfold additions at ih ⊢
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
          cN_succ_neg (fun x => f x = true) s (2 * m + 1) (by rw [show s + (2 * m + 1) = s + 2 * m + 1 by omega, hs]; decide),
          cN_succ_pos (fun x => f x = true) s (2 * m) ha, ih]

private theorem count_evens_ge (P : Nat → Prop) (s : Nat) :
    ∀ m : Nat, (∀ j, j < m → P (s + 2 * j)) → m ≤ cN P s (2 * m)
  | 0, _ => Nat.zero_le _
  | m + 1, h => by
      have ih := count_evens_ge P s m (fun j hj => h j (by omega))
      have hm := h m (by omega)
      have h1 : cN P s (2 * m + 1) = cN P s (2 * m) + 1 := cN_succ_pos P s (2 * m) hm
      have h2 : cN P s (2 * m + 1) ≤ cN P s ((2 * m + 1) + 1) := by
        by_cases hp : P (s + (2 * m + 1))
        · rw [cN_succ_pos P s (2 * m + 1) hp]; omega
        · rw [cN_succ_neg P s (2 * m + 1) hp]; exact Nat.le_refl _
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
      omega

/-! ## Family A parameters and staged blocks -/

def famH (k : Nat) : Nat := 3 * k
def famA (k : Nat) : Nat := k * (3 * k - 2)
def famBank (k : Nat) : Nat := 3 * famA k + 2
def famLift (k : Nat) : Nat := famA k + 1

def bankStages (k : Nat) : List Nat :=
  List.replicate (famH k - 2) 1 ++ [famBank k, 1, famLift k]

def repeatStages (k : Nat) : List Nat :=
  List.replicate (famH k) 1 ++ [famA k]

def bankBlock (k : Nat) : List Bool := stagedBlock (bankStages k)
def repeatBlock (k : Nat) : List Bool := stagedBlock (repeatStages k)

def familyTail (k R : Nat) : List Bool :=
  bankBlock k ++ repeatWord R (repeatBlock k) ++ [true, true]

/-- Full post-prehistory word `S^(H+2) ++ V₀ ++ V^R ++ AA` in the exact H-20261126-01 grammar. -/
def familyWord (k R : Nat) : List Bool :=
  List.replicate (famH k + 2) false ++ familyTail k R

theorem bankBlock_eq (k : Nat) (hk : 1 ≤ k) :
    bankBlock k =
      List.replicate (famH k - 2) true ++
      asRep (famBank k - 1) ++ [true] ++ [true] ++
      asRep (famLift k - 1) ++ [true] ++
      List.replicate (famH k + 1) false := by
  unfold bankBlock stagedBlock bankStages
  have hlen : (List.replicate (famH k - 2) 1 ++ [famBank k, 1, famLift k]).length = famH k + 1 := by
    simp [famH]; omega
  rw [hlen, List.map_append, List.flatten_append, flatten_map_replicate_one]
  simp [stageWord, asRep, List.append_assoc]

theorem repeatBlock_eq (k : Nat) :
    repeatBlock k =
      List.replicate (famH k) true ++
      asRep (famA k - 1) ++ [true] ++
      List.replicate (famH k + 1) false := by
  unfold repeatBlock stagedBlock repeatStages
  have hlen : (List.replicate (famH k) 1 ++ [famA k]).length = famH k + 1 := by
    simp
  rw [hlen, List.map_append, List.flatten_append, flatten_map_replicate_one]
  simp [stageWord, List.append_assoc]

theorem bankBlock_length (k : Nat) (hk : 1 ≤ k) :
    (bankBlock k).length = 2 * famH k + 2 * famBank k + 2 * famLift k - 2 := by
  rw [bankBlock_eq k hk]
  have hH : 3 ≤ famH k := by unfold famH; omega
  have hB : 1 ≤ famBank k := by unfold famBank; omega
  have hL : 1 ≤ famLift k := by unfold famLift; omega
  simp only [List.length_append, List.length_replicate, asRep_length, List.length_singleton]
  omega

theorem repeatBlock_length (k : Nat) (hk : 1 ≤ k) :
    (repeatBlock k).length = 2 * famH k + 2 * famA k := by
  rw [repeatBlock_eq k]
  have hA : 1 ≤ famA k := by
    unfold famA
    have : 1 ≤ 3 * k - 2 := by omega
    exact Nat.mul_pos hk this
  simp only [List.length_append, List.length_replicate, asRep_length, List.length_singleton]
  omega

/-! ## Core invariance of `repeatBlock k`: mass `0` and zero `Φ_{H-1}` shift -/

private theorem repeatBlock_fw_ar (f : Nat → Bool) (s k : Nat) (hk : 1 ≤ k)
    (hmatch : MatchesAt f s (repeatBlock k)) :
    Fw f (s + (repeatBlock k).length) = Fw f s ∧
    Ar f s (repeatBlock k).length =
      ((repeatBlock k).length : Int) * ((famH k : Int) - 1) ∧
    additions f s (repeatBlock k).length = famH k + famA k := by
  have hlen := repeatBlock_length k hk
  have hApos : 1 ≤ famA k := by
    unfold famA; exact Nat.mul_pos hk (by omega)
  rw [repeatBlock_eq k] at hmatch
  -- Split into A^H, (AS)^(a-1), [A], S^(H+1)
  have hmatch' : MatchesAt f s
      (List.replicate (famH k) true ++
        (asRep (famA k - 1) ++ ([true] ++ List.replicate (famH k + 1) false))) := by
    simpa [List.append_assoc] using hmatch
  obtain ⟨h1, hr1⟩ := matchesAt_append hmatch'
  obtain ⟨h2, hr2⟩ := matchesAt_append hr1
  obtain ⟨h3, h4⟩ := matchesAt_append hr2
  simp only [List.length_replicate, asRep_length, List.length_singleton] at hr1 hr2 h2 h3 h4
  have hA_run := matchesAt_replicate h1
  have hAS_run := matchesAt_asRep h2
  have hA_end := matchesAt_singleton h3
  have hS_run := matchesAt_replicate h4
  -- Fw & Ar of each piece
  obtain ⟨hF1, hAr1⟩ := fw_ar_allA f s (famH k) hA_run
  obtain ⟨hF2, hAr2⟩ := fw_ar_as f (s + famH k) (famA k - 1) hAS_run
  have hF3 : Fw f (s + famH k + 2 * (famA k - 1) + 1) = Fw f s + (famH k : Int) + 1 := by
    rw [Fw_succ, hA_end, hF2, hF1]; simp [sign]
  have hAr3 : Ar f (s + famH k + 2 * (famA k - 1)) 1 = 1 := by
    simp [Ar, Fw_succ, hA_end, sign]
    omega
  obtain ⟨hF4, hAr4⟩ := fw_ar_allS f (s + famH k + 2 * (famA k - 1) + 1) (famH k + 1) hS_run
  -- Combine lengths and Fw
  have htot : (repeatBlock k).length =
      famH k + (2 * (famA k - 1) + (1 + (famH k + 1))) := by omega
  have hFw_end : Fw f (s + (repeatBlock k).length) = Fw f s := by
    rw [htot]
    have hidx : s + (famH k + (2 * (famA k - 1) + (1 + (famH k + 1)))) =
        s + famH k + 2 * (famA k - 1) + 1 + (famH k + 1) := by omega
    rw [hidx, hF4, hF3]
    simp only [Int.natCast_add, Int.natCast_one]; omega
  -- Combine Ar via Ar_add
  have hAr_34 := Ar_add f (s + famH k + 2 * (famA k - 1)) 1 (famH k + 1)
  have hAr_234 := Ar_add f (s + famH k) (2 * (famA k - 1)) (1 + (famH k + 1))
  have hAr_all := Ar_add f s (famH k) (2 * (famA k - 1) + (1 + (famH k + 1)))
  -- Key algebraic identity: 3 * famA k = famH k * (famH k - 2)
  have hkey : 3 * (famA k : Int) = (famH k : Int) * ((famH k : Int) - 2) := by
    unfold famA famH
    have hk3 : ((3 * k - 2 : Nat) : Int) = 3 * (k : Int) - 2 := by omega
    rw [Int.natCast_mul, hk3]
    push_cast
    grind only
  have hAr_eq : Ar f s (repeatBlock k).length =
      ((repeatBlock k).length : Int) * ((famH k : Int) - 1) := by
    have hF3' : Fw f (s + famH k + 2 * (famA k - 1) + 1) -
        Fw f (s + famH k + 2 * (famA k - 1)) = 1 := by
      rw [hF3, hF2, hF1]; omega
    have hA_cast : ((famA k - 1 : Nat) : Int) = (famA k : Int) - 1 := by
      omega
    have hlen_cast : ((repeatBlock k).length : Int) = 2 * (famH k : Int) + 2 * (famA k : Int) := by
      rw [hlen]; push_cast; omega
    have hAr_body : Ar f s (famH k + (2 * (famA k - 1) + (1 + (famH k + 1)))) =
        (2 * (famH k : Int) + 2 * (famA k : Int)) * ((famH k : Int) - 1) := by
      rw [hAr_all, hAr_234, hAr_34, hAr2, hAr3, hF3', hF2, hF1]
      have h2 : 2 * (Ar f s (famH k) +
          (((famA k - 1 : Nat) : Int) +
            (1 + Ar f (s + famH k + 2 * (famA k - 1) + 1) (famH k + 1) +
              ((famH k + 1 : Nat) : Int) * 1) +
            ((1 + (famH k + 1) : Nat) : Int) * (Fw f s + (famH k : Int) - (Fw f s + (famH k : Int)))) +
          ((2 * (famA k - 1) + (1 + (famH k + 1)) : Nat) : Int) * (Fw f s + (famH k : Int) - Fw f s)) =
          2 * ((2 * (famH k : Int) + 2 * (famA k : Int)) * ((famH k : Int) - 1)) := by
        push_cast at hAr4 hAr1 ⊢
        grind only
      grind only
    rw [hlen_cast, htot]
    exact hAr_body
  -- Additions count in repeatBlock k
  have hadd : additions f s (repeatBlock k).length = famH k + famA k := by
    rw [htot]
    unfold additions
    rw [cN_add, cN_add, cN_add]
    have c1 := count_allA_additions f s (famH k) hA_run
    have c2 := count_as_additions f (s + famH k) (famA k - 1) hAS_run
    have c3 : cN (fun x => f x = true) (s + famH k + 2 * (famA k - 1)) 1 = 1 := by
      have h := cN_succ_pos (fun x => f x = true) (s + famH k + 2 * (famA k - 1)) 0 (by simpa using hA_end)
      simpa [cN] using h
    have c4 := count_allS_additions f (s + famH k + 2 * (famA k - 1) + 1) (famH k + 1) hS_run
    unfold additions at c1 c2 c4
    rw [c1, c2, c3, c4]
    omega
  exact ⟨hFw_end, hAr_eq, hadd⟩

/-- Repeated copies of `repeatBlock k` preserve `Fw` and add `r * |V| * (H - 1)` to `Ar`. -/
private theorem repeatWord_fw_ar (f : Nat → Bool) (s k : Nat) (hk : 1 ≤ k) :
    ∀ r : Nat, MatchesAt f s (repeatWord r (repeatBlock k)) →
      Fw f (s + r * (repeatBlock k).length) = Fw f s ∧
      Ar f s (r * (repeatBlock k).length) =
        ((r * (repeatBlock k).length : Nat) : Int) * ((famH k : Int) - 1) ∧
      additions f s (r * (repeatBlock k).length) = r * (famH k + famA k)
  | 0, _ => by simp [Ar, additions, cN]
  | r + 1, hm => by
      obtain ⟨hfirst, hrest⟩ := matchesAt_append hm
      obtain ⟨hF1, hAr1, hA1⟩ := repeatBlock_fw_ar f s k hk hfirst
      obtain ⟨hFr, hArr, hAr_add_r⟩ := repeatWord_fw_ar f (s + (repeatBlock k).length) k hk r hrest
      have hmul : (r + 1) * (repeatBlock k).length =
          (repeatBlock k).length + r * (repeatBlock k).length := by
        rw [Nat.succ_mul]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hmul, ← Nat.add_assoc, hFr, hF1]
      · rw [hmul, Ar_add, hAr1, hArr, hF1]
        push_cast; grind only
      · rw [hmul]
        unfold additions at hA1 hAr_add_r ⊢
        rw [cN_add, hA1, hAr_add_r, Nat.succ_mul]; omega

/-! ## Explicit internal supplier from `bankBlock k` to every copy `r < R` and stage-`H` index `j < a` -/

/-- Exact supplier clock in `bankBlock k` (starting at `c`) for stage-`H` target index `j < famA k`. -/
def bankSupplierClock (c k j : Nat) : Nat :=
  c + (famH k - 2) + 2 * (3 * (famA k - 1 - j)) + 1

/-- Exact target clock in copy `r < R` of `repeatBlock k` (after `bankBlock k`) for index `j < famA k`. -/
def repeatTargetClock (c k r j : Nat) : Nat :=
  c + (bankBlock k).length + r * (repeatBlock k).length + famH k + 2 * j

private theorem bank_to_copy_zero_win (f : Nat → Bool) (c k R r j : Nat) (hk : 1 ≤ k)
    (hr : r < R) (hj : j < famA k)
    (hmatch : MatchesAt f c (familyTail k R)) :
    InternalSupplied f c (repeatTargetClock c k r j) := by
  have hH3 : 3 ≤ famH k := by unfold famH; omega
  have hApos : 1 ≤ famA k := by unfold famA; exact Nat.mul_pos hk (by omega)
  have hBlen := bankBlock_length k hk
  have hVlen := repeatBlock_length k hk
  -- Split familyTail into bankBlock, repeatWord R (repeatBlock k), [true, true]
  have hmatch' : MatchesAt f c (bankBlock k ++ (repeatWord R (repeatBlock k) ++ [true, true])) := by
    simpa [familyTail, List.append_assoc] using hmatch
  obtain ⟨hBank, hAfterBank⟩ := matchesAt_append hmatch'
  obtain ⟨hRep, _hAA⟩ := matchesAt_append hAfterBank
  -- Split bankBlock into A^(H-2), (AS)^(bank-1), [A], [A], (AS)^(lift-1), [A], S^(H+1)
  rw [bankBlock_eq k hk] at hBank
  have hBank' : MatchesAt f c
      (List.replicate (famH k - 2) true ++
        (asRep (famBank k - 1) ++
          ([true] ++ ([true] ++ (asRep (famLift k - 1) ++
            ([true] ++ List.replicate (famH k + 1) false)))))) := by
    simpa [List.append_assoc] using hBank
  obtain ⟨hb1, hbr1⟩ := matchesAt_append hBank'
  obtain ⟨hb2, hbr2⟩ := matchesAt_append hbr1
  obtain ⟨hb3, hbr3⟩ := matchesAt_append hbr2
  obtain ⟨hb4, hbr4⟩ := matchesAt_append hbr3
  obtain ⟨hb5, hbr5⟩ := matchesAt_append hbr4
  obtain ⟨hb6, hb7⟩ := matchesAt_append hbr5
  simp only [List.length_replicate, asRep_length, List.length_singleton] at hbr1 hbr2 hbr3 hbr4 hbr5 hb2 hb3 hb4 hb5 hb6 hb7
  have hbA1 := matchesAt_replicate hb1
  have hbAS := matchesAt_asRep hb2
  have hbPeakLast := matchesAt_singleton hb3
  have hbStageH1 := matchesAt_singleton hb4
  have hbLiftAS := matchesAt_asRep hb5
  have hbLiftEnd := matchesAt_singleton hb6
  have hbDescS := matchesAt_replicate hb7
  -- Supplier peak index i = 3 * (a - 1 - j), distance to last bank peak d = 4 + 3 * j
  let i := 3 * (famA k - 1 - j)
  let d := 4 + 3 * j
  have hi_lt : i < famBank k - 1 := by
    unfold famBank; omega
  have hid : i + d = famBank k - 1 := by
    unfold famBank; omega
  let u := bankSupplierClock c k j
  have hu_def : u = c + (famH k - 2) + 2 * i + 1 := rfl
  -- Compute Fw f u = Fw f c + (H - 1)
  obtain ⟨hFb1, _⟩ := fw_ar_allA f c (famH k - 2) hbA1
  obtain ⟨hFbASi, _⟩ := fw_ar_as f (c + (famH k - 2)) i (fun m hm => hbAS m (by omega))
  have hf_ui : f (c + (famH k - 2) + 2 * i) = true := (hbAS i hi_lt).1
  have hFw_u : Fw f u = Fw f c + (famH k : Int) - 1 := by
    rw [hu_def, Fw_succ, hf_ui, hFbASi, hFb1]
    simp [sign]; omega
  -- Segment 1 after u: (SA)^d takes u to u + 2*d = c + (H-2) + 2*(bank-1) + 1 (last peak of stage H-2!)
  have hSA_run : ∀ m, m < d → f (u + 2 * m) = false ∧ f (u + 2 * m + 1) = true := by
    intro m hm
    have hm1 : i + m < famBank k - 1 := by omega
    have hs := (hbAS (i + m) hm1).2
    have hidx1 : u + 2 * m = c + (famH k - 2) + 2 * (i + m) + 1 := by omega
    rw [hidx1]
    refine ⟨hs, ?_⟩
    by_cases hlast : i + m + 1 < famBank k - 1
    · have ha := (hbAS (i + m + 1) hlast).1
      have hidx2 : c + (famH k - 2) + 2 * (i + m) + 1 + 1 =
          c + (famH k - 2) + 2 * (i + m + 1) := by omega
      rw [hidx2]; exact ha
    · have hidx2 : c + (famH k - 2) + 2 * (i + m) + 1 + 1 =
          c + (famH k - 2) + 2 * (famBank k - 1) := by omega
      rw [hidx2]; exact hbPeakLast
  obtain ⟨hF_s1, hAr_s1⟩ := fw_ar_sa f u d hSA_run
  -- Let p1 = u + 2*d (last peak of stage H-2, right before stage H-1's single A)
  let p1 := u + 2 * d
  have hp1_eq : p1 = c + (famH k - 2) + 2 * (famBank k - 1) + 1 := by omega
  -- Segment 2: [A] at p1 (stage H-1)
  have hf_p1 : f p1 = true := by rw [hp1_eq]; exact hbStageH1
  have hF_s2 : Fw f (p1 + 1) = Fw f u + 1 := by
    rw [Fw_succ, hf_p1, hF_s1]; simp [sign]
  have hAr_s2 : Ar f p1 1 = 1 := by simp [Ar, Fw_succ, hf_p1, sign]; omega
  -- Segment 3: (AS)^(lift - 1) starting at p1 + 1
  have hp1_shift : p1 + 1 = c + (famH k - 2) + 2 * (famBank k - 1) + 1 + 1 := by omega
  obtain ⟨hF_s3, hAr_s3⟩ := fw_ar_as f (p1 + 1) (famLift k - 1) (by rw [hp1_shift]; exact hbLiftAS)
  -- Segment 4: [A] at p2 = p1 + 1 + 2*(lift - 1)
  let p2 := p1 + 1 + 2 * (famLift k - 1)
  have hp2_eq : p2 = c + (famH k - 2) + 2 * (famBank k - 1) + 1 + 1 + 2 * (famLift k - 1) := by omega
  have hf_p2 : f p2 = true := by rw [hp2_eq]; exact hbLiftEnd
  have hF_s4 : Fw f (p2 + 1) = Fw f u + 2 := by
    rw [Fw_succ, hf_p2]; dsimp [p2]; rw [hF_s3, hF_s2]; simp [sign]; omega
  have hAr_s4 : Ar f p2 1 = 1 := by simp [Ar, Fw_succ, hf_p2, sign]; omega
  -- Segment 5: S^(H + 1) starting at p2 + 1, reaching c + (bankBlock k).length!
  have hp2_shift : p2 + 1 =
      c + (famH k - 2) + 2 * (famBank k - 1) + 1 + 1 + 2 * (famLift k - 1) + 1 := by omega
  obtain ⟨hF_s5, hAr_s5⟩ := fw_ar_allS f (p2 + 1) (famH k + 1) (by rw [hp2_shift]; exact hbDescS)
  have hend_bank : p2 + 1 + (famH k + 1) = c + (bankBlock k).length := by
    unfold famBank famLift at *; omega
  have hFw_endBank : Fw f (c + (bankBlock k).length) = Fw f c := by
    rw [← hend_bank, hF_s5, hF_s4, hFw_u]
    push_cast; omega
  -- Compute 2 * Ar f u (c + bankBlock.length - u)
  let len_u_to_bank := 2 * d + (1 + (2 * (famLift k - 1) + (1 + (famH k + 1))))
  have hlen_ub : u + len_u_to_bank = c + (bankBlock k).length := by
    unfold famBank famLift at *; omega
  have hkey : 3 * (famA k : Int) = (famH k : Int) * ((famH k : Int) - 2) := by
    unfold famA famH
    have hk3 : ((3 * k - 2 : Nat) : Int) = 3 * (k : Int) - 2 := by omega
    rw [Int.natCast_mul, hk3]
    push_cast
    grind only
  have h2Ar_ub : 2 * Ar f u len_u_to_bank =
      -2 * (d : Int) + (famH k : Int) * (famH k : Int) - 3 * (famH k : Int) + 8 := by
    dsimp only [len_u_to_bank]
    rw [Ar_add, Ar_add, Ar_add, Ar_add]
    have e1 : u + 2 * d = p1 := rfl
    have e2 : p1 + 1 + 2 * (famLift k - 1) = p2 := rfl
    rw [e1, hAr_s1, hF_s1, hAr_s2, hF_s2, hAr_s3, e2, hF_s3, hF_s2, hAr_s4, hF_s4]
    have hL_cast : ((famLift k - 1 : Nat) : Int) = (famA k : Int) := by
      unfold famLift; omega
    push_cast at hAr_s5 ⊢
    grind only
  -- Now cross r full copies of repeatBlock k starting at s0 = c + bankBlock.length!
  let s0 := c + (bankBlock k).length
  have hRep_prefix : MatchesAt f s0 (repeatWord r (repeatBlock k)) := by
    -- split repeatWord R = repeatWord r ++ repeatWord (R - r)
    have hsplit : ∀ a b (w : List Bool), repeatWord (a + b) w = repeatWord a w ++ repeatWord b w := by
      intro a b w
      induction a with
      | zero => simp [repeatWord]
      | succ a ih => rw [Nat.succ_add]; simp [repeatWord, ih, List.append_assoc]
    have hm' : MatchesAt f s0 (repeatWord r (repeatBlock k) ++ repeatWord (R - r) (repeatBlock k)) := by
      rw [← hsplit, Nat.add_sub_cancel' (Nat.le_of_lt hr)]
      exact hRep
    exact (matchesAt_append hm').1
  obtain ⟨hF_rep, hAr_rep, _⟩ := repeatWord_fw_ar f s0 k hk r hRep_prefix
  -- Now inside copy r (starting at sr = s0 + r * repeatBlock.length), match repeatBlock k!
  let sr := s0 + r * (repeatBlock k).length
  have hCopy_r : MatchesAt f sr (repeatBlock k) := matchesAt_repeat_elem hRep r hr
  rw [repeatBlock_eq k] at hCopy_r
  have hCopy_r' : MatchesAt f sr
      (List.replicate (famH k) true ++
        (asRep (famA k - 1) ++ ([true] ++ List.replicate (famH k + 1) false))) := by
    simpa [List.append_assoc] using hCopy_r
  obtain ⟨hc1, hcr1⟩ := matchesAt_append hCopy_r'
  obtain ⟨hc2, hcr2⟩ := matchesAt_append hcr1
  obtain ⟨hc3, _hc4⟩ := matchesAt_append hcr2
  simp only [List.length_replicate, asRep_length] at hcr1 hcr2 hc2 hc3
  have hcA := matchesAt_replicate hc1
  have hcAS := matchesAt_asRep hc2
  have hcAend := matchesAt_singleton hc3
  obtain ⟨hF_cA, hAr_cA⟩ := fw_ar_allA f sr (famH k) hcA
  obtain ⟨hF_cAS, hAr_cAS⟩ := fw_ar_as f (sr + famH k) j (fun m hm => hcAS m (by omega))
  -- Verify f (repeatTargetClock c k r j) = true
  have hTarget_A : f (repeatTargetClock c k r j) = true := by
    show f (sr + famH k + 2 * j) = true
    by_cases hjlast : j < famA k - 1
    · exact (hcAS j hjlast).1
    · have hj_eq : j = famA k - 1 := by omega
      rw [hj_eq]; exact hcAend
  -- Verify Fw at target = Fw f u + 1
  have hFw_target : Fw f (repeatTargetClock c k r j) = Fw f u + 1 := by
    show Fw f (sr + famH k + 2 * j) = Fw f u + 1
    rw [hF_cAS, hF_cA]
    dsimp only [sr]
    rw [hF_rep, hFw_endBank, hFw_u]
    omega
  -- Verify Ar f u (target - u) = 0!
  let k_win := len_u_to_bank + (r * (repeatBlock k).length + (famH k + 2 * j))
  have huk : u + k_win = repeatTargetClock c k r j := by
    show u + (len_u_to_bank + (r * (repeatBlock k).length + (famH k + 2 * j))) =
      s0 + r * (repeatBlock k).length + famH k + 2 * j
    omega
  have hAr_zero : Ar f u k_win = 0 := by
    dsimp only [k_win]
    rw [Ar_add, hlen_ub]
    change Ar f u len_u_to_bank +
      Ar f s0 (r * (repeatBlock k).length + (famH k + 2 * j)) +
      ((r * (repeatBlock k).length + (famH k + 2 * j) : Nat) : Int) * (Fw f s0 - Fw f u) = 0
    rw [Ar_add f s0 (r * (repeatBlock k).length) (famH k + 2 * j)]
    rw [Ar_add f sr (famH k) (2 * j)]
    have hFs0 : Fw f s0 - Fw f u = -((famH k : Int) - 1) := by
      rw [hFw_endBank, hFw_u]; omega
    have hFsr : Fw f sr - Fw f s0 = 0 := by
      dsimp only [sr]; rw [hF_rep]; omega
    have hFcA_diff : Fw f (sr + famH k) - Fw f sr = (famH k : Int) := by
      rw [hF_cA]; omega
    rw [hAr_rep, hFs0, hFsr, hFcA_diff, hAr_cAS]
    -- Clear factor 2 using h2Ar_ub and hAr_cA
    have h2zero : 2 * (Ar f u len_u_to_bank +
        (((r * (repeatBlock k).length : Nat) : Int) * ((famH k : Int) - 1) +
          (Ar f sr (famH k) + (j : Int) + ((2 * j : Nat) : Int) * (famH k : Int)) +
          ((famH k + 2 * j : Nat) : Int) * 0) +
        ((r * (repeatBlock k).length + (famH k + 2 * j) : Nat) : Int) * -((famH k : Int) - 1)) = 0 := by
      have hd_cast : (d : Int) = 4 + 3 * (j : Int) := by dsimp [d]
      push_cast at hAr_cA ⊢
      grind only
    omega
  refine ⟨hTarget_A, u, k_win, by omega, huk, ?_⟩
  refine ⟨by dsimp [k_win, len_u_to_bank]; omega, ?_, hAr_zero⟩
  rw [huk, hFw_target]

/-! ## Counting theorems: exact post-cut additions, internal supply ≥ R*a, and unbounded ratio -/

private theorem bankBlock_additions (f : Nat → Bool) (c k : Nat) (hk : 1 ≤ k)
    (hBank : MatchesAt f c (bankBlock k)) :
    additions f c (bankBlock k).length = 4 * famA k + famH k + 2 := by
  have hH3 : 3 ≤ famH k := by unfold famH; omega
  have hBlen := bankBlock_length k hk
  rw [bankBlock_eq k hk] at hBank
  have hBank' : MatchesAt f c
      (List.replicate (famH k - 2) true ++
        (asRep (famBank k - 1) ++
          ([true] ++ ([true] ++ (asRep (famLift k - 1) ++
            ([true] ++ List.replicate (famH k + 1) false)))))) := by
    simpa [List.append_assoc] using hBank
  obtain ⟨hb1, hbr1⟩ := matchesAt_append hBank'
  obtain ⟨hb2, hbr2⟩ := matchesAt_append hbr1
  obtain ⟨hb3, hbr3⟩ := matchesAt_append hbr2
  obtain ⟨hb4, hbr4⟩ := matchesAt_append hbr3
  obtain ⟨hb5, hbr5⟩ := matchesAt_append hbr4
  obtain ⟨hb6, hb7⟩ := matchesAt_append hbr5
  simp only [List.length_replicate, asRep_length, List.length_singleton] at hbr1 hbr2 hbr3 hbr4 hbr5 hb2 hb3 hb4 hb5 hb6 hb7
  have htot : (bankBlock k).length =
      (famH k - 2) + (2 * (famBank k - 1) + (1 + (1 + (2 * (famLift k - 1) + (1 + (famH k + 1)))))) := by
    unfold famBank famLift at *; omega
  rw [htot]
  unfold additions
  rw [cN_add, cN_add, cN_add, cN_add, cN_add, cN_add]
  have c1 := count_allA_additions f c (famH k - 2) (matchesAt_replicate hb1)
  have c2 := count_as_additions f (c + (famH k - 2)) (famBank k - 1) (matchesAt_asRep hb2)
  have c3 : cN (fun x => f x = true) (c + (famH k - 2) + 2 * (famBank k - 1)) 1 = 1 := by
    have h := cN_succ_pos (fun x => f x = true) (c + (famH k - 2) + 2 * (famBank k - 1)) 0 (by simpa using matchesAt_singleton hb3)
    simpa [cN] using h
  have c4 : cN (fun x => f x = true) (c + (famH k - 2) + 2 * (famBank k - 1) + 1) 1 = 1 := by
    have h := cN_succ_pos (fun x => f x = true) (c + (famH k - 2) + 2 * (famBank k - 1) + 1) 0 (by simpa using matchesAt_singleton hb4)
    simpa [cN] using h
  have c5 := count_as_additions f (c + (famH k - 2) + 2 * (famBank k - 1) + 1 + 1)
    (famLift k - 1) (matchesAt_asRep hb5)
  have c6 : cN (fun x => f x = true)
      (c + (famH k - 2) + 2 * (famBank k - 1) + 1 + 1 + 2 * (famLift k - 1)) 1 = 1 := by
    have h := cN_succ_pos (fun x => f x = true)
      (c + (famH k - 2) + 2 * (famBank k - 1) + 1 + 1 + 2 * (famLift k - 1)) 0 (by simpa using matchesAt_singleton hb6)
    simpa [cN] using h
  have c7 := count_allS_additions f
      (c + (famH k - 2) + 2 * (famBank k - 1) + 1 + 1 + 2 * (famLift k - 1) + 1)
      (famH k + 1) (matchesAt_replicate hb7)
  unfold additions at c1 c2 c5 c7
  rw [c1, c2, c3, c4, c5, c6, c7]
  unfold famBank famLift
  omega

private theorem repeat_copies_internal_ge (f : Nat → Bool) (c k R : Nat) (hk : 1 ≤ k)
    (hmatch : MatchesAt f c (familyTail k R)) :
    ∀ m : Nat, m ≤ R →
      m * famA k ≤ cN (InternalSupplied f c) (c + (bankBlock k).length) (m * (repeatBlock k).length)
  | 0, _ => by simp
  | m + 1, hm => by
      have ih := repeat_copies_internal_ge f c k R hk hmatch m (by omega)
      have hmul : (m + 1) * (repeatBlock k).length =
          m * (repeatBlock k).length + (repeatBlock k).length := by
        rw [Nat.succ_mul]
      rw [hmul, cN_add]
      -- In copy m (starting at sm = c + bankBlock.length + m * repeatBlock.length),
      -- all `famA k` targets at sm + famH k + 2*j are internally supplied!
      let sm := c + (bankBlock k).length + m * (repeatBlock k).length
      have hVlen := repeatBlock_length k hk
      have hge_copy : famA k ≤ cN (InternalSupplied f c) sm (repeatBlock k).length := by
        have hsplit1 := cN_sub (InternalSupplied f c) sm (famH k) (repeatBlock k).length (by omega)
        have hsplit2 := cN_sub (InternalSupplied f c) (sm + famH k) (2 * famA k)
          ((repeatBlock k).length - famH k) (by omega)
        have hevens : famA k ≤ cN (InternalSupplied f c) (sm + famH k) (2 * famA k) := by
          apply count_evens_ge
          intro j hj
          exact bank_to_copy_zero_win f c k R m j hk (by omega) hj hmatch
        omega
      rw [Nat.succ_mul]
      change m * famA k + famA k ≤
        cN (InternalSupplied f c) (c + (bankBlock k).length) (m * (repeatBlock k).length) +
        cN (InternalSupplied f c) sm (repeatBlock k).length
      omega

/-- Exact cross-block reuse budget for arbitrary `k ≥ 1`, arbitrary copy count `R`,
and EVERY original prehistory `f` matching `familyWord k R` after arbitrary length `n`.
All `EndN f 0` and `free` counts keep origin `0` and retain all old co-suppliers. -/
theorem cross_block_reuse_counts (f : Nat → Bool) (n k R : Nat) (hk : 1 ≤ k)
    (hword : MatchesAt f n (familyWord k R)) :
    additions f (n + (famH k + 2)) (familyTail k R).length =
      (4 * famA k + famH k + 4) + R * (famH k + famA k) ∧
    R * famA k ≤ internalSuppliedCount f (n + (famH k + 2)) (familyTail k R).length ∧
    free f (n + (famH k + 2)) (familyTail k R).length +
      exclusiveOldCount f (n + (famH k + 2)) (familyTail k R).length ≤
      (4 * famA k + famH k + 4) + R * famH k := by
  have hmatch : MatchesAt f (n + (famH k + 2)) (familyTail k R) := by
    have h' := (matchesAt_append hword).2
    simpa [List.length_replicate] using h'
  let c := n + (famH k + 2)
  let L := (familyTail k R).length
  have hmatch' : MatchesAt f c (bankBlock k ++ (repeatWord R (repeatBlock k) ++ [true, true])) := by
    simpa [familyTail, List.append_assoc] using hmatch
  obtain ⟨hBank, hAfterBank⟩ := matchesAt_append hmatch'
  obtain ⟨hRep, hAA⟩ := matchesAt_append hAfterBank
  have hL_eq : L = (bankBlock k).length + (R * (repeatBlock k).length + 2) := by
    simp [L, familyTail, List.length_append, repeatWord_length]
  -- Exact post-cut additions
  have hA_total : additions f c L = (4 * famA k + famH k + 4) + R * (famH k + famA k) := by
    rw [hL_eq]
    unfold additions
    rw [cN_add, cN_add]
    have c1 := bankBlock_additions f c k hk hBank
    have c2 := (repeatWord_fw_ar f (c + (bankBlock k).length) k hk R hRep).2.2
    have hAA_arr : ∀ i, i < 2 → f (c + (bankBlock k).length + R * (repeatBlock k).length + i) = true := by
      intro i hi
      have h' := hAA i (by simp; omega)
      rw [repeatWord_length] at h'
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simpa using h'
    have c3 := count_allA_additions f (c + (bankBlock k).length + R * (repeatBlock k).length) 2 hAA_arr
    unfold additions at c1 c2 c3
    rw [c1, c2, c3]
    omega
  -- Internal supply ≥ R * a
  have hInt_ge : R * famA k ≤ internalSuppliedCount f c L := by
    unfold internalSuppliedCount
    rw [hL_eq, cN_add, cN_add]
    have hrep := repeat_copies_internal_ge f c k R hk hmatch R (Nat.le_refl R)
    omega
  -- Partition gives F + O_c ≤ (4a + H + 4) + R * H
  have hpart := additions_partition_after_cut f c L
  have hFO_le : free f c L + exclusiveOldCount f c L ≤ (4 * famA k + famH k + 4) + R * famH k := by
    rw [hA_total] at hpart
    have hdist : R * (famH k + famA k) = R * famH k + R * famA k := Nat.mul_add R (famH k) (famA k)
    omega
  exact ⟨hA_total, hInt_ge, hFO_le⟩

/-- Unbounded ratio theorem: for EVERY constant slope `C : Nat` and additive constant `K : Nat`,
there exist explicit staged-grammar parameters `k ≥ 1` (`H = 3k`) and `R ≥ 1` such that for
EVERY sign history `f : Nat → Bool` and EVERY arbitrary prehistory length `n : Nat` matching
`familyWord k R` after `n`,
  `C * (F + O_c) + K < A_after_cut`.
In particular, no linear cross-block capacity `A_after_cut ≤ C * (F + O_c) + K` holds. -/
theorem no_linear_cross_block_capacity (C K : Nat) :
    ∃ k R, 1 ≤ k ∧ 1 ≤ R ∧
      ∀ (f : Nat → Bool) (n : Nat),
        MatchesAt f n (familyWord k R) →
        C * (free f (n + (famH k + 2)) (familyTail k R).length +
          exclusiveOldCount f (n + (famH k + 2)) (familyTail k R).length) + K <
          additions f (n + (famH k + 2)) (familyTail k R).length := by
  let k := C + 1
  have hk : 1 ≤ k := by omega
  let overhead := 4 * famA k + famH k + 4
  let R := C * overhead + K + 1
  refine ⟨k, R, hk, by omega, ?_⟩
  intro f n hword
  obtain ⟨hA, _hInt, hFO⟩ := cross_block_reuse_counts f n k R hk hword
  -- Per-copy excess: famH k + famA k = C * famH k + 4 * (C + 1)
  have hexcess : C * famH k + 4 ≤ famH k + famA k := by
    have hk_def : k = C + 1 := rfl
    unfold famH famA
    rw [hk_def]
    have hsub : 3 * (C + 1) - 2 = 3 * C + 1 := by omega
    rw [hsub]
    have hmul1 : (C + 1) * (3 * C + 1) = 3 * (C * C) + 4 * C + 1 := by
      have h3c : C * (3 * C) = 3 * (C * C) := by
        rw [← Nat.mul_assoc, Nat.mul_comm C 3, Nat.mul_assoc]
      simp [Nat.add_mul, Nat.mul_add, h3c]; omega
    have hmul2 : C * (3 * (C + 1)) = 3 * (C * C) + 3 * C := by
      have h3c : C * (3 * C) = 3 * (C * C) := by
        rw [← Nat.mul_assoc, Nat.mul_comm C 3, Nat.mul_assoc]
      simp [Nat.mul_add, h3c]; omega
    omega
  have hR_mul : R * (C * famH k + 4) ≤ R * (famH k + famA k) :=
    Nat.mul_le_mul_left R hexcess
  have hC_FO : C * (free f (n + (famH k + 2)) (familyTail k R).length +
      exclusiveOldCount f (n + (famH k + 2)) (familyTail k R).length) ≤
      C * (overhead + R * famH k) :=
    Nat.mul_le_mul_left C hFO
  have h1 : C * (overhead + R * famH k) = C * overhead + R * (C * famH k) := by
    rw [Nat.mul_add]
    have : C * (R * famH k) = R * (C * famH k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm C R, Nat.mul_assoc]
    rw [this]
  have h2 : R * (C * famH k + 4) = R * (C * famH k) + 4 * R := by
    rw [Nat.mul_add, Nat.mul_comm R 4]
  have hR_def : R = C * overhead + K + 1 := rfl
  have hA' : additions f (n + (famH k + 2)) (familyTail k R).length =
      overhead + R * (famH k + famA k) := hA
  omega

/-- Direct refutation of `H-20261126-01`'s candidate `2 * A_after_cut ≤ 3 * (F + O_c) - 3`
using the explicit 2-block counterexample `V₁ = stagedBlock [1,2,1,1]`, `V₂ = stagedBlock [1,1,1,2]`
(27 letters after any prehistory `U` of length `n`), retaining all old co-suppliers. -/
def minCounterTail : List Bool :=
  stagedBlock [1, 2, 1, 1] ++ stagedBlock [1, 1, 1, 2] ++ [true, true]

def minCounterWord : List Bool :=
  List.replicate 5 false ++ minCounterTail

theorem h20261126_two_block_counter (f : Nat → Bool) (n : Nat)
    (hword : MatchesAt f n minCounterWord) :
    additions f (n + 5) minCounterTail.length = 12 ∧
    4 ≤ internalSuppliedCount f (n + 5) minCounterTail.length ∧
    3 * (free f (n + 5) minCounterTail.length + exclusiveOldCount f (n + 5) minCounterTail.length) - 3 <
      2 * additions f (n + 5) minCounterTail.length := by
  have htail : MatchesAt f (n + 5) minCounterTail := by
    have h' := (matchesAt_append hword).2
    simpa [List.length_replicate] using h'
  let c := n + 5
  have htail_val : minCounterTail =
      [true, true, false, true, true, true, false, false, false, false,
       true, true, true, true, false, true, false, false, false, false, true, true] := by
    decide
  have hlen : minCounterTail.length = 22 := by rw [htail_val]; rfl
  have hf : ∀ i, i < 22 → f (c + i) = minCounterTail[i]! := fun i hi => htail i (by omega)
  -- Concrete values of f (c + 0) .. f (c + 21)
  have e0 : f (c + 0) = true := by simpa [htail_val] using hf 0 (by omega)
  have e1 : f (c + 1) = true := by simpa [htail_val] using hf 1 (by omega)
  have e2 : f (c + 2) = false := by simpa [htail_val] using hf 2 (by omega)
  have e3 : f (c + 3) = true := by simpa [htail_val] using hf 3 (by omega)
  have e4 : f (c + 4) = true := by simpa [htail_val] using hf 4 (by omega)
  have e5 : f (c + 5) = true := by simpa [htail_val] using hf 5 (by omega)
  have e6 : f (c + 6) = false := by simpa [htail_val] using hf 6 (by omega)
  have e7 : f (c + 7) = false := by simpa [htail_val] using hf 7 (by omega)
  have e8 : f (c + 8) = false := by simpa [htail_val] using hf 8 (by omega)
  have e9 : f (c + 9) = false := by simpa [htail_val] using hf 9 (by omega)
  have e10 : f (c + 10) = true := by simpa [htail_val] using hf 10 (by omega)
  have e11 : f (c + 11) = true := by simpa [htail_val] using hf 11 (by omega)
  have e12 : f (c + 12) = true := by simpa [htail_val] using hf 12 (by omega)
  have e13 : f (c + 13) = true := by simpa [htail_val] using hf 13 (by omega)
  have e14 : f (c + 14) = false := by simpa [htail_val] using hf 14 (by omega)
  have e15 : f (c + 15) = true := by simpa [htail_val] using hf 15 (by omega)
  have e16 : f (c + 16) = false := by simpa [htail_val] using hf 16 (by omega)
  have e17 : f (c + 17) = false := by simpa [htail_val] using hf 17 (by omega)
  have e18 : f (c + 18) = false := by simpa [htail_val] using hf 18 (by omega)
  have e19 : f (c + 19) = false := by simpa [htail_val] using hf 19 (by omega)
  have e20 : f (c + 20) = true := by simpa [htail_val] using hf 20 (by omega)
  have e21 : f (c + 21) = true := by simpa [htail_val] using hf 21 (by omega)
  -- Step Fw values relative to Fw f c
  have w1 : Fw f (c + 1) = Fw f c + 1 := by rw [Fw_succ, show c = c + 0 by omega, e0]; simp [sign]
  have w2 : Fw f (c + 2) = Fw f c + 2 := by rw [show c + 2 = (c + 1) + 1 from rfl, Fw_succ, e1, w1]; simp [sign]; omega
  have w3 : Fw f (c + 3) = Fw f c + 1 := by rw [show c + 3 = (c + 2) + 1 from rfl, Fw_succ, e2, w2]; simp [sign]; omega
  have w4 : Fw f (c + 4) = Fw f c + 2 := by rw [show c + 4 = (c + 3) + 1 from rfl, Fw_succ, e3, w3]; simp [sign]; omega
  have w5 : Fw f (c + 5) = Fw f c + 3 := by rw [show c + 5 = (c + 4) + 1 from rfl, Fw_succ, e4, w4]; simp [sign]; omega
  have w6 : Fw f (c + 6) = Fw f c + 4 := by rw [show c + 6 = (c + 5) + 1 from rfl, Fw_succ, e5, w5]; simp [sign]; omega
  have w7 : Fw f (c + 7) = Fw f c + 3 := by rw [show c + 7 = (c + 6) + 1 from rfl, Fw_succ, e6, w6]; simp [sign]; omega
  have w8 : Fw f (c + 8) = Fw f c + 2 := by rw [show c + 8 = (c + 7) + 1 from rfl, Fw_succ, e7, w7]; simp [sign]; omega
  have w9 : Fw f (c + 9) = Fw f c + 1 := by rw [show c + 9 = (c + 8) + 1 from rfl, Fw_succ, e8, w8]; simp [sign]; omega
  have w10 : Fw f (c + 10) = Fw f c := by rw [show c + 10 = (c + 9) + 1 from rfl, Fw_succ, e9, w9]; simp [sign]; omega
  have w11 : Fw f (c + 11) = Fw f c + 1 := by rw [show c + 11 = (c + 10) + 1 from rfl, Fw_succ, e10, w10]; simp [sign]
  have w12 : Fw f (c + 12) = Fw f c + 2 := by rw [show c + 12 = (c + 11) + 1 from rfl, Fw_succ, e11, w11]; simp [sign]; omega
  have w13 : Fw f (c + 13) = Fw f c + 3 := by rw [show c + 13 = (c + 12) + 1 from rfl, Fw_succ, e12, w12]; simp [sign]; omega
  have w14 : Fw f (c + 14) = Fw f c + 4 := by rw [show c + 14 = (c + 13) + 1 from rfl, Fw_succ, e13, w13]; simp [sign]; omega
  have w15 : Fw f (c + 15) = Fw f c + 3 := by rw [show c + 15 = (c + 14) + 1 from rfl, Fw_succ, e14, w14]; simp [sign]; omega
  -- Four explicit internal supplies:
  -- 1. target c+5 supplied by c+2 (len 3: SAA)
  have hS5 : InternalSupplied f c (c + 5) := by
    refine ⟨e5, c + 2, 3, by omega, by omega, by omega, ?_, ?_⟩
    · rw [show c + 2 + 3 = c + 5 by omega, w5, w2]; omega
    · rw [Ar3, show c + 2 + 1 = c + 3 by omega, show c + 2 + 2 = c + 4 by omega,
          show c + 2 + 3 = c + 5 by omega, w2, w3, w4, w5]; omega
  -- 2. target c+12 supplied by c+9 (len 3: SAA across block boundary)
  have hS12 : InternalSupplied f c (c + 12) := by
    refine ⟨e12, c + 9, 3, by omega, by omega, by omega, ?_, ?_⟩
    · rw [show c + 9 + 3 = c + 12 by omega, w12, w9]; omega
    · rw [Ar3, show c + 9 + 1 = c + 10 by omega, show c + 9 + 2 = c + 11 by omega,
          show c + 9 + 3 = c + 12 by omega, w9, w10, w11, w12]; omega
  -- 3. target c+13 supplied by c+2 (len 11: SAME bank peak c+2 reused across blocks!)
  have hS13 : InternalSupplied f c (c + 13) := by
    refine ⟨e13, c + 2, 11, by omega, by omega, by omega, ?_, ?_⟩
    · rw [show c + 2 + 11 = c + 13 by omega, w13, w2]; omega
    · simp only [Ar, show c + 2 + 0 + 1 = c + 3 by omega,
        show c + 2 + 1 + 1 = c + 4 by omega, show c + 2 + 2 + 1 = c + 5 by omega,
        show c + 2 + 3 + 1 = c + 6 by omega, show c + 2 + 4 + 1 = c + 7 by omega,
        show c + 2 + 5 + 1 = c + 8 by omega, show c + 2 + 6 + 1 = c + 9 by omega,
        show c + 2 + 7 + 1 = c + 10 by omega, show c + 2 + 8 + 1 = c + 11 by omega,
        show c + 2 + 9 + 1 = c + 12 by omega, show c + 2 + 10 + 1 = c + 13 by omega,
        w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13]
      omega
  -- 4. target c+15 supplied by c+8 (len 7: descent clock c+8 supplies c+15!)
  have hS15 : InternalSupplied f c (c + 15) := by
    refine ⟨e15, c + 8, 7, by omega, by omega, by omega, ?_, ?_⟩
    · rw [show c + 8 + 7 = c + 15 by omega, w15, w8]; omega
    · simp only [Ar, show c + 8 + 0 + 1 = c + 9 by omega,
        show c + 8 + 1 + 1 = c + 10 by omega, show c + 8 + 2 + 1 = c + 11 by omega,
        show c + 8 + 3 + 1 = c + 12 by omega, show c + 8 + 4 + 1 = c + 13 by omega,
        show c + 8 + 5 + 1 = c + 14 by omega, show c + 8 + 6 + 1 = c + 15 by omega,
        w8, w9, w10, w11, w12, w13, w14, w15]
      omega
  -- Exact count of additions = 12
  have hadd12 : additions f c minCounterTail.length = 12 := by
    rw [hlen]
    unfold additions
    simp only [cN, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
      e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21]
    decide
  -- Lower bound internalSuppliedCount ≥ 4
  have hint4 : 4 ≤ internalSuppliedCount f c minCounterTail.length := by
    unfold internalSuppliedCount
    rw [hlen]
    have hmono : ∀ a b, a ≤ b → cN (InternalSupplied f c) c a ≤ cN (InternalSupplied f c) c b := by
      intro a b hab
      have hsp := cN_sub (InternalSupplied f c) c a b hab
      omega
    have p5 : cN (InternalSupplied f c) c 6 = cN (InternalSupplied f c) c 5 + 1 :=
      cN_succ_pos (InternalSupplied f c) c 5 hS5
    have p12 : cN (InternalSupplied f c) c 13 = cN (InternalSupplied f c) c 12 + 1 :=
      cN_succ_pos (InternalSupplied f c) c 12 hS12
    have p13 : cN (InternalSupplied f c) c 14 = cN (InternalSupplied f c) c 13 + 1 :=
      cN_succ_pos (InternalSupplied f c) c 13 hS13
    have p15 : cN (InternalSupplied f c) c 16 = cN (InternalSupplied f c) c 15 + 1 :=
      cN_succ_pos (InternalSupplied f c) c 15 hS15
    have m1 := hmono 6 12 (by omega)
    have m2 := hmono 14 15 (by omega)
    have m3 := hmono 16 22 (by omega)
    omega
  have hpart := additions_partition_after_cut f c minCounterTail.length
  exact ⟨hadd12, hint4, by dsimp only [c] at hadd12 hint4 hpart; omega⟩

end Recaman.CrossBlockReuseUnbounded
