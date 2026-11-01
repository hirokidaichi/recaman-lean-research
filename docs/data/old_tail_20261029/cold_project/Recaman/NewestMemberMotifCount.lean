import Recaman.SuffixHallOwnerMap
import Recaman.P2SubtractionLevelSum

namespace Recaman.NewestMemberMotifCount

/-! Theorem R of H-20261003-01: counting below the newest member.

Let `v` be a member whose window `past e v L` is P2, and suppose every subtraction of that window other
than `own v` is owned by another member that is either an AAS owning its only S (`own b = b - 3`,
`e (b-1) = e (b-2) = A`) or the w1 of a w1 triple owning its oldest S (`own b = b - 7`, bits `S A A A A S`
on `b-6 .. b-1` read oldest first, and the AAS sibling `b - 3` owns `b - 6`). If all members lie at or
before `v`, then `L = 3`: the window of `v` is `AAS`.

Counting: the subtractions of `v`'s window other than `own v` split into AAS-owned and w1-owned ones.
An AAS-owned `s` is followed by the three additions `s+1, s+2, s+3`; a w1-owned `s` gives the addition
`s+5`, and `s+1` is AAS-owned. These additions are distinct, so `3·#AAS + #w1 ≤ #A = (L+1)/2`, while
`#AAS + #w1 = (L-3)/2` and `#w1 ≤ #AAS`. Hence `L ≤ 7`, and `L = 7` is impossible because a w1 owner
needs its S at least 8 clocks before `v`.

In a finite closed configuration whose newest member owns a subtraction lying in no other window,
removing `v` leaves a closed configuration; if that one decomposes into isolated AAS members and w1
triples, this theorem makes `v` an AAS. That is the inductive step of the classification in the case
"`own v` private"; the case where `own v` lies in an older member's window is not treated here.
-/

open ShortPeriodicSupply (sign)
open LeadingRunSupply (P2 past ones p2_count_identities)
open SuffixHallOwnerMap (OwnerMap nodup_map_of_inj)

theorem length_filter_partition {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : p a <;> simp [h] <;> omega

theorem ones_eq_filter (f : Nat → Bool) (L : Nat) :
    ones ((List.range L).map f) = ((List.range L).filter f).length := by
  induction L with
  | zero => simp [ones]
  | succ L ih =>
    rw [List.range_succ, List.map_append, List.filter_append]
    have hone : ∀ (u w : List Bool), ones (u ++ w) = ones u + ones w := LeadingRunSupply.ones_append
    rw [hone, ih]
    cases h : f L <;> simp [ones, h]

/-- The motif shape of an owner (AAS owning its S, or a triple's w1 owning its oldest S). -/
def MotifOwner (e : Int → Bool) (M : List Int) (own : Int → Int) (b : Int) : Prop :=
  (own b = b - 3 ∧ e (b - 1) = true ∧ e (b - 2) = true) ∨
  (own b = b - 7 ∧ e (b - 2) = true ∧ e (b - 3) = true ∧ e (b - 4) = true ∧ e (b - 5) = true ∧
    e (b - 6) = false ∧ (b - 3) ∈ M ∧ own (b - 3) = b - 6)

theorem newest_motif_count (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hO : OwnerMap e M lag own) (hA : ∀ b ∈ M, e b = true)
    (v : Int) (hv : v ∈ M) (hnew : ∀ b ∈ M, b ≤ v)
    (L : Nat) (hP : P2 (past e v L)) (hown : v - (L : Int) ≤ own v)
    (hcov : ∀ c : Int, v - L ≤ c → c < v → e c = false → c ≠ own v →
      ∃ b ∈ M, b ≠ v ∧ own b = c)
    (hmotif : ∀ b ∈ M, b ≠ v → MotifOwner e M own b) :
    L = 3 := by
  -- offsets: index i ∈ range L is the clock v - (i+1)
  let clk : Nat → Int := fun i => v - ((i : Int) + 1)
  let Sv := (List.range L).filter (fun i => !e (clk i))
  let T := Sv.filter (fun i => decide (clk i ≠ own v))
  let isA : Nat → Bool := fun i => decide ((clk i + 3) ∈ M ∧ own (clk i + 3) = clk i)
  let TA := T.filter isA
  let TW := T.filter (fun i => !isA i)
  let Av := (List.range L).filter (fun i => e (clk i))
  have hSvnodup : Sv.Nodup := List.nodup_range.filter _
  have hTnodup : T.Nodup := hSvnodup.filter _
  have hTAnodup : TA.Nodup := hTnodup.filter _
  have hTWnodup : TW.Nodup := hTnodup.filter _
  have memT : ∀ i ∈ T, i < L ∧ e (clk i) = false ∧ clk i ≠ own v := by
    intro i hi
    have h := List.mem_filter.mp hi
    have h' := List.mem_filter.mp h.1
    refine ⟨List.mem_range.mp h'.1, by simpa using h'.2, by simpa using h.2⟩
  have owner : ∀ i ∈ T, ∃ b ∈ M, b ≠ v ∧ own b = clk i := by
    intro i hi
    obtain ⟨hiL, hS, hne⟩ := memT i hi
    exact hcov (clk i) (by simp [clk]; omega) (by simp [clk]; omega) hS hne
  have TAsub : ∀ i ∈ TA, i ∈ T := fun i hi => (List.mem_filter.mp hi).1
  have TWsub : ∀ i ∈ TW, i ∈ T := fun i hi => (List.mem_filter.mp hi).1
  -- AAS-owned offsets
  have factA : ∀ i ∈ TA, 3 ≤ i ∧ ∀ d : Nat, 1 ≤ d → d ≤ 3 → e (clk (i - d)) = true := by
    intro i hi
    have h := List.mem_filter.mp hi
    have hc : (clk i + 3) ∈ M ∧ own (clk i + 3) = clk i := by simpa [isA] using h.2
    have hle := hnew _ hc.1
    have hne : clk i + 3 ≠ v := by
      intro heq
      obtain ⟨_, _, hne'⟩ := memT i h.1
      exact hne' (by rw [← hc.2, heq])
    have hi3 : 3 ≤ i := by simp [clk] at hle hne; omega
    rcases hmotif _ hc.1 hne with ⟨ho, h1, h2⟩ | ⟨ho, _⟩
    · refine ⟨hi3, fun d hd1 hd3 => ?_⟩
      have hcd : clk (i - d) = clk i + d := by simp [clk]; omega
      rw [hcd]
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl
      · have : clk i + 3 - 2 = clk i + ((1 : Nat) : Int) := by push_cast; omega
        rw [← this]; exact h2
      · have : clk i + 3 - 1 = clk i + ((2 : Nat) : Int) := by push_cast; omega
        rw [← this]; exact h1
      · have : clk i + 3 = clk i + ((3 : Nat) : Int) := by push_cast; omega
        rw [← this]; exact hA _ hc.1
    · exfalso; rw [hc.2] at ho; omega
  -- w1-owned offsets
  have factW : ∀ i ∈ TW, 7 ≤ i ∧ (∀ d : Nat, 2 ≤ d → d ≤ 5 → e (clk (i - d)) = true) ∧ (i - 1) ∈ TA := by
    intro i hi
    have h := List.mem_filter.mp hi
    have hnA : ¬ ((clk i + 3) ∈ M ∧ own (clk i + 3) = clk i) := by
      intro hc
      have h2 := h.2
      simp [isA, hc.1, hc.2] at h2
    obtain ⟨hiL, hS, hne⟩ := memT i h.1
    obtain ⟨b, hb, hbv, hob⟩ := owner i h.1
    have hle := hnew b hb
    have hblt : b < v := by omega
    rcases hmotif b hb hbv with ⟨ho, _, _⟩ | ⟨ho, h2, h3, h4, h5, h6, hsib, hsibo⟩
    · exfalso; apply hnA
      have : b = clk i + 3 := by omega
      subst this; exact ⟨hb, hob⟩
    · have hbc : b = clk i + 7 := by omega
      subst hbc
      have hi7 : 7 ≤ i := by simp [clk] at hblt; omega
      refine ⟨hi7, fun d hd2 hd5 => ?_, ?_⟩
      · have hcd : clk (i - d) = clk i + d := by simp [clk]; omega
        rw [hcd]
        rcases (by omega : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5) with rfl | rfl | rfl | rfl
        · have e1 : clk i + 7 - 5 = clk i + ((2 : Nat) : Int) := by push_cast; omega
          rw [← e1]; exact h5
        · have e1 : clk i + 7 - 4 = clk i + ((3 : Nat) : Int) := by push_cast; omega
          rw [← e1]; exact h4
        · have e1 : clk i + 7 - 3 = clk i + ((4 : Nat) : Int) := by push_cast; omega
          rw [← e1]; exact h3
        · have e1 : clk i + 7 - 2 = clk i + ((5 : Nat) : Int) := by push_cast; omega
          rw [← e1]; exact h2
      · have hclk : clk (i - 1) = clk i + 1 := by simp [clk]; omega
        have hS1 : e (clk (i - 1)) = false := by
          rw [hclk]; have : clk i + 7 - 6 = clk i + 1 := by omega
          rw [← this]; exact h6
        have hne1 : clk (i - 1) ≠ own v := by
          intro heq
          have hown' : own (clk i + 7 - 3) = own v := by rw [hsibo, ← heq, hclk]; omega
          have := hO.inj _ hsib _ hv hown'
          omega
        have hT1 : (i - 1) ∈ T := by
          apply List.mem_filter.mpr
          refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), by simp [hS1]⟩, by simpa using hne1⟩
        apply List.mem_filter.mpr
        refine ⟨hT1, ?_⟩
        simp only [isA, decide_eq_true_eq]
        rw [hclk]
        have : clk i + 1 + 3 = clk i + 7 - 3 := by omega
        rw [this]
        refine ⟨hsib, ?_⟩
        rw [hsibo]; omega
  -- the additions B
  let Bl := TA.map (fun i => i - 1) ++ TA.map (fun i => i - 2) ++ TA.map (fun i => i - 3) ++
    TW.map (fun i => i - 5)
  have inAv : ∀ j, j < L → e (clk j) = true → j ∈ Av := fun j hj he =>
    List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simpa using he⟩
  have hBsub : Bl ⊆ Av := by
    intro j hj
    simp only [Bl, List.mem_append, List.mem_map] at hj
    rcases hj with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
    · have hiL := (memT i (TAsub i hi)).1
      exact inAv _ (by omega) ((factA i hi).2 1 (Nat.le_refl _) (by omega))
    · have hiL := (memT i (TAsub i hi)).1
      exact inAv _ (by omega) ((factA i hi).2 2 (by omega) (by omega))
    · have hiL := (memT i (TAsub i hi)).1
      exact inAv _ (by omega) ((factA i hi).2 3 (by omega) (Nat.le_refl _))
    · have hiL := (memT i (TWsub i hi)).1
      exact inAv _ (by omega) ((factW i hi).2.1 5 (by omega) (Nat.le_refl _))
  -- an S offset is not an A offset
  have notA : ∀ i ∈ T, ∀ j, e (clk j) = true → i ≠ j := by
    intro i hi j hj heq
    subst heq
    rw [(memT i hi).2.1] at hj
    exact absurd hj (by decide)
  have shiftNodup : ∀ (d : Nat) (l : List Nat), l.Nodup → (∀ i ∈ l, d ≤ i) →
      (l.map (fun i => i - d)).Nodup :=
    fun d l hl hd => nodup_map_of_inj l _ hl (fun a ha b hb h => by
      have := hd a ha; have := hd b hb; omega)
  have gA : ∀ i ∈ TA, 3 ≤ i := fun i hi => (factA i hi).1
  have gW : ∀ i ∈ TW, 7 ≤ i := fun i hi => (factW i hi).1
  -- pairwise disjointness: i - a = i' - b with a < b forces the S offset i to be the A offset i' - (b - a)
  have dAA : ∀ (a b : Nat), a < b → b ≤ 3 → ∀ i ∈ TA, ∀ i' ∈ TA, i - a ≠ i' - b := by
    intro a b hab hb3 i hi i' hi' heq
    have h3 := gA i hi; have h3' := gA i' hi'
    exact notA i (TAsub i hi) (i' - (b - a)) ((factA i' hi').2 (b - a) (by omega) (by omega)) (by omega)
  have dAW : ∀ (a : Nat), 1 ≤ a → a ≤ 3 → ∀ i ∈ TA, ∀ i' ∈ TW, i - a ≠ i' - 5 := by
    intro a ha1 ha3 i hi i' hi' heq
    have h3 := gA i hi; have h7 := gW i' hi'
    exact notA i (TAsub i hi) (i' - (5 - a)) ((factW i' hi').2.1 (5 - a) (by omega) (by omega)) (by omega)
  have hBnodup : Bl.Nodup := by
    simp only [Bl]
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨⟨shiftNodup 1 TA hTAnodup (fun i hi => by have := gA i hi; omega),
      shiftNodup 2 TA hTAnodup (fun i hi => by have := gA i hi; omega), ?_⟩,
      shiftNodup 3 TA hTAnodup gA, ?_⟩, shiftNodup 5 TW hTWnodup (fun i hi => by have := gW i hi; omega), ?_⟩
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hy
      exact dAA 1 2 (by omega) (by omega) i hi i' hi'
    · intro x hx y hy
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hy
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact dAA 1 3 (by omega) (Nat.le_refl _) i hi i' hi'
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact dAA 2 3 (by omega) (Nat.le_refl _) i hi i' hi'
    · intro x hx y hy
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hy
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          exact dAW 1 (Nat.le_refl _) (by omega) i hi i' hi'
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          exact dAW 2 (by omega) (by omega) i hi i' hi'
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact dAW 3 (by omega) (Nat.le_refl _) i hi i' hi'
  have hBle : Bl.length ≤ Av.length := hBnodup.length_le_of_subset hBsub
  have hBlen : Bl.length = 3 * TA.length + TW.length := by simp [Bl]; omega
  -- w1-owned offsets inject into AAS-owned ones
  have hWA : TW.length ≤ TA.length := by
    have hsub : TW.map (fun i => i - 1) ⊆ TA := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact (factW i hi).2.2
    have := (shiftNodup 1 TW hTWnodup (fun i hi => by have := gW i hi; omega)).length_le_of_subset hsub
    simpa using this
  have hpart : TA.length + TW.length = T.length := length_filter_partition T isA
  -- counting the window
  have hAvS : Av.length + Sv.length = L := by
    have := length_filter_partition (List.range L) (fun i => e (clk i))
    simpa [Av, Sv] using this
  have hones : ones (past e v L) = Av.length := by
    have hf : (fun i : Nat => e (v - ((i + 1 : Nat) : Int))) = (fun i => e (clk i)) := by
      funext i; simp [clk]
    have := ones_eq_filter (fun i : Nat => e (v - ((i + 1 : Nat) : Int))) L
    simp only [past] at this ⊢
    rw [this, hf]
  have hc := p2_count_identities _ hP
  have hlenpast : (past e v L).length = L := by simp [past]
  rw [hlenpast, hones] at hc
  -- the owned S of v is one S offset of the window
  have hTS : T.length + 1 = Sv.length := by
    have hpS := length_filter_partition Sv (fun i => decide (clk i ≠ own v))
    -- exactly one S offset is own v
    let istar := (v - own v - 1).toNat
    have hlt := hO.own_lt v hv
    have hstarS : e (clk istar) = false := by
      have : clk istar = own v := by simp [clk, istar]; omega
      rw [this]; exact hO.own_S v hv
    have hstarmem : istar ∈ Sv.filter (fun i => !decide (clk i ≠ own v)) := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by simp [istar]; omega), by simp [hstarS]⟩, ?_⟩
      simp [clk, istar]; omega
    have hone : (Sv.filter (fun i => !decide (clk i ≠ own v))).length = 1 := by
      have hnd : (Sv.filter (fun i => !decide (clk i ≠ own v))).Nodup := hSvnodup.filter _
      have hsub : Sv.filter (fun i => !decide (clk i ≠ own v)) ⊆ [istar] := by
        intro x hx
        have h := List.mem_filter.mp hx
        have hx' : clk x = own v := by simpa using h.2
        simp [clk, istar] at hx' ⊢; omega
      have h1 : (Sv.filter (fun i => !decide (clk i ≠ own v))).length ≤ [istar].length :=
        hnd.length_le_of_subset hsub
      have h2 := List.length_pos_of_mem hstarmem
      rw [List.length_singleton] at h1
      omega
    simp only [T]; omega
  obtain ⟨hL, -, hev⟩ := hc
  have hW7 : L = 7 → TW.length = 0 := by
    intro h7
    apply List.length_eq_zero_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have := gW i hi
    have := (memT i (TWsub i hi)).1
    omega
  -- arithmetic
  have hAvL : (Av.length : Int) * 2 = L + 1 := by omega
  rcases (by omega : L = 3 ∨ L = 7 ∨ 7 < L ∨ L < 3) with h | h | h | h
  · exact h
  · have := hW7 h; omega
  · omega
  · omega

/-- A finite closed configuration of the line model (members listed in `M`): the owner map (M1, M1'),
members are additions with P2 windows `past e b (lag b)`, and every subtraction inside a member window is
owned (M2). Minimality of the windows is not needed below. -/
structure ClosedConfig (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int) : Prop where
  owner : OwnerMap e M lag own
  addA : ∀ b ∈ M, e b = true
  p2 : ∀ b ∈ M, P2 (past e b (lag b))
  onto : ∀ b ∈ M, ∀ c : Int, b - (lag b : Int) ≤ c → c < b → e c = false → ∃ b' ∈ M, own b' = c

/-- Every member has the motif shape (the local form of "isolated AAS members and w1 triples"). -/
def Motif (e : Int → Bool) (M : List Int) (own : Int → Int) : Prop :=
  ∀ b ∈ M, MotifOwner e M own b

/-- Removing a member whose owned subtraction lies in no other member's window keeps the configuration
closed. -/
theorem erase_closed (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hC : ClosedConfig e M lag own) (v : Int) (hv : v ∈ M)
    (hpriv : ∀ b ∈ M, b ≠ v → ¬ (b - (lag b : Int) ≤ own v ∧ own v < b)) :
    ClosedConfig e (M.erase v) lag own := by
  have hnd := hC.owner.nodup
  have mem_er : ∀ b, b ∈ M.erase v ↔ b ≠ v ∧ b ∈ M := fun b => hnd.mem_erase_iff
  refine ⟨⟨hnd.erase v, fun b hb => hC.owner.own_lt b (List.mem_of_mem_erase hb),
    fun b hb => hC.owner.own_ge b (List.mem_of_mem_erase hb),
    fun b hb => hC.owner.own_S b (List.mem_of_mem_erase hb),
    fun b hb b' hb' h => hC.owner.inj b (List.mem_of_mem_erase hb) b' (List.mem_of_mem_erase hb') h⟩,
    fun b hb => hC.addA b (List.mem_of_mem_erase hb), fun b hb => hC.p2 b (List.mem_of_mem_erase hb), ?_⟩
  intro b hb c h1 h2 hS
  obtain ⟨hbv, hbM⟩ := (mem_er b).1 hb
  obtain ⟨b', hb', hob'⟩ := hC.onto b hbM c h1 h2 hS
  refine ⟨b', (mem_er b').2 ⟨?_, hb'⟩, hob'⟩
  intro heq
  subst heq
  exact hpriv b hbM hbv ⟨by rw [← hob'] at h1; exact h1, by rw [← hob'] at h2; exact h2⟩

/-- The inductive step of the classification when the newest member's owned subtraction is private:
if `M ∖ {v}` has the motif shape, so does `M` (and `v` is an AAS owning `v - 3`). -/
theorem motif_of_erase_newest (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hC : ClosedConfig e M lag own) (v : Int) (hv : v ∈ M) (hnew : ∀ b ∈ M, b ≤ v)
    (hrest : Motif e (M.erase v) own) : Motif e M own := by
  have hnd := hC.owner.nodup
  have mem_er : ∀ b, b ∈ M.erase v ↔ b ≠ v ∧ b ∈ M := fun b => hnd.mem_erase_iff
  have hother : ∀ b ∈ M, b ≠ v → MotifOwner e M own b := by
    intro b hb hbv
    rcases hrest b ((mem_er b).2 ⟨hbv, hb⟩) with h | ⟨h1, h2, h3, h4, h5, h6, hsib, hsibo⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, h4, h5, h6, List.mem_of_mem_erase hsib, hsibo⟩
  intro b hb
  by_cases hbv : b = v
  · subst hbv
    have hL : lag b = 3 := by
      apply newest_motif_count e M lag own hC.owner hC.addA b hb hnew (lag b) (hC.p2 b hb)
        (hC.owner.own_ge b hb)
      · intro c h1 h2 hS hne
        obtain ⟨b', hb', hob'⟩ := hC.onto b hb c h1 h2 hS
        refine ⟨b', hb', ?_, hob'⟩
        intro heq; subst heq; exact hne hob'.symm
      · exact hother
    have hw := P2SubtractionLevelSum.p2_length_three _ (hC.p2 b hb) (by simp [past, hL])
    rw [hL] at hw
    have hlt := hC.owner.own_lt b hb
    have hge := hC.owner.own_ge b hb
    rw [hL] at hge
    have hS := hC.owner.own_S b hb
    have e1 : e (b - 1) = true := by
      have := congrArg (fun l => l[0]?) hw; simpa [past] using this
    have e2 : e (b - 2) = true := by
      have := congrArg (fun l => l[1]?) hw
      simp [past] at this
      have h' : b - (1 + 1) = b - 2 := by omega
      simpa [h'] using this
    have hown : own b = b - 3 := by
      rcases (by omega : own b = b - 1 ∨ own b = b - 2 ∨ own b = b - 3) with h | h | h
      · rw [h] at hS; rw [e1] at hS; exact absurd hS (by decide)
      · rw [h] at hS; rw [e2] at hS; exact absurd hS (by decide)
      · exact h
    exact Or.inl ⟨hown, e1, e2⟩
  · exact hother b hb hbv

/-- Back-closure: a sublist `C` of the members that is closed under predecessors (whenever a member `r`
owns a subtraction lying in the window of a member `m ∈ C`, `r ∈ C`) is again a closed configuration.
`erase_closed` is the special case `C = M.erase v` with a private owned subtraction of `v`. -/
theorem pred_closed_closed (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hC : ClosedConfig e M lag own) (C : List Int) (hsub : C.Sublist M)
    (hpred : ∀ m ∈ C, ∀ r ∈ M, r ≠ m → (m - (lag m : Int) ≤ own r ∧ own r < m) → r ∈ C) :
    ClosedConfig e C lag own := by
  have hmem : ∀ b ∈ C, b ∈ M := fun b hb => hsub.subset hb
  refine ⟨⟨hC.owner.nodup.sublist hsub, fun b hb => hC.owner.own_lt b (hmem b hb),
    fun b hb => hC.owner.own_ge b (hmem b hb), fun b hb => hC.owner.own_S b (hmem b hb),
    fun b hb b' hb' h => hC.owner.inj b (hmem b hb) b' (hmem b' hb') h⟩,
    fun b hb => hC.addA b (hmem b hb), fun b hb => hC.p2 b (hmem b hb), ?_⟩
  intro m hm c h1 h2 hS
  obtain ⟨r, hr, hor⟩ := hC.onto m (hmem m hm) c h1 h2 hS
  refine ⟨r, ?_, hor⟩
  by_cases hrm : r = m
  · subst hrm; exact hm
  · exact hpred m hm r hr hrm ⟨by rw [hor]; exact h1, by rw [hor]; exact h2⟩

/-- E-split: if no window that starts before `z` still owns a subtraction at or after `z`
(`E(z) = 0`), the members whose windows start at or after `z` form a closed configuration. -/
theorem suffix_split_closed (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hC : ClosedConfig e M lag own) (z : Int)
    (hE : ∀ b ∈ M, b - (lag b : Int) < z → own b < z) :
    ClosedConfig e (M.filter (fun a => decide (z ≤ a - (lag a : Int)))) lag own := by
  apply pred_closed_closed e M lag own hC _ List.filter_sublist
  intro m hm r hr _ hwin
  have hm' := List.mem_filter.mp hm
  have hz : z ≤ m - (lag m : Int) := by simpa using hm'.2
  apply List.mem_filter.mpr
  refine ⟨hr, ?_⟩
  simp only [decide_eq_true_eq]
  by_cases h : r - (lag r : Int) < z
  · have := hE r hr h; omega
  · omega

/-- D-split: if no ownership arc crosses `z` (no member `o > z` owns a subtraction before `z`), the
members at or before `z` form a closed configuration. -/
theorem prefix_split_closed (e : Int → Bool) (M : List Int) (lag : Int → Nat) (own : Int → Int)
    (hC : ClosedConfig e M lag own) (z : Int)
    (hD : ∀ o ∈ M, ¬ (own o < z ∧ z < o)) :
    ClosedConfig e (M.filter (fun a => decide (a ≤ z))) lag own := by
  apply pred_closed_closed e M lag own hC _ List.filter_sublist
  intro m hm r hr _ hwin
  have hm' := List.mem_filter.mp hm
  have hz : m ≤ z := by simpa using hm'.2
  apply List.mem_filter.mpr
  refine ⟨hr, ?_⟩
  simp only [decide_eq_true_eq]
  by_cases h : r ≤ z
  · exact h
  · exfalso; exact hD r hr ⟨by omega, by omega⟩

end Recaman.NewestMemberMotifCount
