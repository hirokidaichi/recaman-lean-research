import Recaman.OneSSMultiplicity

namespace Recaman.SSGapBudget

set_option linter.unusedSimpArgs false

open LeadingRunSupply OneSSGapAlgebra OneSSMultiplicity SSFreeSupply

/-! An all-SS structural budget on actual words. This does not allocate S
resources between different supply windows. -/

def zeroGaps (gs : List Nat) : Nat := (gs.filter fun g => g=0).length
def extraAs (gs : List Nat) : Nat := (gs.map fun g => g-1).sum
def enlargedGaps (gs : List Nat) : Nat := (gs.filter fun g => 2≤g).length
def largeGaps (gs : List Nat) : Nat := (gs.filter fun g => 3≤g).length

theorem gap_balance (gs : List Nat) : gs.sum+zeroGaps gs=gs.length+extraAs gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    dsimp [zeroGaps,extraAs] at ih
    by_cases hg : g=0
    · simp [zeroGaps,extraAs,hg]; omega
    · simp [zeroGaps,extraAs,hg]; omega

theorem large_cost (gs : List Nat) : 2*largeGaps gs ≤ extraAs gs := by
  induction gs with
  | nil => simp [largeGaps,extraAs]
  | cons g gs ih =>
    dsimp [largeGaps,extraAs] at ih
    by_cases hg : 3≤g <;> simp [largeGaps,extraAs,hg] <;> omega

theorem enlarged_cost (gs : List Nat) (h : ∀ g ∈ gs, g≠2) :
    2*enlargedGaps gs ≤ extraAs gs := by
  induction gs with
  | nil => simp [enlargedGaps,extraAs]
  | cons g gs ih =>
    have hg2 := h g (by simp)
    have hi := ih (by intro x hx; exact h x (by simp [hx]))
    dsimp [enlargedGaps,extraAs] at hi
    by_cases hg : 2≤g <;> simp [enlargedGaps,extraAs,hg] <;> omega

theorem ssCount_pre_A (a : Nat) (w : List Bool) :
    ssCount (List.replicate a true++w)=ssCount w := by
  induction a with
  | zero => rfl
  | succ a ih => simpa [List.replicate_succ,ssCount] using ih

theorem ssCount_S_As (v : Nat) : ssCount (false::List.replicate v true)=0 := by
  cases v with
  | zero => rfl
  | succ v =>
    have h := ssCount_pre_A v []
    simpa [ssCount,List.replicate_succ] using h

theorem gapWord_head (a b : Nat) (gs : List Nat) :
    (gapWord a (b::gs)).head?=some (if a=0 then false else true) := by
  cases a <;> simp [gapWord,List.replicate_succ]

theorem ssCount_gapWord (a v : Nat) (gs : List Nat) :
    ssCount (gapWord a (gs++[v]))=zeroGaps gs := by
  induction gs generalizing a with
  | nil => simp [gapWord,ssCount_pre_A,ssCount_S_As,zeroGaps]
  | cons g gs ih =>
    simp only [List.cons_append,gapWord,ssCount_pre_A]
    change (if false=false ∧ (gapWord g (gs++[v])).head?=some false then 1 else 0)+
      ssCount (gapWord g (gs++[v]))=zeroGaps (g::gs)
    have hh : (gapWord g (gs++[v])).head?=some (if g=0 then false else true) := by
      cases gs with
      | nil => exact gapWord_head g v []
      | cons x xs => exact gapWord_head g x (xs++[v])
    rw [hh,ih]
    by_cases hg : g=0 <;> simp [zeroGaps,hg] <;> omega

theorem noSAAS_suffix (u w : List Bool) (h : NoSAAS (u++w)) : NoSAAS w := by
  induction u with
  | nil => exact h
  | cons b u ih => exact ih (noSAAS_tail b (u++w) h)

theorem noSAAS_internal_gaps (a v : Nat) (gs : List Nat)
    (h : NoSAAS (gapWord a (gs++[v]))) : ∀ g ∈ gs, g≠2 := by
  induction gs generalizing a with
  | nil => simp
  | cons g gs ih =>
    have hs : NoSAAS (false::gapWord g (gs++[v])) :=
      noSAAS_suffix (List.replicate a true) _ h
    have hg : g≠2 := by
      intro heq
      subst g
      cases gs with
      | nil => exact hs [] (List.replicate v true) (by simp [gapWord])
      | cons x xs => exact hs [] (gapWord x (xs++[v])) (by simp [gapWord])
    have hi := ih g (noSAAS_tail false _ hs)
    intro x hx
    rcases List.mem_cons.mp hx with heq | hm
    · simpa [heq] using hg
    · exact hi x hm

theorem exact_word_budget (a v : Nat) (gs : List Nat)
    (hm : mass (gapWord a (gs++[v]))=1) :
    a+v+extraAs gs=ssCount (gapWord a (gs++[v]))+2 := by
  have hmass := gapWord_mass a (gs++[v])
  have hb := gap_balance gs
  rw [hm] at hmass
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.length_append,
    List.length_cons,List.length_nil,Int.natCast_add,Int.cast_ofNat_Int] at hmass
  rw [ssCount_gapWord]
  omega

/-- Counting gaps of length at least three does not require NoSAAS. -/
theorem large_gap_budget (a v : Nat) (gs : List Nat)
    (hm : mass (gapWord a (gs++[v]))=1) :
    a+v+2*largeGaps gs ≤ ssCount (gapWord a (gs++[v]))+2 := by
  have h := exact_word_budget a v gs hm
  have hc := large_cost gs
  omega

/-- Under the actual forbidden-subword condition, every enlarged internal
gap costs at least two extras. The moment-zero condition is unnecessary. -/
theorem enlarged_gap_budget (a v : Nat) (gs : List Nat)
    (hm : mass (gapWord a (gs++[v]))=1)
    (hno : NoSAAS (gapWord a (gs++[v]))) :
    a+v+2*enlargedGaps gs ≤ ssCount (gapWord a (gs++[v]))+2 := by
  have h := exact_word_budget a v gs hm
  have hc := enlarged_cost gs (noSAAS_internal_gaps a v gs hno)
  omega

theorem word_gap_representation (w : List Bool) : ∃ a gs, w=gapWord a gs := by
  induction w with
  | nil => exact ⟨0,[],rfl⟩
  | cons b w ih =>
    obtain ⟨a,gs,heq⟩ := ih
    cases b with
    | false => exact ⟨0,a::gs,by simp [gapWord,heq]⟩
    | true =>
      refine ⟨a+1,gs,?_⟩
      cases gs <;> simp [gapWord,List.replicate_succ,heq]

theorem nonempty_last (xs : List Nat) (h : xs≠[]) : ∃ gs v, xs=gs++[v] := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[],x,rfl⟩
    | cons y ys =>
      obtain ⟨gs,v,hg⟩ := ih (by simp)
      exact ⟨x::gs,v,by simp [hg]⟩

/-- Every mass-one word containing S is covered by the concrete gap theorem. -/
theorem every_word_budget (w : List Bool) (hS : false ∈ w) (hm : mass w=1)
    (hno : NoSAAS w) :
    ∃ a v gs, w=gapWord a (gs++[v]) ∧
      a+v+extraAs gs=ssCount w+2 ∧ a+v+2*enlargedGaps gs≤ssCount w+2 := by
  obtain ⟨a,gs,hw⟩ := word_gap_representation w
  have hgs : gs≠[] := by
    intro hnil
    simp [hw,hnil,gapWord] at hS
  obtain ⟨inner,v,hinner⟩ := nonempty_last gs hgs
  rw [hinner] at hw
  refine ⟨a,v,inner,hw,?_,?_⟩
  · rw [hw] at hm ⊢
    exact exact_word_budget a v inner hm
  · rw [hw] at hm hno ⊢
    exact enlarged_gap_budget a v inner hm hno

theorem every_P2_budget (w : List Bool) (hP : P2 w) (hno : NoSAAS w) :
    ∃ a v gs, w=gapWord a (gs++[v]) ∧
      a+v+extraAs gs=ssCount w+2 ∧ a+v+2*enlargedGaps gs≤ssCount w+2 := by
  obtain ⟨a,gs,hw⟩ := word_gap_representation w
  have hgs : gs≠[] := by
    intro hnil
    apply not_p2_all_A a
    simpa [hw,hnil,gapWord] using hP
  obtain ⟨inner,v,hinner⟩ := nonempty_last gs hgs
  rw [hinner] at hw
  refine ⟨a,v,inner,hw,?_,?_⟩
  · rw [hw] at hP ⊢
    exact exact_word_budget a v inner hP.1
  · rw [hw] at hP hno ⊢
    exact enlarged_gap_budget a v inner hP.1 hno

theorem gapWord_first_S? (a : Nat) (g : Nat) (gs : List Nat) :
    (gapWord a (g :: gs))[a]? = some false := by
  simp [gapWord]

theorem leading_run_eq_gap_a (k : Nat) (rest : List Bool)
    (a v : Nat) (gs : List Nat)
    (hw : List.replicate k true ++ false :: rest = gapWord a (gs ++ [v])) :
    a = k := by
  have hleftA (i : Nat) (hi : i < k) :
      (List.replicate k true ++ false :: rest)[i]? = some true := by
    have hilen : i < (List.replicate k true).length := by simpa using hi
    rw [List.getElem?_append_left hilen, List.getElem?_replicate]
    simp [hi]
  have hleftS : (List.replicate k true ++ false :: rest)[k]? = some false := by
    simp
  have hrightA (g : Nat) (gs' : List Nat) (i : Nat) (hi : i < a) :
      (gapWord a (g :: gs'))[i]? = some true := by
    have hilen : i < (List.replicate a true).length := by simpa using hi
    simp only [gapWord]
    rw [List.getElem?_append_left hilen, List.getElem?_replicate]
    simp [hi]
  have hidx := congrArg (fun w : List Bool => w[a]?) hw
  have hkdx := congrArg (fun w : List Bool => w[k]?) hw
  cases gs with
  | nil =>
    simp only [List.nil_append] at hw hidx hkdx
    have hS : (gapWord a [v])[a]? = some false := gapWord_first_S? a v []
    by_cases hlt : a < k
    · have hA := hleftA a hlt
      have : some true = some false := hA.symm.trans (hidx.trans hS)
      cases this
    · by_cases hgt : k < a
      · have hA := hrightA v [] k hgt
        have : some false = some true := hleftS.symm.trans (hkdx.trans hA)
        cases this
      · omega
  | cons g gs' =>
    simp only [List.cons_append] at hw hidx hkdx
    have hS : (gapWord a (g :: (gs' ++ [v])))[a]? = some false :=
      gapWord_first_S? a g (gs' ++ [v])
    by_cases hlt : a < k
    · have hA := hleftA a hlt
      have : some true = some false := hA.symm.trans (hidx.trans hS)
      cases this
    · by_cases hgt : k < a
      · have hA := hrightA g (gs' ++ [v]) k hgt
        have : some false = some true := hleftS.symm.trans (hkdx.trans hA)
        cases this
      · omega

/-- NoSAAS P2 windows with exactly two SS cannot begin with five or more
A's. Combined with E-132 (no leading AAS), the remaining leading runs
are 0, 1, 3, or 4. Orbit SS=2 has no a=4 (E-158). -/
theorem aaaa_sss_not_P2 : ¬ P2 (gapWord 4 [0, 0, 0]) := by
  unfold P2 gapWord
  decide

/-- The unique extraAs=0, zeroGaps=2, trailing-v=0 family for a=4. -/
def a4Gaps (p q r : Nat) : List Nat :=
  List.replicate p 1 ++ 0 ::
    (List.replicate q 1 ++ 0 :: (List.replicate r 1 ++ [0]))

theorem gapWeight_cons_one (gs : List Nat) :
    gapWeight (1 :: gs) = gs.length + gapWeight gs := by
  simp [gapWeight]

theorem two_gapWeight_replicate_one (n : Nat) (gs : List Nat) :
    2 * gapWeight (List.replicate n 1 ++ gs) =
      2 * n * gs.length + n * (n - 1) + 2 * gapWeight gs := by
  induction n with
  | zero => simp [gapWeight]
  | succ n ih =>
    simp [List.replicate_succ, List.cons_append, gapWeight, List.length_append,
      List.length_replicate]
    have hsplit :
        2 * ((n : Int) + gs.length + gapWeight (List.replicate n 1 ++ gs)) =
          2 * n + 2 * gs.length + 2 * gapWeight (List.replicate n 1 ++ gs) := by
      omega
    rw [hsplit, ih]
    grind

theorem gapWeight_zero_cons (gs : List Nat) :
    gapWeight (0 :: gs) = gapWeight gs := by
  simp [gapWeight]

theorem two_gapWeight_a4 (p q r : Nat) :
    2 * gapWeight (a4Gaps p q r) =
      ((p + q + r : Int) ^ 2) + 5 * p + 3 * q + r := by
  unfold a4Gaps
  have h1 := two_gapWeight_replicate_one p
    (0 :: (List.replicate q 1 ++ 0 :: (List.replicate r 1 ++ [0])))
  have h2 := two_gapWeight_replicate_one q
    (0 :: (List.replicate r 1 ++ [0]))
  have h3 := two_gapWeight_replicate_one r [0]
  simp [gapWeight_zero_cons, gapWeight, List.length_append, List.length_replicate,
    List.length_cons] at h1 h2 h3 ⊢
  rw [h3] at h2
  rw [h2] at h1
  simp [h1]
  grind

theorem a4Gaps_list_length (p q r : Nat) :
    (a4Gaps p q r).length = p + q + r + 3 := by
  simp [a4Gaps]; omega

theorem a4Gaps_sum (p q r : Nat) :
    (a4Gaps p q r).sum = p + q + r := by
  simp [a4Gaps]; omega

theorem a4_family_length (p q r : Nat) :
    (gapWord 4 (a4Gaps p q r)).length = 2 * (p + q + r) + 7 := by
  simp [gapWord_length, a4Gaps_list_length, a4Gaps_sum]
  omega

theorem twice_moment_a4_family (p q r : Nat) :
    2 * moment (gapWord 4 (a4Gaps p q r)) =
      -16 - 10 * p - 6 * q - 2 * r := by
  have hM := gapWord_moment 4 (a4Gaps p q r)
  have hW := two_gapWeight_a4 p q r
  have hl := a4_family_length p q r
  have hlen := a4Gaps_list_length p q r
  rw [hl, hlen] at hM
  grind

theorem a4_family_not_P2 (p q r : Nat) :
    ¬ P2 (gapWord 4 (a4Gaps p q r)) := by
  intro h
  have hM := twice_moment_a4_family p q r
  have : moment (gapWord 4 (a4Gaps p q r)) = 0 := h.2
  omega

def a5Gaps (p q r s : Nat) : List Nat :=
  List.replicate p 1 ++ 0 ::
    (List.replicate q 1 ++ 0 ::
      (List.replicate r 1 ++ 0 :: (List.replicate s 1 ++ [0])))

theorem two_gapWeight_a5 (p q r s : Nat) :
    2 * gapWeight (a5Gaps p q r s) =
      ((p + q + r + s : Int) ^ 2) + 7 * p + 5 * q + 3 * r + s := by
  unfold a5Gaps
  have h1 := two_gapWeight_replicate_one p
    (0 :: (List.replicate q 1 ++ 0 ::
      (List.replicate r 1 ++ 0 :: (List.replicate s 1 ++ [0]))))
  have h2 := two_gapWeight_replicate_one q
    (0 :: (List.replicate r 1 ++ 0 :: (List.replicate s 1 ++ [0])))
  have h3 := two_gapWeight_replicate_one r
    (0 :: (List.replicate s 1 ++ [0]))
  have h4 := two_gapWeight_replicate_one s [0]
  simp [gapWeight_zero_cons, gapWeight, List.length_append, List.length_replicate,
    List.length_cons] at h1 h2 h3 h4 ⊢
  rw [h4] at h3
  rw [h3] at h2
  rw [h2] at h1
  simp [h1]
  grind

theorem a5Gaps_list_length (p q r s : Nat) :
    (a5Gaps p q r s).length = p + q + r + s + 4 := by
  simp [a5Gaps]; omega

theorem a5Gaps_sum (p q r s : Nat) :
    (a5Gaps p q r s).sum = p + q + r + s := by
  simp [a5Gaps]; omega

theorem a5_family_length (p q r s : Nat) :
    (gapWord 5 (a5Gaps p q r s)).length = 2 * (p + q + r + s) + 9 := by
  simp [gapWord_length, a5Gaps_list_length, a5Gaps_sum]
  omega

theorem twice_moment_a5_family (p q r s : Nat) :
    2 * moment (gapWord 5 (a5Gaps p q r s)) =
      -30 - 14 * p - 10 * q - 6 * r - 2 * s := by
  have hM := gapWord_moment 5 (a5Gaps p q r s)
  have hW := two_gapWeight_a5 p q r s
  have hl := a5_family_length p q r s
  have hlen := a5Gaps_list_length p q r s
  rw [hl, hlen] at hM
  grind

theorem a5_family_not_P2 (p q r s : Nat) :
    ¬ P2 (gapWord 5 (a5Gaps p q r s)) := by
  intro h
  have hM := twice_moment_a5_family p q r s
  have : moment (gapWord 5 (a5Gaps p q r s)) = 0 := h.2
  omega

theorem extraAs_cons (g : Nat) (gs : List Nat) :
    extraAs (g :: gs) = (g - 1) + extraAs gs := by
  simp [extraAs]

theorem extraAs_zero_le_one {gs : List Nat} (h : extraAs gs = 0) :
    ∀ g ∈ gs, g ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [extraAs_cons] at h
    intro x hx
    rcases List.mem_cons.mp hx with heq | hm
    · have : g ≤ 1 := by omega
      simpa [heq] using this
    · exact ih (by omega) x hm

theorem zeroGaps_cons (g : Nat) (gs : List Nat) :
    zeroGaps (g :: gs) = (if g = 0 then 1 else 0) + zeroGaps gs := by
  unfold zeroGaps
  by_cases hg : g = 0 <;> simp [hg, List.filter_cons] <;> omega

theorem zeroGaps_zero_replicate_one {gs : List Nat}
    (hle : ∀ g ∈ gs, g ≤ 1) (hz : zeroGaps gs = 0) :
    gs = List.replicate gs.length 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : g ≤ 1 := hle g (by simp)
    have hg1 : g = 1 := by
      have hg0 : g ≠ 0 := by
        intro h0
        subst g
        rw [zeroGaps_cons] at hz
        simp at hz
      omega
    subst hg1
    have hz' : zeroGaps gs = 0 := by
      rw [zeroGaps_cons] at hz
      simpa using hz
    have ih := ih (fun x hx => hle x (List.mem_cons_of_mem 1 hx)) hz'
    rw [ih]
    simp [List.length_cons, List.replicate_succ]

theorem replicate_ones_split {gs : List Nat} (hle : ∀ g ∈ gs, g ≤ 1) :
    ∃ n rest, gs = List.replicate n 1 ++ rest ∧
      (rest = [] ∨ rest.head? = some 0) := by
  induction gs with
  | nil => exact ⟨0, [], by simp, Or.inl rfl⟩
  | cons g gs ih =>
    have hg : g ≤ 1 := hle g (by simp)
    obtain ⟨n, rest, heq, hrest⟩ := ih (fun x hx => hle x (by simp [hx]))
    if hg0 : g = 0 then
      exact ⟨0, g :: gs, by simp, by simp [hg0]⟩
    else
      have hg1 : g = 1 := by omega
      subst hg1
      exact ⟨n + 1, rest, by simp [heq, List.replicate_succ], hrest⟩

theorem zeroGaps_append_ones (n : Nat) (gs : List Nat) :
    zeroGaps (List.replicate n 1 ++ gs) = zeroGaps gs := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, List.cons_append, zeroGaps_cons, ih]

theorem two_zero_gaps_form {gs : List Nat}
    (hle : ∀ g ∈ gs, g ≤ 1) (hz : zeroGaps gs = 2) :
    ∃ p q r, gs = List.replicate p 1 ++ 0 ::
      (List.replicate q 1 ++ 0 :: List.replicate r 1) := by
  obtain ⟨p, rest, hp, hrest⟩ := replicate_ones_split hle
  if hnil : rest = [] then
    subst rest
    rw [hp, zeroGaps_append_ones] at hz
    simp [zeroGaps] at hz
  else
    have h0 : rest.head? = some 0 := by
      cases hrest with
      | inl h => exact False.elim (hnil h)
      | inr h => exact h
    have ⟨x, rest1, hx⟩ : ∃ x rest1, rest = x :: rest1 := by
      match rest with
      | [] => exact False.elim (hnil rfl)
      | x :: rest1 => exact ⟨x, rest1, rfl⟩
    have hx0 : x = 0 := by
      simp [hx] at h0
      exact h0
    subst x
    have hle1 : ∀ g ∈ rest1, g ≤ 1 := fun g hg => hle g (by simp [hp, hx, hg])
    obtain ⟨q, rest2, hq, hrest2⟩ := replicate_ones_split hle1
    if hnil2 : rest2 = [] then
      subst rest2
      have : zeroGaps gs = 1 := by
        rw [hp, hx, hq, zeroGaps_append_ones, zeroGaps_cons, zeroGaps_append_ones]
        simp [zeroGaps]
      omega
    else
      have h02 : rest2.head? = some 0 := by
        cases hrest2 with
        | inl h => exact False.elim (hnil2 h)
        | inr h => exact h
      have ⟨y, rest3, hy⟩ : ∃ y rest3, rest2 = y :: rest3 := by
        match rest2 with
        | [] => exact False.elim (hnil2 rfl)
        | y :: rest3 => exact ⟨y, rest3, rfl⟩
      have hy0 : y = 0 := by
        simp [hy] at h02
        exact h02
      subst y
      have hle3 : ∀ g ∈ rest3, g ≤ 1 := fun g hg =>
        hle g (by simp [hp, hx, hq, hy, hg])
      have hz0 : zeroGaps rest3 = 0 := by
        have h1 : zeroGaps gs =
            zeroGaps (0 :: (List.replicate q 1 ++ 0 :: rest3)) := by
          rw [hp, hx, hq, hy, zeroGaps_append_ones]
        have h2 : zeroGaps (0 :: (List.replicate q 1 ++ 0 :: rest3)) =
            1 + zeroGaps (List.replicate q 1 ++ 0 :: rest3) := by
          rw [zeroGaps_cons]; simp
        have h3 : zeroGaps (List.replicate q 1 ++ 0 :: rest3) =
            zeroGaps (0 :: rest3) := zeroGaps_append_ones q _
        have h4 : zeroGaps (0 :: rest3) = 1 + zeroGaps rest3 := by
          rw [zeroGaps_cons]; simp
        omega
      have hones := zeroGaps_zero_replicate_one hle3 hz0
      refine ⟨p, q, rest3.length, ?_⟩
      rw [hp, hx, hq, hy, hones]
      simp [List.length_replicate]

theorem three_zero_gaps_form {gs : List Nat}
    (hle : ∀ g ∈ gs, g ≤ 1) (hz : zeroGaps gs = 3) :
    ∃ p q r s, gs = List.replicate p 1 ++ 0 ::
      (List.replicate q 1 ++ 0 ::
        (List.replicate r 1 ++ 0 :: List.replicate s 1)) := by
  obtain ⟨p, rest, hp, hrest⟩ := replicate_ones_split hle
  if hnil : rest = [] then
    subst rest
    rw [hp, zeroGaps_append_ones] at hz
    simp [zeroGaps] at hz
  else
    have h0 : rest.head? = some 0 := by
      cases hrest with
      | inl h => exact False.elim (hnil h)
      | inr h => exact h
    have ⟨x, rest1, hx⟩ : ∃ x rest1, rest = x :: rest1 := by
      match rest with
      | [] => exact False.elim (hnil rfl)
      | x :: rest1 => exact ⟨x, rest1, rfl⟩
    have hx0 : x = 0 := by
      simp [hx] at h0
      exact h0
    subst x
    have hle1 : ∀ g ∈ rest1, g ≤ 1 := fun g hg => hle g (by simp [hp, hx, hg])
    have hz1 : zeroGaps rest1 = 2 := by
      have h1 : zeroGaps gs = 1 + zeroGaps rest1 := by
        rw [hp, hx, zeroGaps_append_ones, zeroGaps_cons]
        simp
      omega
    obtain ⟨q, r, s, hgs1⟩ := two_zero_gaps_form hle1 hz1
    exact ⟨p, q, r, s, by simp [hp, hx, hgs1]⟩

theorem a5Gaps_of_three_zeros {gs : List Nat} {p q r s : Nat}
    (hgs : gs = List.replicate p 1 ++ 0 ::
      (List.replicate q 1 ++ 0 ::
        (List.replicate r 1 ++ 0 :: List.replicate s 1))) :
    gs ++ [0] = a5Gaps p q r s := by
  simp [hgs, a5Gaps]

theorem noSAAS_ss3_not_lead_five (rest : List Bool)
    (hP : P2 (List.replicate 5 true ++ false :: rest))
    (hss : ssCount (List.replicate 5 true ++ false :: rest) = 3)
    (hno : NoSAAS (List.replicate 5 true ++ false :: rest)) : False := by
  obtain ⟨a, v, gs, hw, hexact, hbud⟩ := every_P2_budget _ hP hno
  have ha : a = 5 := leading_run_eq_gap_a 5 rest a v gs hw
  subst ha
  rw [hss] at hexact hbud
  have hv : v = 0 := by omega
  have hE : extraAs gs = 0 := by omega
  subst v
  have hle := extraAs_zero_le_one hE
  have hz : zeroGaps gs = 3 := by
    have hssg := ssCount_gapWord 5 0 gs
    rw [← hw] at hssg
    omega
  obtain ⟨p, q, r, s, hgs⟩ := three_zero_gaps_form hle hz
  have hfull := a5Gaps_of_three_zeros hgs
  have hw' : List.replicate 5 true ++ false :: rest =
      gapWord 5 (a5Gaps p q r s) := by
    rw [← hfull, hw]
  exact a5_family_not_P2 p q r s (hw' ▸ hP)

theorem noSAAS_ss3_leading_run_lt_five (k : Nat) (rest : List Bool)
    (hk : 5 ≤ k)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = 3)
    (hno : NoSAAS (List.replicate k true ++ false :: rest)) : False := by
  have hcases : k = 5 ∨ 6 ≤ k := by omega
  rcases hcases with rfl | h6
  · exact noSAAS_ss3_not_lead_five rest hP hss hno
  · obtain ⟨a, v, gs, hw, _, hbud⟩ := every_P2_budget _ hP hno
    have ha : a = k := leading_run_eq_gap_a k rest a v gs hw
    rw [ha, hss] at hbud
    omega

theorem a4Gaps_of_two_zeros {gs : List Nat} {p q r : Nat}
    (hgs : gs = List.replicate p 1 ++ 0 ::
      (List.replicate q 1 ++ 0 :: List.replicate r 1)) :
    gs ++ [0] = a4Gaps p q r := by
  simp [hgs, a4Gaps]

theorem noSAAS_ss2_not_lead_four (rest : List Bool)
    (hP : P2 (List.replicate 4 true ++ false :: rest))
    (hss : ssCount (List.replicate 4 true ++ false :: rest) = 2)
    (hno : NoSAAS (List.replicate 4 true ++ false :: rest)) : False := by
  obtain ⟨a, v, gs, hw, hexact, hbud⟩ := every_P2_budget _ hP hno
  have ha : a = 4 := leading_run_eq_gap_a 4 rest a v gs hw
  subst ha
  rw [hss] at hexact hbud
  have hv : v = 0 := by omega
  have hE : extraAs gs = 0 := by omega
  subst v
  have hle := extraAs_zero_le_one hE
  have hz : zeroGaps gs = 2 := by
    have hssg := ssCount_gapWord 4 0 gs
    rw [← hw] at hssg
    omega
  obtain ⟨p, q, r, hgs⟩ := two_zero_gaps_form hle hz
  have hfull := a4Gaps_of_two_zeros hgs
  have hw' : List.replicate 4 true ++ false :: rest =
      gapWord 4 (a4Gaps p q r) := by
    rw [← hfull, hw]
  exact a4_family_not_P2 p q r (hw' ▸ hP)

theorem noSAAS_ss2_leading_lt_five (k : Nat) (rest : List Bool) (hk : 5 ≤ k)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = 2)
    (hno : NoSAAS (List.replicate k true ++ false :: rest)) : False := by
  obtain ⟨a, v, gs, hw, _, hbud⟩ :=
    every_P2_budget _ hP hno
  have ha : a = k := leading_run_eq_gap_a k rest a v gs hw
  rw [ha, hss] at hbud
  omega

theorem noSAAS_ss2_leading_run_lt_four (k : Nat) (rest : List Bool)
    (hk : 4 ≤ k)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = 2)
    (hno : NoSAAS (List.replicate k true ++ false :: rest)) : False := by
  have hcases : k = 4 ∨ 5 ≤ k := by omega
  rcases hcases with rfl | h5
  · exact noSAAS_ss2_not_lead_four rest hP hss hno
  · exact noSAAS_ss2_leading_lt_five k rest h5 hP hss hno

/-- E-126 specialises to a leading-run bound: `a ≤ ssCount+2`. -/
theorem noSAAS_p2_leading_le_ssCount (k : Nat) (rest : List Bool) (n : Nat)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = n)
    (hno : NoSAAS (List.replicate k true ++ false :: rest)) :
    k ≤ n + 2 := by
  obtain ⟨a, v, gs, hw, _, hbud⟩ := every_P2_budget _ hP hno
  have ha : a = k := leading_run_eq_gap_a k rest a v gs hw
  rw [ha, hss] at hbud
  omega

theorem drop_cons_of_get (w : List Bool) (k : Nat) (x : Bool)
    (hk : k < w.length) (h : w[k]'(hk) = x) :
    ∃ rest, w.drop k = x :: rest := by
  cases hdrop : w.drop k with
  | nil =>
    have : w.length ≤ k := (List.drop_eq_nil_iff).mp hdrop
    omega
  | cons b rest =>
    have hb : b = x := by
      have hgot := List.getElem_drop (xs := w) (i := k) (j := 0)
        (h := by simp [hdrop])
      simp [hdrop] at hgot
      exact hgot.trans h
    refine ⟨rest, ?_⟩
    rw [hb]

theorem noSAAS_ss2_prefix_A_run (w : List Bool) (k : Nat)
    (hk : 4 ≤ k) (hkl : k < w.length)
    (hA : ∀ i : Nat, (hi : i < k) → w[i]'(Nat.lt_trans hi hkl) = true)
    (hS : w[k]'(hkl) = false)
    (hP : P2 w) (hss : ssCount w = 2) (hno : NoSAAS w) : False := by
  have htake := take_leading w k (Nat.le_of_lt hkl) (fun i hi => hA i hi)
  have hsplit := (List.take_append_drop k w).symm
  obtain ⟨rest, hrest⟩ := drop_cons_of_get w k false hkl hS
  have hw : w = List.replicate k true ++ false :: rest := by
    rw [hsplit, htake, hrest]
  rw [hw] at hP hss hno
  exact noSAAS_ss2_leading_run_lt_four k rest hk hP hss hno

theorem noSAAS_premise_control :
    mass (gapWord 1 [2,0])=1 ∧ ¬ NoSAAS (gapWord 1 [2,0]) ∧
      ssCount (gapWord 1 [2,0])+2 < 1+0+2*enlargedGaps [2] := by
  refine ⟨by decide,?_,by decide⟩
  intro h
  exact h [true] [] rfl

/-- Mass-1 P2 words that contain an S have an exact extraAs budget.
The enlarged-gap inequality is the only part of `every_P2_budget` that
needs NoSAAS; the equality does not. -/
theorem every_P2_exact (w : List Bool) (hP : P2 w) :
    ∃ a v gs, w = gapWord a (gs ++ [v]) ∧
      a + v + extraAs gs = ssCount w + 2 := by
  obtain ⟨a, gs, hw⟩ := word_gap_representation w
  have hgs : gs ≠ [] := by
    intro hnil
    apply not_p2_all_A a
    simpa [hw, hnil, gapWord] using hP
  obtain ⟨inner, v, hinner⟩ := nonempty_last gs hgs
  rw [hinner] at hw
  refine ⟨a, v, inner, hw, ?_⟩
  rw [hw] at hP ⊢
  exact exact_word_budget a v inner hP.1

/-- Leading A-run of a P2 word is at most `ssCount+2`. NoSAAS is not used. -/
theorem p2_leading_le_ssCount (k : Nat) (rest : List Bool) (n : Nat)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = n) :
    k ≤ n + 2 := by
  obtain ⟨a, v, gs, hw, hexact⟩ := every_P2_exact _ hP
  have ha : a = k := leading_run_eq_gap_a k rest a v gs hw
  rw [ha, hss] at hexact
  omega

theorem ss2_not_lead_four (rest : List Bool)
    (hP : P2 (List.replicate 4 true ++ false :: rest))
    (hss : ssCount (List.replicate 4 true ++ false :: rest) = 2) : False := by
  obtain ⟨a, v, gs, hw, hexact⟩ := every_P2_exact _ hP
  have ha : a = 4 := leading_run_eq_gap_a 4 rest a v gs hw
  subst ha
  rw [hss] at hexact
  have hv : v = 0 := by omega
  have hE : extraAs gs = 0 := by omega
  subst v
  have hle := extraAs_zero_le_one hE
  have hz : zeroGaps gs = 2 := by
    have hssg := ssCount_gapWord 4 0 gs
    rw [← hw] at hssg
    omega
  obtain ⟨p, q, r, hgs⟩ := two_zero_gaps_form hle hz
  have hfull := a4Gaps_of_two_zeros hgs
  have hw' : List.replicate 4 true ++ false :: rest =
      gapWord 4 (a4Gaps p q r) := by
    rw [← hfull, hw]
  exact a4_family_not_P2 p q r (hw' ▸ hP)

theorem ss2_leading_lt_five (k : Nat) (rest : List Bool) (hk : 5 ≤ k)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = 2) : False := by
  obtain ⟨a, v, gs, hw, hexact⟩ := every_P2_exact _ hP
  have ha : a = k := leading_run_eq_gap_a k rest a v gs hw
  rw [ha, hss] at hexact
  omega

theorem ss2_leading_run_lt_four (k : Nat) (rest : List Bool)
    (hk : 4 ≤ k)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = 2) : False := by
  have hcases : k = 4 ∨ 5 ≤ k := by omega
  rcases hcases with rfl | h5
  · exact ss2_not_lead_four rest hP hss
  · exact ss2_leading_lt_five k rest h5 hP hss

theorem ss2_prefix_A_run (w : List Bool) (k : Nat)
    (hk : 4 ≤ k) (hkl : k < w.length)
    (hA : ∀ i : Nat, (hi : i < k) → w[i]'(Nat.lt_trans hi hkl) = true)
    (hS : w[k]'(hkl) = false)
    (hP : P2 w) (hss : ssCount w = 2) : False := by
  have htake := take_leading w k (Nat.le_of_lt hkl) (fun i hi => hA i hi)
  have hsplit := (List.take_append_drop k w).symm
  obtain ⟨rest, hrest⟩ := drop_cons_of_get w k false hkl hS
  have hw : w = List.replicate k true ++ false :: rest := by
    rw [hsplit, htake, hrest]
  rw [hw] at hP hss
  exact ss2_leading_run_lt_four k rest hk hP hss

theorem ss3_not_lead_five (rest : List Bool)
    (hP : P2 (List.replicate 5 true ++ false :: rest))
    (hss : ssCount (List.replicate 5 true ++ false :: rest) = 3) : False := by
  obtain ⟨a, v, gs, hw, hexact⟩ := every_P2_exact _ hP
  have ha : a = 5 := leading_run_eq_gap_a 5 rest a v gs hw
  subst ha
  rw [hss] at hexact
  have hv : v = 0 := by omega
  have hE : extraAs gs = 0 := by omega
  subst v
  have hle := extraAs_zero_le_one hE
  have hz : zeroGaps gs = 3 := by
    have hssg := ssCount_gapWord 5 0 gs
    rw [← hw] at hssg
    omega
  obtain ⟨p, q, r, s, hgs⟩ := three_zero_gaps_form hle hz
  have hfull := a5Gaps_of_three_zeros hgs
  have hw' : List.replicate 5 true ++ false :: rest =
      gapWord 5 (a5Gaps p q r s) := by
    rw [← hfull, hw]
  exact a5_family_not_P2 p q r s (hw' ▸ hP)

theorem ss3_leading_run_lt_five (k : Nat) (rest : List Bool)
    (hk : 5 ≤ k)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = 3) : False := by
  have hcases : k = 5 ∨ 6 ≤ k := by omega
  rcases hcases with rfl | h6
  · exact ss3_not_lead_five rest hP hss
  · obtain ⟨a, v, gs, hw, hexact⟩ := every_P2_exact _ hP
    have ha : a = k := leading_run_eq_gap_a k rest a v gs hw
    rw [ha, hss] at hexact
    omega

/-- `{0,1}`-gap lists with a trailing 0, one one-run per zero. Nonempty
`ps` gives mass 1 when the leading A-run is `ps.length+1`. -/
def eqGaps : List Nat → List Nat
  | [] => [0]
  | p :: [] => List.replicate p 1 ++ [0]
  | p :: q :: ps => List.replicate p 1 ++ 0 :: eqGaps (q :: ps)

def eqOddSum : List Nat → Int
  | [] => 0
  | p :: ps => (2 * ((ps.length : Int) + 1) - 1) * (p : Int) + eqOddSum ps

theorem eqGaps_ne_nil (ps : List Nat) : eqGaps ps ≠ [] := by
  cases ps with
  | nil => simp [eqGaps]
  | cons p ps =>
    cases ps with
    | nil => simp [eqGaps]
    | cons q ps => simp [eqGaps]

theorem eqGaps_length : ∀ ps : List Nat, ps ≠ [] →
    (eqGaps ps).length = ps.sum + ps.length
  | [], h => (h rfl).elim
  | [p], _ => by simp [eqGaps]
  | p :: q :: ps, _ => by
      have ih := eqGaps_length (q :: ps) (by simp)
      simp [eqGaps, ih, List.sum_cons]
      omega

theorem eqGaps_sum : ∀ ps : List Nat, ps ≠ [] →
    (eqGaps ps).sum = ps.sum
  | [], h => (h rfl).elim
  | [p], _ => by simp [eqGaps]
  | p :: q :: ps, _ => by
      have ih := eqGaps_sum (q :: ps) (by simp)
      simp [eqGaps, ih, List.sum_cons]

theorem eqGaps_a4 (p q r : Nat) : eqGaps [p, q, r] = a4Gaps p q r := by
  simp [eqGaps, a4Gaps]

theorem eqGaps_a5 (p q r s : Nat) : eqGaps [p, q, r, s] = a5Gaps p q r s := by
  simp [eqGaps, a5Gaps]

theorem eqOddSum_nonneg (ps : List Nat) : 0 ≤ eqOddSum ps := by
  induction ps with
  | nil => simp [eqOddSum]
  | cons p ps ih =>
    simp only [eqOddSum]
    have hcoeff : 0 ≤ 2 * ((ps.length : Int) + 1) - 1 := by omega
    have hp : 0 ≤ (p : Int) := Int.natCast_nonneg p
    have hmul : 0 ≤ (2 * ((ps.length : Int) + 1) - 1) * (p : Int) :=
      Int.mul_nonneg hcoeff hp
    omega

theorem int_add_sq (x y : Int) :
    (x + y) * (x + y) = x * x + 2 * x * y + y * y := by
  simp [Int.add_mul, Int.mul_add, Int.mul_comm y x]
  grind

theorem int_sub_one_mul (p : Int) : p * (p - 1) = p * p - p := by
  simp [Int.mul_sub]

/-- The length/weight combination that appears in `gapWord_moment` for the
equality family. -/
theorem eq_family_core (m S : Int) :
    (2 * S + 2 * m + 1) * (2 * S + 2 * m + 2)
      - 2 * (S + m) * (2 * (m + 1) + (S + m) + 1)
    = 2 * S * S + 2 - 2 * m * m := by
  grind

theorem two_gapWeight_eqGaps : ∀ ps : List Nat, ps ≠ [] →
    2 * gapWeight (eqGaps ps) =
      (ps.sum : Int) * ps.sum + eqOddSum ps
  | [], h => (h rfl).elim
  | [p], _ => by
      have h1 := two_gapWeight_replicate_one p [0]
      simp [eqGaps, eqOddSum, gapWeight] at h1 ⊢
      have hp := int_sub_one_mul (p : Int)
      grind
  | p :: q :: ps, _ => by
      have ih := two_gapWeight_eqGaps (q :: ps) (by simp)
      have hlen := eqGaps_length (q :: ps) (by simp)
      have h1 := two_gapWeight_replicate_one p (0 :: eqGaps (q :: ps))
      simp [eqGaps, gapWeight_zero_cons, List.length_cons] at h1 ⊢
      rw [hlen] at h1
      rw [h1, ih]
      simp only [eqOddSum, List.sum_cons, List.length_cons]
      have hsq := int_add_sq (p : Int) ((q :: ps).sum : Int)
      have hp := int_sub_one_mul (p : Int)
      grind

theorem twice_moment_eqGaps (ps : List Nat) (hps : ps ≠ []) :
    2 * moment (gapWord (ps.length + 1) (eqGaps ps)) =
      -2 * ((ps.length : Int) * ps.length - 1) - 2 * eqOddSum ps := by
  have hW := two_gapWeight_eqGaps ps hps
  have hl := eqGaps_length ps hps
  have hs := eqGaps_sum ps hps
  have hM := gapWord_moment (ps.length + 1) (eqGaps ps)
  have hlen := gapWord_length (ps.length + 1) (eqGaps ps)
  rw [hlen, hl, hs] at hM
  have hcore := eq_family_core (ps.length : Int) (ps.sum : Int)
  grind

theorem eqGaps_not_P2 (ps : List Nat) (h : 2 ≤ ps.length) :
    ¬ P2 (gapWord (ps.length + 1) (eqGaps ps)) := by
  intro hP
  have hne : ps ≠ [] := by intro hnil; simp [hnil] at h
  have hM := twice_moment_eqGaps ps hne
  have hmom : moment (gapWord (ps.length + 1) (eqGaps ps)) = 0 := hP.2
  have hpen := eqOddSum_nonneg ps
  have hmul : 4 ≤ ps.length * ps.length := Nat.mul_le_mul h h
  have hsq : (4 : Int) ≤ (ps.length : Int) * ps.length := by
    have := (Int.ofNat_le).mpr hmul
    simpa [Int.natCast_mul] using this
  omega

theorem extraAs_zero_to_eqGaps {gs : List Nat}
    (hle : ∀ g ∈ gs, g ≤ 1) (hn : 1 ≤ zeroGaps gs) :
    ∃ ps, gs ++ [0] = eqGaps ps ∧ ps.length = zeroGaps gs + 1 ∧ 2 ≤ ps.length := by
  obtain ⟨p, rest, hp, hrest⟩ := replicate_ones_split hle
  have hrest0 : rest ≠ [] := by
    intro hnil
    subst rest
    have : zeroGaps gs = 0 := by
      rw [hp, zeroGaps_append_ones]
      simp [zeroGaps]
    omega
  have h0 : rest.head? = some 0 := by
    cases hrest with
    | inl h => exact False.elim (hrest0 h)
    | inr h => exact h
  have ⟨x, rest1, hx⟩ : ∃ x rest1, rest = x :: rest1 := by
    match rest with
    | [] => exact False.elim (hrest0 rfl)
    | x :: rest1 => exact ⟨x, rest1, rfl⟩
  have hx0 : x = 0 := by
    simp [hx] at h0
    exact h0
  subst x
  have hle1 : ∀ g ∈ rest1, g ≤ 1 := fun g hg => hle g (by simp [hp, hx, hg])
  have hzgs : zeroGaps gs = 1 + zeroGaps rest1 := by
    rw [hp, hx, zeroGaps_append_ones, zeroGaps_cons]
    simp
  if hz0 : zeroGaps rest1 = 0 then
    have hones := zeroGaps_zero_replicate_one hle1 hz0
    refine ⟨[p, rest1.length], ?_, ?_, by simp⟩
    · rw [hp, hx, hones]
      simp [eqGaps, List.append_assoc]
    · rw [hzgs, hz0]
      simp
  else
    have hn1 : 1 ≤ zeroGaps rest1 := by omega
    obtain ⟨ps, hps, hlen, h2⟩ := extraAs_zero_to_eqGaps (gs := rest1) hle1 hn1
    have hpsne : ps ≠ [] := by intro hnil; simp [hnil] at h2
    refine ⟨p :: ps, ?_, ?_, ?_⟩
    · have hcons :
          eqGaps (p :: ps) = List.replicate p 1 ++ 0 :: eqGaps ps := by
        match ps with
        | [] => exact (hpsne rfl).elim
        | q :: qs => rfl
      have hadd :
          (List.replicate p 1 ++ 0 :: rest1) ++ [0] =
            List.replicate p 1 ++ 0 :: (rest1 ++ [0]) := by
        simp [List.append_assoc]
      rw [hp, hx, hadd, hps, hcons]
    · rw [hzgs, List.length_cons, hlen]
      omega
    · exact Nat.le_succ_of_le h2
termination_by gs.length
decreasing_by
  simp [hp, hx]
  omega

theorem ss_eq_family_not_P2 (n : Nat) (rest : List Bool) (hn : 1 ≤ n)
    (hP : P2 (List.replicate (n + 2) true ++ false :: rest))
    (hss : ssCount (List.replicate (n + 2) true ++ false :: rest) = n) :
    False := by
  obtain ⟨a, v, gs, hw, hexact⟩ := every_P2_exact _ hP
  have ha : a = n + 2 := leading_run_eq_gap_a (n + 2) rest a v gs hw
  subst ha
  rw [hss] at hexact
  have hv : v = 0 := by omega
  have hE : extraAs gs = 0 := by omega
  subst v
  have hle := extraAs_zero_le_one hE
  have hz : zeroGaps gs = n := by
    have hssg := ssCount_gapWord (n + 2) 0 gs
    rw [← hw] at hssg
    omega
  have hn1 : 1 ≤ zeroGaps gs := by omega
  obtain ⟨ps, hgs, hlen, h2⟩ := extraAs_zero_to_eqGaps hle hn1
  have hw' : List.replicate (n + 2) true ++ false :: rest =
      gapWord (ps.length + 1) (eqGaps ps) := by
    have : n + 2 = ps.length + 1 := by omega
    rw [hw, this, hgs]
  exact eqGaps_not_P2 ps h2 (hw' ▸ hP)

/-- For SS≥1, a P2 window cannot open with `ssCount+2` leading A's.
SS=0 still allows AAS (E-168 equality with n=0). -/
theorem p2_leading_le_ssCount_succ (k : Nat) (rest : List Bool) (n : Nat)
    (hn : 1 ≤ n)
    (hP : P2 (List.replicate k true ++ false :: rest))
    (hss : ssCount (List.replicate k true ++ false :: rest) = n) :
    k ≤ n + 1 := by
  have hle := p2_leading_le_ssCount k rest n hP hss
  have hcases : k ≤ n + 1 ∨ k = n + 2 := by omega
  rcases hcases with h | rfl
  · exact h
  · exact (ss_eq_family_not_P2 n rest hn hP hss).elim

end Recaman.SSGapBudget
