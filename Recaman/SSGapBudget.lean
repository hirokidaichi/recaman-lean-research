import Recaman.OneSSMultiplicity

namespace Recaman.SSGapBudget

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

theorem noSAAS_premise_control :
    mass (gapWord 1 [2,0])=1 ∧ ¬ NoSAAS (gapWord 1 [2,0]) ∧
      ssCount (gapWord 1 [2,0])+2 < 1+0+2*enlargedGaps [2] := by
  refine ⟨by decide,?_,by decide⟩
  intro h
  exact h [true] [] rfl

end Recaman.SSGapBudget
