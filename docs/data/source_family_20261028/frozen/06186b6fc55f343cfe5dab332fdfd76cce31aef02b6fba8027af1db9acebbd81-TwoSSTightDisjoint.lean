import Recaman.TwoSSPeriodicSupply
import Recaman.TwoSSEndpoint

/-!
# TwoSSTightDisjoint

Tight subset obstruction and strict neighborhood expansion for SS=2 windows
-/

namespace Recaman.TwoSSTightDisjoint

open TwoSSPeriodicSupply TwoSSEndpoint LeadingRunSupply EndpointRepetitionBudget OneSSMultiplicity

/-- A window at `u` with lag `d` covers subtraction phase `s` modulo `p`. -/
def WindowCoversSubtraction (e : Int → Bool) (p : Nat) (u : Int) (d : Nat) (s : Nat) : Prop :=
  ∃ i : Nat, i < d ∧ e (u - 1 - (i : Int)) = false ∧ (u - 1 - (i : Int)) % (p : Int) = (s : Int)

/-- Decidable test for whether window at `u` with lag `d` covers subtraction phase `s`. -/
def isCoveredByWindow (e : Int → Bool) (p : Nat) (u : Int) (d : Nat) (s : Nat) : Bool :=
  (List.range d).any (fun i => decide (e (u - 1 - (i : Int)) = false) && decide ((u - 1 - (i : Int)) % (p : Int) = (s : Int)))

/-- Decidable test for whether a subset of additions `A` covers subtraction phase `s`. -/
def isCoveredBySubset (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat) : Bool :=
  A.any (fun u => isCoveredByWindow e p (u : Int) (lag u) s)

/-- Exact equivalence between boolean tester and proposition for window coverage. -/
theorem isCoveredByWindow_iff (e : Int → Bool) (p : Nat) (u : Int) (d : Nat) (s : Nat) :
    isCoveredByWindow e p u d s = true ↔
    ∃ i : Nat, i < d ∧ e (u - 1 - (i : Int)) = false ∧ (u - 1 - (i : Int)) % (p : Int) = (s : Int) := by
  unfold isCoveredByWindow
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hbool⟩
    rw [List.mem_range] at hi
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hbool
    exact ⟨i, hi, hbool.1, hbool.2⟩
  · rintro ⟨i, hi, he, hmod⟩
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨he, hmod⟩

/-- Exact equivalence between boolean tester and proposition for subset coverage. -/
theorem isCoveredBySubset_iff (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat) :
    isCoveredBySubset e p A lag s = true ↔
    ∃ u ∈ A, ∃ i : Nat, i < lag u ∧ e ((u : Int) - 1 - (i : Int)) = false ∧
      ((u : Int) - 1 - (i : Int)) % (p : Int) = (s : Int) := by
  unfold isCoveredBySubset
  rw [List.any_eq_true]
  constructor
  · rintro ⟨u, hu, hcov⟩
    rw [isCoveredByWindow_iff] at hcov
    exact ⟨u, hu, hcov⟩
  · rintro ⟨u, hu, hcov⟩
    refine ⟨u, hu, ?_⟩
    rw [isCoveredByWindow_iff]
    exact hcov

/-- The concrete subtraction neighborhood `N(A)` of a subset of additions `A`. -/
def neighborhood (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) : List Nat :=
  (LagElevenPeriodic.subPhases e 0 p).filter (fun s => isCoveredBySubset e p A lag s)

/-- The residual subtraction neighborhood `N(A) \ {s}` after deleting subtraction `s`. -/
def deletedNeighborhood (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat) : List Nat :=
  (neighborhood e p A lag).filter (fun y => decide (y ≠ s))

/-- Filter over a list with an identically true predicate preserves the entire list. -/
theorem filter_all_true (α : Type) (p : α → Bool) (l : List α) (hall : ∀ x ∈ l, p x = true) :
    l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = true := hall x (by simp)
    have ih' : xs.filter p = xs := ih (fun y hy => hall y (by simp [hy]))
    simp [hx, ih']

/-- Removing a single element from a nodup list reduces its length by at most 1. -/
theorem filter_ne_nodup {α : Type} [DecidableEq α] {l : List α} (hn : l.Nodup) (x : α) :
    l.length - 1 ≤ (l.filter (fun y => decide (y ≠ x))).length := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.nodup_cons] at hn
    rw [List.length_cons, List.filter_cons]
    split
    · rw [List.length_cons]
      have ih' := ih hn.2
      omega
    · rename_i heq
      have hxy : y = x := by
        apply Classical.byContradiction
        intro hc
        have : decide (y ≠ x) = true := by simp [hc]
        rw [this] at heq
        contradiction
      subst y
      have hnot : ∀ z ∈ ys, decide (z ≠ x) = true := by
        intro z hz
        have : z ≠ x := fun hzx => hn.1 (hzx ▸ hz)
        simp [this]
      have hfilt := filter_all_true α (fun y => decide (y ≠ x)) ys hnot
      rw [hfilt]
      omega

/-- Subtraction phases modulo p are strictly distinct without duplicates. -/
theorem subPhases_nodup (e : Int → Bool) (p : Nat) :
    (LagElevenPeriodic.subPhases e 0 p).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

/-- For `p ≤ 11`, if `A` contains an SS=2 window, its subtraction neighborhood
is the ENTIRE set `D = subPhases e 0 p` of subtractions. -/
theorem neighborhood_eq_subPhases_of_has_ss2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2) :
    neighborhood e p A lag = LagElevenPeriodic.subPhases e 0 p := by
  unfold neighborhood
  apply filter_all_true
  intro s hs
  rw [isCoveredBySubset_iff]
  refine ⟨u0, hu0, ?_⟩
  have hmem := (LagElevenPeriodic.mem_subPhases e 0 p s).mp hs
  have hs_lt : s < p := hmem.1
  have hs_S : e s = false := by
    have h0 : (0 : Int) + (s : Int) = (s : Int) := by omega
    have hs0 := hmem.2
    rw [h0] at hs0
    exact hs0
  exact ss2_window_covers_all_subtractions_of_p_le_eleven e p hp hp11 hper u0 (lag u0) hP hss s hs_lt hs_S

/-- For `p ≤ 11`, the neighborhood of any subset `A` containing an SS=2 window
has maximum possible capacity `|D|`. -/
theorem neighborhood_length_of_has_ss2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2) :
    (neighborhood e p A lag).length = (LagElevenPeriodic.subPhases e 0 p).length := by
  rw [neighborhood_eq_subPhases_of_has_ss2 e p hp hp11 hper A lag u0 hu0 hP hss]

/-- Strict neighborhood expansion: in any word with positive slack `|U| < |D|`,
any subset `A` containing an SS=2 window strictly expands: `|A| < |N(A)|`. -/
theorem strict_expansion_of_has_ss2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2) :
    A.length < (neighborhood e p A lag).length := by
  rw [neighborhood_length_of_has_ss2 e p hp hp11 hper A lag u0 hu0 hP hss]
  omega

/-- Main theorem of T6 tight obstruction:
In any word with positive slack, NO tight subset of additions (`|N(A)| = |A|`)
can contain an SS=2 window. -/
theorem no_tight_subset_contains_ss2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (htight : (neighborhood e p A lag).length = A.length) : False := by
  have hlt := strict_expansion_of_has_ss2 e p hp hp11 hper U A lag hAU hslack u0 hu0 hP hss
  omega

/-- Hall's condition preservation under arbitrary deletion:
In any word with positive slack, deleting ANY subtraction phase `s` preserves
Hall's condition on any subset `A` containing an SS=2 window: `|A| ≤ |N(A) \ {s}|`. -/
theorem deleted_neighborhood_hall_of_has_ss2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (s : Nat) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  unfold deletedNeighborhood
  rw [neighborhood_eq_subPhases_of_has_ss2 e p hp hp11 hper A lag u0 hu0 hP hss]
  have hfilt := filter_ne_nodup (subPhases_nodup e p) s
  omega

/-- Strict slack lower bound on any subset containing an SS=2 window. -/
theorem slack_of_has_ss2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2) :
    (LagElevenPeriodic.subPhases e 0 p).length - U.length ≤ (neighborhood e p A lag).length - A.length := by
  rw [neighborhood_length_of_has_ss2 e p hp hp11 hper A lag u0 hu0 hP hss]
  omega

/-- A subtraction phase s is deletable if deleting it preserves Hall's condition on all sublists of U. -/
def IsDeletableSubtraction (e : Int → Bool) (p : Nat) (U : List Nat) (lag : Nat → Nat) (s : Nat) : Prop :=
  ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ (deletedNeighborhood e p A lag s).length

/-- Reduction of deletability: in any word with positive slack, any subset containing the SS=2 window
automatically satisfies Hall's condition after deleting s, so deletability reduces to subsets avoiding u₀. -/
theorem deletable_of_avoids_ss2 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (s : Nat)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → u0 ∉ A → A.length ≤ (deletedNeighborhood e p A lag s).length)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length) :
    IsDeletableSubtraction e p U lag s := by
  intro A hAU hAnodup
  by_cases hu0A : u0 ∈ A
  · have hlen := hsublen A hAU hAnodup
    exact deleted_neighborhood_hall_of_has_ss2 e p hp hp11 hper U A lag hlen hslack u0 hu0A hP hss s
  · exact havoid A hAU hu0A

end Recaman.TwoSSTightDisjoint
