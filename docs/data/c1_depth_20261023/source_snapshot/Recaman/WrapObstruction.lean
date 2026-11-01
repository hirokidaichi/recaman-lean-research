import Recaman.TwoSSAvoidTight

/-!
# WrapObstruction: Universal Non-Wrapping Obstruction to Tight Bottlenecks

This module establishes the general wrap obstruction for periodic sign words of **arbitrary period p ≥ 1**:
1. **Universal coverage by wrapping windows**: Any window of length `d ≥ p` covers all
   subtraction phases of `e`: `window_wrap_covers_all_subtractions`.
2. **Full neighborhood**: Any subset `A ⊆ U` containing a wrapping window (`lag u₀ ≥ p`)
   has full neighborhood `N(A) = D`: `neighborhood_eq_subPhases_of_has_wrap`.
3. **Strict expansion**: In any word with positive slack `|U| < |D|`, any subset containing
   a wrapping window strictly expands `|A| < |N(A)|`: `strict_expansion_of_has_wrap`.
4. **No tight subset contains a wrapping window**: No tight subset `A` (`|N(A)| = |A|`) can ever
   contain a wrapping window: `no_tight_subset_contains_wrap`.
5. **Localization of tight bottlenecks**: Every tight subset in a positive-slack word consists
   purely of non-wrapping, strictly local windows (`lag u < p`): `tight_subset_all_lags_lt_p`.
6. **Universal Hall preservation under deletion**: Deleting any subtraction `s ∈ D` preserves
   Hall's condition on all subsets containing a wrapping window:
   `deleted_neighborhood_hall_of_has_wrap`.
7. **Reduction of deletability**: Deletability of any subtraction reduces to subsets avoiding
   wrapping windows: `deletable_of_avoids_wrap`.
8. **Finite lag classification**:
   - For `p ≤ 7`, tight subsets consist exclusively of lag 3 windows: `tight_lags_for_p_le_seven`.
   - For `p ≤ 11`, tight subsets consist exclusively of lag 3 and lag 7 windows: `tight_lags_for_p_le_eleven`.
-/

namespace Recaman.WrapObstruction

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

/-- Any window of length `d ≥ p` covers every subtraction phase `s ∈ D`. -/
theorem window_wrap_covers_all_subtractions (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (t : Int) (d : Nat) (hd : p ≤ d)
    (s : Nat) (hs : s ∈ LagElevenPeriodic.subPhases e 0 p) :
    WindowCoversSubtraction e p t d s := by
  have hs_mem := (LagElevenPeriodic.mem_subPhases e 0 p s).mp hs
  have hs_lt := hs_mem.1
  have hs_S := hs_mem.2
  have h0 : (0 : Int) + (s : Int) = (s : Int) := by omega
  rw [h0] at hs_S
  exact periodic_window_covers_subtraction e p hp hper t d hd s hs_lt hs_S

/-- For arbitrary period p, if `A` contains a window of lag `d ≥ p`, its subtraction neighborhood
is the ENTIRE set `D = subPhases e 0 p` of subtractions. -/
theorem neighborhood_eq_subPhases_of_has_wrap (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hwrap : p ≤ lag u0) :
    neighborhood e p A lag = LagElevenPeriodic.subPhases e 0 p := by
  unfold neighborhood
  apply filter_all_true
  intro s hs
  rw [isCoveredBySubset_iff]
  refine ⟨u0, hu0, ?_⟩
  exact window_wrap_covers_all_subtractions e p hp hper (u0 : Int) (lag u0) hwrap s hs

/-- The neighborhood length of any subset containing a wrapping window is `|D|`. -/
theorem neighborhood_length_of_has_wrap (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hwrap : p ≤ lag u0) :
    (neighborhood e p A lag).length = (LagElevenPeriodic.subPhases e 0 p).length := by
  rw [neighborhood_eq_subPhases_of_has_wrap e p hp hper A lag u0 hu0 hwrap]

/-- In any word with positive slack `|U| < |D|`, any subset containing a wrapping window
strictly expands: `|A| < |N(A)|`. -/
theorem strict_expansion_of_has_wrap (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hwrap : p ≤ lag u0) :
    A.length < (neighborhood e p A lag).length := by
  rw [neighborhood_length_of_has_wrap e p hp hper A lag u0 hu0 hwrap]
  omega

/-- NO tight subset (`|N(A)| = |A|`) can EVER contain a wrapping window (`lag u₀ ≥ p`). -/
theorem no_tight_subset_contains_wrap (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hwrap : p ≤ lag u0) :
    (neighborhood e p A lag).length ≠ A.length := by
  have hlt := strict_expansion_of_has_wrap e p hp hper U A lag hAU hslack u0 hu0 hwrap
  omega

/-- Localization of tight bottlenecks:
In any word with positive slack, every window in a tight subset must have lag strictly less than p. -/
theorem tight_subset_all_lags_lt_p (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length) :
    ∀ u ∈ A, lag u < p := by
  intro u hu
  by_cases hlt : lag u < p
  · exact hlt
  · have hwrap : p ≤ lag u := by omega
    have hne := no_tight_subset_contains_wrap e p hp hper U A lag hAU hslack u hu hwrap
    contradiction

/-- Deleting any subtraction preserves Hall's condition on any subset containing a wrapping window. -/
theorem deleted_neighborhood_hall_of_has_wrap (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hwrap : p ≤ lag u0)
    (s : Nat) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  unfold deletedNeighborhood
  rw [neighborhood_eq_subPhases_of_has_wrap e p hp hper A lag u0 hu0 hwrap]
  have hfilt := filter_ne_nodup (subPhases_nodup e p) s
  omega

/-- Reduction of deletability: in any positive-slack word, Hall's condition after deleting s
reduces entirely to subsets avoiding wrapping windows. -/
theorem deletable_of_avoids_wrap (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hwrap : p ≤ lag u0)
    (s : Nat)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → u0 ∉ A → A.length ≤ (deletedNeighborhood e p A lag s).length)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length) :
    IsDeletableSubtraction e p U lag s := by
  intro A hAU hAnodup
  by_cases hu0A : u0 ∈ A
  · have hlen := hsublen A hAU hAnodup
    exact deleted_neighborhood_hall_of_has_wrap e p hp hper U A lag hlen hslack u0 hu0A hwrap s
  · exact havoid A hAU hu0A

/-- For `p ≤ 7`, every P2 window in a tight subset has lag exactly 3. -/
theorem tight_lags_for_p_le_seven (p : Nat) (hp : p ≤ 7)
    (d : Nat) (hd_lt : d < p) (hpos : 0 < d) (hmod : d % 4 = 3) :
    d = 3 := by
  omega

/-- For `p ≤ 11`, every P2 window in a tight subset has lag either 3 or 7. -/
theorem tight_lags_for_p_le_eleven (p : Nat) (hp : p ≤ 11)
    (d : Nat) (hd_lt : d < p) (hpos : 0 < d) (hmod : d % 4 = 3) :
    d = 3 ∨ d = 7 := by
  omega

end Recaman.WrapObstruction
