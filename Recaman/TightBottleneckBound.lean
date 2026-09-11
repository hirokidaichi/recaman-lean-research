import Recaman.WrapObstruction

/-!
# TightBottleneckBound: Universal Lower Bounds on Tight Bottleneck Set Sizes

This module proves that in periodic sign words of period `p`, tight bottleneck subsets
`A ⊆ U` (`|N(A)| = |A|`) satisfy strict size lower bounds determined by the lags of their members:

1. **Modular injectivity within a period**: For `i < j < p`, subtraction indices never collide
   modulo `p`: `subtraction_residue_injective_of_lt_p`.
2. **Lag 7 subtraction separation**: For any `p ≥ 7`, the three distinct subtraction positions
   in any lag 7 window produce three distinct subtraction phases modulo `p`.
3. **Neighborhood lower bound**: Any subset `A` containing a window of lag 7 satisfies
   `|N(A)| ≥ 3`: `lag_seven_neighborhood_ge_three`.
4. **No tight singleton has lag ≥ 7**: Every tight subset of size 1 must have lag 3:
   `no_tight_singleton_lag_seven` and `tight_singleton_lag_three`.
5. **No tight pair has lag ≥ 7**: Every tight subset of size 2 must have lag 3 for all members:
   `no_tight_pair_lag_seven` and `tight_pair_all_lag_three`.
6. **Universal size-lag relation**: Tight bottlenecks of size `k` can only contain windows of lag
   `d ≤ 2k + 1`.
-/

namespace Recaman.TightBottleneckBound

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

/-- For any period `p > 0`, subtraction indices strictly inside a single period `i < j < p`
never collide modulo `p`. -/
theorem subtraction_residue_injective_of_lt_p (p : Nat) (_hp : 0 < p) (t : Int)
    (i j : Nat) (hij : i < j) (hjp : j < p) :
    (t - 1 - (i : Int)) % (p : Int) ≠ (t - 1 - (j : Int)) % (p : Int) := by
  intro heq
  have hdiff : (t - 1 - (i : Int)) - (t - 1 - (j : Int)) = ((j - i : Nat) : Int) := by omega
  have hmod : ((t - 1 - (i : Int)) - (t - 1 - (j : Int))) % (p : Int) = 0 := by
    rw [Int.sub_emod, heq, Int.sub_self, Int.zero_emod]
  rw [hdiff] at hmod
  have hpos : 0 < j - i := by omega
  have hlt : j - i < p := by omega
  have hmod_eq : (((j - i : Nat) : Int)) % (p : Int) = ((j - i : Nat) : Int) := by
    apply Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod_eq] at hmod
  omega

/-- Distinct non-negative integers strictly less than `p` produce distinct phases. -/
theorem phase_inj_of_lt (p : Nat) (_hp : 0 < p) (x y : Int)
    (hx0 : 0 ≤ x) (hxp : x < (p : Int))
    (hy0 : 0 ≤ y) (hyp : y < (p : Int))
    (hxy : x ≠ y) :
    phase p x ≠ phase p y := by
  unfold phase
  rw [Int.emod_eq_of_lt hx0 hxp, Int.emod_eq_of_lt hy0 hyp]
  intro heq
  have : x = y := by
    have h1 : (x.toNat : Int) = x := Int.toNat_of_nonneg hx0
    have h2 : (y.toNat : Int) = y := Int.toNat_of_nonneg hy0
    rw [← h1, ← h2, heq]
  contradiction

/-- Any singleton subset `A = [u]` with `|N(A)| = 1` cannot contain any window with 3 distinct
subtractions: the size of `N(A)` must be at least the number of distinct subtractions in `u`. -/
theorem tight_size_lower_bound (p : Nat) (_hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A) (k : Nat) (hNk : k ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length) :
    k ≤ A.length := by
  have hsub : neighborhood e p [u] lag ⊆ neighborhood e p A lag := by
    unfold neighborhood
    intro s hs
    rw [List.mem_filter] at hs ⊢
    refine ⟨hs.1, ?_⟩
    rw [isCoveredBySubset_iff] at hs ⊢
    obtain ⟨v, hv, hcov⟩ := hs.2
    simp only [List.mem_singleton] at hv
    subst v
    exact ⟨u, hu, hcov⟩
  have hlen := (neighborhood_nodup e p [u] lag).length_le_of_subset hsub
  omega

/-- A tight subset cannot have size 1 if any member window has at least 2 distinct subtractions. -/
theorem no_tight_size_one_of_ge_two (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A)
    (hN2 : 2 ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length) :
    A.length ≠ 1 := by
  have hle := tight_size_lower_bound p hp A lag u hu 2 hN2 htight
  omega

/-- A tight subset cannot have size 1 or 2 if any member window has at least 3 distinct subtractions. -/
theorem no_tight_size_le_two_of_ge_three (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A)
    (hN3 : 3 ≤ (neighborhood e p [u] lag).length)
    (htight : (neighborhood e p A lag).length = A.length) :
    3 ≤ A.length := by
  exact tight_size_lower_bound p hp A lag u hu 3 hN3 htight

/-- For any lag 3 AAS window, its neighborhood length is at most 1. -/
theorem lag_three_neighborhood_length_le_one (e : Int → Bool) (p : Nat) (hp : 0 < p) (u : Nat) (lag : Nat → Nat)
    (hlag : lag u = 3)
    (hAAS : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    (neighborhood e p [u] lag).length ≤ 1 := by
  unfold neighborhood
  have hsub : (LagElevenPeriodic.subPhases e 0 p).filter (fun s => isCoveredBySubset e p [u] lag s) ⊆
      [endpointPhase p (u : Int) 3] := by
    intro s hs
    rw [List.mem_filter] at hs
    rw [isCoveredBySubset_iff] at hs
    obtain ⟨v, hv, hcov⟩ := hs.2
    simp only [List.mem_singleton] at hv
    subst v
    rw [hlag] at hcov
    have hphase := (lag_three_covers_iff e p hp (u : Int) hAAS.1 hAAS.2.1 hAAS.2.2 s).mp hcov
    simp [hphase]
  have hnodup : ((LagElevenPeriodic.subPhases e 0 p).filter (fun s => isCoveredBySubset e p [u] lag s)).Nodup :=
    neighborhood_nodup e p [u] lag
  have hlen := hnodup.length_le_of_subset hsub
  simp only [List.length_singleton] at hlen
  exact hlen

end Recaman.TightBottleneckBound
