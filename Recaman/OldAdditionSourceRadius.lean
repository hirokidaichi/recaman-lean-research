import Recaman.SeparatorTailFreeGap

namespace Recaman.OldAdditionSourceRadius

open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.SeparatorTailFreeGap

/-! An old A budget bounds how far an original source can precede a cut.
The future A count, old depth and all word lengths remain unrestricted.
Removing the proved irrelevant prefix does not reset its free ledger. -/

/-- Only the old interval contributes to the radius. The area equation is
unneeded for this bound, but the hypothesis is the actual library window. -/
theorem old_source_distance (f : Nat → Bool) (u v k p b : Nat)
    (huv : u ≤ v) (hA : cN (fun i => f i = true) 0 v ≤ p)
    (hlevel : Fw f (u+k) ≤ Fw f v + (b : Int) + 1)
    (hW : Win f u k) : v-u ≤ 2*p+b := by
  have hc := cN_sub0 (fun i => f i = true) u v huv
  have hw := cN_walk f u (v-u)
  rw [Nat.add_sub_cancel' huv] at hw
  have hmass := hW.2.1
  omega

/-- Every original source, including all alternatives, survives this cut. -/
theorem source_clock_ge_cut (f : Nat → Bool) (u v k p b : Nat)
    (hA : cN (fun i => f i = true) 0 v ≤ p)
    (hlevel : Fw f (u+k) ≤ Fw f v + (b : Int) + 1)
    (hW : Win f u k) : v-(2*p+b) ≤ u := by
  by_cases huv : u ≤ v
  · have hd := old_source_distance f u v k p b huv hA hlevel hW
    omega
  · omega

/-- Literal suffix translation preserves each source window, not merely
existence of some supply. No hypothesis on the erased prefix is used here. -/
theorem window_nat_shift (f : Nat → Bool) (s u k : Nat) :
    Win f (s+u) k ↔ Win (fun i => f (s+i)) u k := by
  have hs := seg_nat_shift f s u k
  have hm1 := seg_mass f (s+u) k
  have hm2 := seg_mass (fun i => f (s+i)) u k
  rw [hs] at hm2
  have ha : Ar f (s+u) k = Ar (fun i => f (s+i)) u k := by
    rw [Ar_areaW, Ar_areaW, hs]
  constructor
  · rintro ⟨hk, hm, hz⟩
    exact ⟨hk, by omega, by rwa [←ha]⟩
  · rintro ⟨hk, hm, hz⟩
    exact ⟨hk, by omega, by rwa [ha]⟩

/-- Complete original source-set transport, at the source's original clock.
The reverse direction restores the exact same window in the old history. -/
theorem original_source_iff (f : Nat → Bool) (u v k p b : Nat)
    (hA : cN (fun i => f i = true) 0 v ≤ p)
    (hlevel : Fw f (u+k) ≤ Fw f v + (b : Int) + 1) :
    let s := v-(2*p+b)
    Win f u k ↔ s ≤ u ∧ Win (fun i => f (s+i)) (u-s) k := by
  dsimp only
  let s := v-(2*p+b)
  constructor
  · intro hW
    have hu : s ≤ u := source_clock_ge_cut f u v k p b hA hlevel hW
    refine ⟨hu, ?_⟩
    have hs := window_nat_shift f s (u-s) k
    rw [Nat.add_sub_cancel' hu] at hs
    exact hs.mp hW
  · rintro ⟨hu,hW⟩
    have hs := window_nat_shift f s (u-s) k
    rw [Nat.add_sub_cancel' hu] at hs
    exact hs.mpr hW

/-- Actual supply is unchanged after the proved complete-source cut. -/
theorem endN_cut_iff (f : Nat → Bool) (v q p b : Nat)
    (hA : cN (fun i => f i = true) 0 v ≤ p)
    (hlevel : Fw f q ≤ Fw f v + (b : Int) + 1) :
    EndN f 0 q ↔ EndN f (v-(2*p+b)) q := by
  constructor
  · rintro ⟨hq,u,k,_,huk,hW⟩
    have hu := source_clock_ge_cut f u v k p b hA (by rwa [huk]) hW
    exact ⟨hq,u,k,hu,huk,hW⟩
  · exact end_mono f 0 (v-(2*p+b)) q (Nat.zero_le _)

/-- Only future A heights are constrained. Arbitrarily many future A and
arbitrarily long futures are allowed; original free tags are preserved. -/
theorem future_free_transport (f : Nat → Bool) (v K p b : Nat)
    (hA : cN (fun i => f i = true) 0 v ≤ p)
    (hlevel : ∀ i, v ≤ i → i < v+K → f i = true →
      Fw f i ≤ Fw f v + (b : Int) + 1) :
    let s := v-(2*p+b)
    cN (fun i => f i = true ∧ ¬EndN f 0 i) v K =
      cN (fun i => f (s+i) = true ∧ ¬EndN (fun j => f (s+j)) 0 i) (v-s) K := by
  dsimp only
  let s := v-(2*p+b)
  have hcut : cN (fun i => f i = true ∧ ¬EndN f 0 i) v K =
      cN (fun i => f i = true ∧ ¬EndN f s i) v K := by
    apply cN_congr
    intro i hi hiK
    apply and_congr_right
    intro hiA
    exact not_congr (endN_cut_iff f v i p b hA (hlevel i hi hiK hiA))
  rw [hcut]
  have hs := free_count_nat_shift f s (v-s) K
  have hle : s ≤ v := Nat.sub_le _ _
  rw [Nat.add_sub_cancel' hle] at hs
  exact hs

/-- The original prefix free count remains explicitly charged. In
particular the transported future is never asserted to have a fresh past. -/
theorem original_free_ledger (f : Nat → Bool) (v K p b : Nat)
    (hA : cN (fun i => f i = true) 0 v ≤ p)
    (hlevel : ∀ i, v ≤ i → i < v+K → f i = true →
      Fw f i ≤ Fw f v + (b : Int) + 1) :
    let s := v-(2*p+b)
    cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 (v+K) =
      cN (fun i => f i = true ∧ ¬EndN f 0 i) 0 v +
      cN (fun i => f (s+i) = true ∧ ¬EndN (fun j => f (s+j)) 0 i) (v-s) K := by
  have hc := cN_add (fun i => f i = true ∧ ¬EndN f 0 i) 0 v K
  simp only [Nat.zero_add] at hc
  rw [hc, future_free_transport f v K p b hA hlevel]

end Recaman.OldAdditionSourceRadius
