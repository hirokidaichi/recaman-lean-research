import Recaman.BoundedExcessSupply
import Recaman.BoundedExcessReservoir

namespace Recaman.SupplyReservoirGeometry

open LeadingRunSupply BoundedExcessSupply BoundedExcessReservoir

/-! Disjointness of the middle reservoirs of bounded-excess supplied A phases. -/

theorem run_value (e : Int → Bool) (t x : Int) (m : Nat)
    (hcur : e t = true)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hxlo : t-m ≤ x) (hxhi : x ≤ t) : e x = true := by
  by_cases heq : x = t
  · simpa [heq] using hcur
  · let i := (t-x-1).toNat
    have hi : (i : Int) = t-x-1 := Int.toNat_of_nonneg (by omega)
    have hilt : i < m := by omega
    have h := ha i hilt
    have hx : t-((i+1 : Nat) : Int) = x := by omega
    rwa [hx] at h

theorem same_run_start (e : Int → Bool) (t u : Int) (m n : Nat) (htu : t < u)
    (htA : e t = true) (huA : e u = true)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false) (huS : e (u-n-1) = false)
    (hoverlap : u-n ≤ t) : t-m = u-n := by
  by_cases h₁ : t-m < u-n
  · have hc := run_value e t (u-n-1) m htA hat (by omega) (by omega)
    rw [huS] at hc
    contradiction
  · by_cases h₂ : u-n < t-m
    · have hc := run_value e u (t-m-1) n huA hau (by omega) (by omega)
      rw [htS] at hc
      contradiction
    · omega

theorem subwindow_ones_le (e : Int → Bool) (t : Int) (d k n : Nat)
    (hkn : k+n ≤ d) : ones (past e (t-k) n) ≤ ones (past e t d) := by
  have hd : d = k+(n+(d-k-n)) := by omega
  rw [hd, past_append, past_append, ones_append, ones_append]
  have h₁ := (ones_bounds (past e t k)).1
  have h₂ := (ones_bounds (past e (t-k-n) (d-k-n))).1
  omega

theorem run_word_ones (e : Int → Bool) (t : Int) (m : Nat)
    (hcur : e t = true)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true) :
    ones (past e (t+1) (m+1)) = (m : Int)+1 := by
  have hw : past e (t+1) (m+1) = List.replicate (m+1) true := by
    apply List.ext_getElem
    · simp [past]
    · intro i hi hj
      have hin : i < m+1 := by simpa using hj
      have hv := run_value e t (t+1-((i+1 : Nat) : Int)) m hcur ha (by omega) (by omega)
      simpa [past] using hv
  rw [hw, ones_replicate_A]
  omega

/-- A reservoir spanning an earlier A run must pay for every A in that run. -/
theorem reservoir_contains_run_count (e : Int → Bool) (t u : Int) (m n : Nat)
    (hcur : e t = true)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hsep : t < u-n) (hcover : u-2*n+1 ≤ t-m) :
    (m : Int)+1 ≤ ones (past e (u-n) (n-1)) := by
  let k := (u-n-t-1).toNat
  have hk : (k : Int) = u-n-t-1 := Int.toNat_of_nonneg (by omega)
  have hkn : k+(m+1) ≤ n-1 := by omega
  have hc := subwindow_ones_le e (u-n) (n-1) k (m+1) hkn
  have heq : u-n-(k : Int) = t+1 := by omega
  rw [heq, run_word_ones e t m hcur ha] at hc
  exact hc


/-- Two distinct eligible sources on the integer line cannot share a reservoir
position. The band hypotheses refer to actual P2 lags, not an assumed matching. -/
theorem ordered_reservoirs_disjoint (e : Int → Bool) (t u x : Int)
    (m n R d d₂ : Nat) (htu : t < u)
    (hm : 3 ≤ m) (hn : 3 ≤ n) (hthreshold : R*(R+1) < m)
    (hsize : 2*R < m+1)
    (htA : e t = true) (huA : e u = true)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false) (huS : e (u-n-1) = false)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u d₂)
    (htlo : 4*(m : Int)-1 ≤ d) (hthi : (d : Int) ≤ 4*m-1+4*R)
    (hulo : 4*(n : Int)-1 ≤ d₂) (huhi : (d₂ : Int) ≤ 4*n-1+4*R)
    (hxt : x ≤ t-m-1) (hxu : u-2*n+1 ≤ x) : False := by
  by_cases hoverlap : u-n ≤ t
  · have hstart := same_run_start e t u m n htu htA huA hat hau htS huS hoverlap
    let k := (u-t).toNat
    have hk : (k : Int) = u-t := Int.toNat_of_nonneg (by omega)
    have hkpos : 1 ≤ k := by omega
    have hu : u = t+k := by omega
    have hkn : n = m+k := by omega
    have hrun : ∀ i, i < k → e (t+i) = true := by
      intro i hi
      exact run_value e u (t+i) n huA hau (by omega) (by omega)
    have hnew : ShortPeriodicSupply.P2 e (t+k) d₂ := by rw [← hu]; exact huP
    have hbound := stream_bounded_excess_multiplicity e t R m k d d₂ hkpos hrun
      htP hnew htlo hthi (by omega) (by omega)
    omega
  · have hcount := reservoir_contains_run_count e t u m n htA hat (by omega) (by omega)
    have hbound := stream_middle_As e u d₂ n R hn hau huP huhi
    omega

/-- Symmetric form suitable for lifting an intersection modulo a period. -/
theorem reservoirs_common_point_eq (e : Int → Bool) (t u x : Int)
    (m n R d d₂ : Nat)
    (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hthresholdt : R*(R+1) < m) (hthresholdu : R*(R+1) < n)
    (hsizet : 2*R < m+1) (hsizeu : 2*R < n+1)
    (htA : e t = true) (huA : e u = true)
    (hat : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hau : ∀ i, i < n → e (u-((i+1 : Nat) : Int)) = true)
    (htS : e (t-m-1) = false) (huS : e (u-n-1) = false)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u d₂)
    (htlo : 4*(m : Int)-1 ≤ d) (hthi : (d : Int) ≤ 4*m-1+4*R)
    (hulo : 4*(n : Int)-1 ≤ d₂) (huhi : (d₂ : Int) ≤ 4*n-1+4*R)
    (hxt : t-2*m+1 ≤ x ∧ x ≤ t-m-1)
    (hxu : u-2*n+1 ≤ x ∧ x ≤ u-n-1) : t = u := by
  by_cases htu : t < u
  · exact False.elim (ordered_reservoirs_disjoint e t u x m n R d d₂ htu hm hn
      hthresholdt hsizet htA huA hat hau htS huS htP huP htlo hthi hulo huhi hxt.2 hxu.1)
  · by_cases hut : u < t
    · exact False.elim (ordered_reservoirs_disjoint e u t x n m R d₂ d hut hn hm
        hthresholdu hsizeu huA htA hau hat huS htS huP htP hulo huhi htlo hthi hxu.2 hxt.1)
    · omega

end Recaman.SupplyReservoirGeometry
