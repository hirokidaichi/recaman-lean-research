import Recaman.EndpointRepetitionBudget
import Recaman.LowSSEndpoint

/-!
# TwoSSEndpoint

Rigidity and clean-only earlier shared endpoints for SS=2 P2 windows.

Key results:
- `ssCount_two_shared_endpoint_clean`: Any word sharing an endpoint with an SS=2
  window (separated by current-A) must have `ssCount = 0` (strictly clean).
- `intervening_word_data`: The intervening word `v ++ [true]` must have mass 0
  and moment equal to `-length`.
- `stream_ssCount_two_shared_endpoint_clean`: In any stream, an earlier window
  sharing an endpoint with an SS ≤ 2 window must be clean (`ssCount = 0`).
- `stream_ssCount_two_later_ge_four`: An earlier window with `ssCount ≥ 2` forces
  any later window sharing its endpoint to have `ssCount ≥ 4`.
- `stream_earlier_ss_pos_obstruction`: An earlier window with `ssCount ≥ 1` cannot
  share an endpoint with a later window having `ssCount ≤ 2`.
- `stream_no_two_SS_shared_endpoint`: Two SS=2 windows can never share an endpoint.
- `two_SS_endpoint_injective`: Any two SS=2 windows sharing an endpoint must be
  identical.
- `ss_one_two_no_shared_endpoint`: An SS=1 window and an SS=2 window can never
  share an endpoint in either direction.
- `mass_zero_length_even`: Mass zero forces even length.
- `no_intervening_witness_two` .. `ten`: No intervening word exists of length ≤ 10.
- `intervening_witness_twelve`: The unique length-12 intervening word is `AASASASASSSA`.
- `intervening_twelve_has_p2_prefix`: The unique length-12 witness has a clean P2 prefix.
-/

namespace Recaman.TwoSSEndpoint

open LeadingRunSupply OneSSMultiplicity LowSSEndpoint EndpointRepetitionBudget

/-- An SS=2 window sharing an endpoint with an earlier window separated by
current-A forces the earlier window to have zero SS edges and consumes the
entire budget of two SS edges in the intervening word. -/
theorem ssCount_two_shared_endpoint_clean (v u : List Bool)
    (hnew : P2 ((v++[true])++u)) (hold : P2 u)
    (hss : ssCount ((v++[true])++u) ≤ 2) :
    ssCount u = 0 ∧ ssCount (v++[true]) = 2 := by
  have hc := intervening_cost v u hnew hold
  have ha := ssCount_append_superadditive (v++[true]) u
  omega

/-- An intervening word between two shared-endpoint P2 windows has zero mass
and moment equal to `-length`. -/
theorem intervening_word_data (v u : List Bool)
    (hnew : P2 ((v++[true])++u)) (hold : P2 u) :
    mass (v++[true]) = 0 ∧ moment (v++[true]) + ((v++[true]).length : Int) = 0 := by
  have hm := mass_append (v++[true]) u
  have hM := moment_append (v++[true]) u
  rw [hnew.1, hold.1] at hm
  rw [hnew.2, hold.2, hold.1] at hM
  omega

/-- In any stream, an earlier window sharing an endpoint with a later window
of SS-count at most two must be strictly clean (`ssCount = 0`). -/
theorem stream_ssCount_two_shared_endpoint_clean (e : Int → Bool) (t : Int) (k d : Nat)
    (hk : 0 < k) (hA : e t = true)
    (hnew : ShortPeriodicSupply.P2 e (t+k) (k+d))
    (hold : ShortPeriodicSupply.P2 e t d)
    (hss : ssCount (past e (t+k) (k+d)) ≤ 2) :
    ssCount (past e t d) = 0 := by
  have hinc := stream_SS_increment e t k d hk hA hnew hold
  omega

/-- An earlier window with `ssCount ≥ 2` forces any later window sharing its
endpoint (separated by current-A) to have `ssCount ≥ 4`. -/
theorem stream_ssCount_two_later_ge_four (e : Int → Bool) (t : Int) (k d : Nat)
    (hk : 0 < k) (hA : e t = true)
    (hnew : ShortPeriodicSupply.P2 e (t+k) (k+d))
    (hold : ShortPeriodicSupply.P2 e t d)
    (hold_ss : 2 ≤ ssCount (past e t d)) :
    4 ≤ ssCount (past e (t+k) (k+d)) := by
  have hinc := stream_SS_increment e t k d hk hA hnew hold
  omega

/-- An earlier window with positive SS-count cannot share an endpoint with a
later window having `ssCount ≤ 2`. -/
theorem stream_earlier_ss_pos_obstruction (e : Int → Bool) (t : Int) (k d : Nat)
    (hk : 0 < k) (hA : e t = true)
    (hnew : ShortPeriodicSupply.P2 e (t+k) (k+d))
    (hold : ShortPeriodicSupply.P2 e t d)
    (hold_ss : 1 ≤ ssCount (past e t d))
    (hnew_ss : ssCount (past e (t+k) (k+d)) ≤ 2) : False := by
  have hinc := stream_SS_increment e t k d hk hA hnew hold
  omega

/-- Two SS=2 windows can never share an endpoint separated by an A-sign. -/
theorem stream_no_two_SS_shared_endpoint (e : Int → Bool) (t : Int) (k d : Nat)
    (hk : 0 < k) (hA : e t = true)
    (hnew : ShortPeriodicSupply.P2 e (t+k) (k+d))
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew_ss : ssCount (past e (t+k) (k+d)) ≤ 2)
    (hold_ss : 2 ≤ ssCount (past e t d)) : False := by
  have hclean := stream_ssCount_two_shared_endpoint_clean e t k d hk hA hnew hold hnew_ss
  omega

/-- Two SS=2 windows ending at A having the same endpoint must be identical. -/
theorem two_SS_endpoint_injective (e : Int → Bool) (t u : Int) (d f : Nat)
    (htA : e t = true) (huA : e u = true)
    (htss : ssCount (past e t d) = 2) (huss : ssCount (past e u f) = 2)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u f)
    (heq : t - d = u - f) : t = u := by
  by_cases htu : t = u
  · exact htu
  · by_cases hlt : t < u
    · let k := (u - t).toNat
      have hk : (k : Int) = u - t := Int.toNat_of_nonneg (by omega)
      have hkpos : 0 < k := by omega
      have htime : t + (k : Int) = u := by omega
      have hlen : k + d = f := by omega
      have huP' : ShortPeriodicSupply.P2 e (t + k) (k + d) := by
        rw [htime, hlen]; exact huP
      have huss' : ssCount (past e (t + k) (k + d)) ≤ 2 := by
        rw [htime, hlen]; omega
      have htss_le : 2 ≤ ssCount (past e t d) := by omega
      have hf := stream_no_two_SS_shared_endpoint e t k d hkpos htA huP' htP huss' htss_le
      exact False.elim hf
    · let k := (t - u).toNat
      have hk : (k : Int) = t - u := Int.toNat_of_nonneg (by omega)
      have hkpos : 0 < k := by omega
      have htime : u + (k : Int) = t := by omega
      have hlen : k + f = d := by omega
      have htP' : ShortPeriodicSupply.P2 e (u + k) (k + f) := by
        rw [htime, hlen]; exact htP
      have htss' : ssCount (past e (u + k) (k + f)) ≤ 2 := by
        rw [htime, hlen]; omega
      have huss_le : 2 ≤ ssCount (past e u f) := by omega
      have hf := stream_no_two_SS_shared_endpoint e u k f hkpos huA htP' huP htss' huss_le
      exact False.elim hf

/-- An SS=1 window and an SS=2 window can never share an endpoint in either direction. -/
theorem ss_one_two_no_shared_endpoint (e : Int → Bool) (t u : Int) (d f : Nat)
    (htA : e t = true) (huA : e u = true)
    (htss : ssCount (past e t d) = 1) (huss : ssCount (past e u f) = 2)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u f)
    (heq : t - d = u - f) : False := by
  by_cases htu : t = u
  · subst u
    have heqd : d = f := by omega
    subst f
    omega
  · by_cases hlt : t < u
    · let k := (u - t).toNat
      have hk : (k : Int) = u - t := Int.toNat_of_nonneg (by omega)
      have hkpos : 0 < k := by omega
      have htime : t + (k : Int) = u := by omega
      have hlen : k + d = f := by omega
      have huP' : ShortPeriodicSupply.P2 e (t + k) (k + d) := by
        rw [htime, hlen]; exact huP
      have huss' : ssCount (past e (t + k) (k + d)) ≤ 2 := by
        rw [htime, hlen]; omega
      have htss_le : 1 ≤ ssCount (past e t d) := by omega
      have hf := stream_earlier_ss_pos_obstruction e t k d hkpos htA huP' htP htss_le huss'
      exact hf
    · let k := (t - u).toNat
      have hk : (k : Int) = t - u := Int.toNat_of_nonneg (by omega)
      have hkpos : 0 < k := by omega
      have htime : u + (k : Int) = t := by omega
      have hlen : k + f = d := by omega
      have htP' : ShortPeriodicSupply.P2 e (u + k) (k + f) := by
        rw [htime, hlen]; exact htP
      have htss' : ssCount (past e (u + k) (k + f)) ≤ 1 := by
        rw [htime, hlen]; omega
      have hinc := stream_SS_increment e u k f hkpos huA htP' huP
      omega

/-- Mass zero forces word length to be even. -/
theorem mass_zero_length_even (w : List Bool) (hm : mass w = 0) :
    w.length = 2 * (ones w).toNat := by
  have h := mass_eq w
  have ho := ones_bounds w
  omega

/-- All binary words of length n. -/
def bitWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitWords n).flatMap (fun w => [false :: w, true :: w])

/-- Decidable predicate identifying an intervening word between shared endpoints. -/
def isInterveningWitness (w : List Bool) : Bool :=
  w.getLast? == some true &&
  mass w == 0 &&
  moment w + (w.length : Int) == 0 &&
  ssCount w ≤ 2

/-- Decidable check for whether a word has a non-trivial P2 prefix. -/
def hasP2Prefix (w : List Bool) : Bool :=
  (List.range w.length).any (fun d => d > 0 && mass (w.take d) == 1 && moment (w.take d) == 0)

set_option maxRecDepth 3000000

theorem no_intervening_witness_two :
    (bitWords 2).filter isInterveningWitness = [] := by decide

theorem no_intervening_witness_four :
    (bitWords 4).filter isInterveningWitness = [] := by decide

theorem no_intervening_witness_six :
    (bitWords 6).filter isInterveningWitness = [] := by decide

theorem no_intervening_witness_eight :
    (bitWords 8).filter isInterveningWitness = [] := by decide

theorem no_intervening_witness_ten :
    (bitWords 10).filter isInterveningWitness = [] := by decide

/-- The unique intervening word of length 12 is `two_SS_control`. -/
theorem intervening_witness_twelve :
    (bitWords 12).filter isInterveningWitness =
      [[true, true, false, true, false, true, false, true, false, false, false, true]] := by decide

/-- Every intervening word of length 12 has a strict P2 prefix. -/
theorem intervening_twelve_has_p2_prefix :
    ∀ w ∈ (bitWords 12).filter isInterveningWitness, hasP2Prefix w = true := by decide

/-- Every list is in the exhaustive bit-words list of its length. -/
theorem mem_bitWords (w : List Bool) : w ∈ bitWords w.length := by
  induction w with
  | nil => simp [bitWords]
  | cons b w ih =>
    simp only [List.length_cons, bitWords, List.mem_flatMap]
    refine ⟨w, ih, ?_⟩
    cases b <;> simp

/-- A P2 word has odd length. -/
theorem p2_length_odd (w : List Bool) (hP : P2 w) : w.length % 2 = 1 := by
  have h := mass_eq w
  have hm := hP.1
  omega

/-- Decidable check for SS=2 P2 word. -/
def isSS2P2 (w : List Bool) : Bool :=
  mass w == 1 && moment w == 0 && ssCount w == 2

theorem no_ss2_p2_one : ∀ w ∈ bitWords 1, isSS2P2 w = false := by decide
theorem no_ss2_p2_three : ∀ w ∈ bitWords 3, isSS2P2 w = false := by decide
theorem no_ss2_p2_five : ∀ w ∈ bitWords 5, isSS2P2 w = false := by decide
theorem no_ss2_p2_seven : ∀ w ∈ bitWords 7, isSS2P2 w = false := by decide
theorem no_ss2_p2_nine : ∀ w ∈ bitWords 9, isSS2P2 w = false := by decide

/-- Any P2 word with ssCount = 2 has length at least 11. -/
theorem ss2_length_ge_eleven (w : List Bool) (hP : P2 w) (hss : ssCount w = 2) :
    11 ≤ w.length := by
  by_cases hge : 11 ≤ w.length
  · exact hge
  · have hmem := mem_bitWords w
    have htrue : isSS2P2 w = true := by
      simp [isSS2P2, hP.1, hP.2, hss]
    have hcases : w.length = 1 ∨ w.length = 3 ∨ w.length = 5 ∨ w.length = 7 ∨ w.length = 9 := by
      have hodd := p2_length_odd w hP
      omega
    cases hcases with
    | inl h1 => have := no_ss2_p2_one w (h1 ▸ hmem); rw [htrue] at this; contradiction
    | inr hrest => cases hrest with
      | inl h3 => have := no_ss2_p2_three w (h3 ▸ hmem); rw [htrue] at this; contradiction
      | inr hrest => cases hrest with
        | inl h5 => have := no_ss2_p2_five w (h5 ▸ hmem); rw [htrue] at this; contradiction
        | inr hrest => cases hrest with
          | inl h7 => have := no_ss2_p2_seven w (h7 ▸ hmem); rw [htrue] at this; contradiction
          | inr h9 => have := no_ss2_p2_nine w (h9 ▸ hmem); rw [htrue] at this; contradiction

/-- In any stream, an SS=2 P2 window has lag at least 11. -/
theorem stream_ss2_lag_ge_eleven (e : Int → Bool) (t : Int) (d : Nat)
    (hP : ShortPeriodicSupply.P2 e t d)
    (hss : ssCount (past e t d) = 2) : 11 ≤ d := by
  have hp2 := (past_p2_iff e t d).mpr hP
  have hlen := ss2_length_ge_eleven (past e t d) hp2 hss
  simp only [past, List.length_map, List.length_range] at hlen
  exact hlen

/-- An SS=2 P2 word contains at least 5 subtractions. -/
theorem ss2_subtractions_ge_five (w : List Bool) (hP : P2 w) (hss : ssCount w = 2) :
    5 ≤ w.length - (ones w).toNat := by
  have hlen := ss2_length_ge_eleven w hP hss
  have h := mass_eq w
  have hm := hP.1
  have ho := ones_bounds w
  omega

end Recaman.TwoSSEndpoint
