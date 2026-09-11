import Recaman.TwoSSTightAvoidanceTheorem

/-!
# SS2AASCollisionObstruction: Modular Disjointness of SS=2 Donors and AAS Windows

This module proves that an SS=2 window with lag `d < 15` can never collide with
the endpoint phase of a lag 3 AAS window:

1. `ss2_intervening_word_ge_twelve`: The time separation `k` between a clean lag 3 AAS
   window and a succeeding SS=2 window sharing the same endpoint must be at least 12.
2. `stream_ss2_aas_no_shared_endpoint_of_lag_lt_fifteen`: In any stream, an SS=2 window
   with lag `d < 15` can never share an endpoint with a lag 3 AAS window.
3. `periodic_ss2_aas_no_shared_endpoint_of_lag_lt_fifteen`: In any periodic word,
   modular endpoint collision between an SS=2 window of lag `d < 15` and a lag 3 AAS
   window is impossible:
   `endpointPhase p t d ≠ endpointPhase p u 3`.
4. `ss2_lag_lt_fifteen_disjoint_from_aas`: The donated subtraction `s*(u₀)` from an SS=2
   donor with `lag u₀ < 15` is provably disjoint from all lag 3 AAS endpoints in `U`.
-/

namespace Recaman.SS2AASCollisionObstruction

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint

/-- Any intervening word of length k between a clean lag 3 AAS window and a succeeding SS=2
window sharing an endpoint must have length k ≥ 12. -/
theorem ss2_intervening_word_ge_twelve (e : Int → Bool) (t : Int) (k : Nat)
    (hk : 0 < k) (htA : e t = true)
    (hnew : ShortPeriodicSupply.P2 e (t + k) (k + 3))
    (hold : ShortPeriodicSupply.P2 e t 3)
    (hss : ssCount (past e (t + k) (k + 3)) ≤ 2) :
    12 ≤ k := by
  have hmod := stream_shared_endpoint_time_mod_four e t k 3 hk htA hnew hold
  by_cases h12 : 12 ≤ k
  · exact h12
  · have hklen : k = (k - 1) + 1 := by omega
    have hlast : past e (t + k - (k - 1 : Nat)) 1 = [true] := by
      have htime : t + (k : Int) - ((k - 1 : Nat) : Int) - 1 = t := by omega
      simpa [past, htime] using congrArg (fun b => [b]) htA
    have hfirst : past e (t + k) k = past e (t + k) (k - 1) ++ [true] := by
      calc
        past e (t + k) k = past e (t + k) ((k - 1) + 1) := congrArg (past e (t + k)) hklen
        _ = past e (t + k) (k - 1) ++ past e (t + k - (k - 1 : Nat)) 1 := past_append _ _ _ _
        _ = past e (t + k) (k - 1) ++ [true] := by rw [hlast]
    have htime : t + (k : Int) - k = t := by omega
    have hn := (past_p2_iff e (t + k) (k + 3)).mpr hnew
    rw [past_append, hfirst, htime] at hn
    have hdata := intervening_word_data (past e (t + k) (k - 1)) (past e t 3) hn ((past_p2_iff e t 3).mpr hold)
    have hlen : (past e (t + k) (k - 1) ++ [true]).length = k := by
      simp [past]
      omega
    let w := past e (t + k) (k - 1) ++ [true]
    have hw_len : w.length = k := hlen
    have hw_last : w.getLast? = some true := by
      dsimp [w]
      simp
    have hw_mass : mass w = 0 := hdata.1
    have hw_moment : moment w + (w.length : Int) = 0 := hdata.2
    have hw_ss : ssCount w ≤ 2 := by
      have hss_split : ssCount w ≤ ssCount (w ++ past e t 3) := ssCount_append_left_le w (past e t 3)
      have hpast_eq : past e (t + k) (k + 3) = w ++ past e t 3 := by
        dsimp [w]
        rw [← hfirst, past_append, htime]
      rw [hpast_eq] at hss
      omega
    have hwit : isInterveningWitness w = true := by
      dsimp [isInterveningWitness]
      simp [hw_last, hw_mass, hw_moment, hw_ss]
    have hmem := mem_bitWords w
    rw [hw_len] at hmem
    have hcases : k = 4 ∨ k = 8 := by omega
    rcases hcases with rfl | rfl
    · have hfilt := no_intervening_witness_four
      have hmem_filt : w ∈ (bitWords 4).filter isInterveningWitness := by
        rw [List.mem_filter]
        exact ⟨hmem, hwit⟩
      rw [hfilt] at hmem_filt
      cases hmem_filt
    · have hfilt := no_intervening_witness_eight
      have hmem_filt : w ∈ (bitWords 8).filter isInterveningWitness := by
        rw [List.mem_filter]
        exact ⟨hmem, hwit⟩
      rw [hfilt] at hmem_filt
      cases hmem_filt

/-- In any stream, an SS=2 window with lag d < 15 can never share an endpoint
with a lag 3 AAS window. -/
theorem stream_ss2_aas_no_shared_endpoint_of_lag_lt_fifteen (e : Int → Bool)
    (t u : Int) (d : Nat)
    (_htA : e t = true) (huA : e u = true)
    (hd_lt : d < 15)
    (htss : ssCount (past e t d) = 2) (_huss : ssCount (past e u 3) = 0)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u 3)
    (heq : t - d = u - 3) : False := by
  by_cases htu : t = u
  · subst u
    have heqd : d = 3 := by omega
    subst d
    have hlen := ss2_length_ge_eleven (past e t 3) ((past_p2_iff e t 3).mpr htP) htss
    simp only [past, List.length_map, List.length_range] at hlen
    omega
  · by_cases hlt : t < u
    · have hlen : (u : Int) - t = 3 - (d : Int) := by omega
      have hd11 : 11 ≤ d := stream_ss2_lag_ge_eleven e t d htP htss
      omega
    · let k := (t - u).toNat
      have hk : (k : Int) = t - u := Int.toNat_of_nonneg (by omega)
      have hkpos : 0 < k := by omega
      have htime : u + (k : Int) = t := by omega
      have hlen : k + 3 = d := by omega
      have htP' : ShortPeriodicSupply.P2 e (u + k) (k + 3) := by
        rw [htime, hlen]; exact htP
      have htss' : ssCount (past e (u + k) (k + 3)) ≤ 2 := by
        rw [htime, hlen]; omega
      have hk12 := ss2_intervening_word_ge_twelve e u k hkpos huA htP' huP htss'
      omega

/-- In any periodic word, an SS=2 window with lag d < 15 can never share a modular
endpoint phase with a lag 3 AAS window. -/
theorem periodic_ss2_aas_no_shared_endpoint_of_lag_lt_fifteen (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x)
    (t u : Int) (d : Nat)
    (htA : e t = true) (huA : e u = true)
    (hd_lt : d < 15)
    (htss : ssCount (past e t d) = 2) (huss : ssCount (past e u 3) = 0)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u 3)
    (heq : endpointPhase p t d = endpointPhase p u 3) : False := by
  have horder := two_SS_clean_endpoint_mod_order e p hp hper t u d 3 htA huA htss huss htP huP heq
  obtain ⟨z, hzlt, hzeq⟩ := horder
  have huA' : e (u + z * p) = true := by rw [LagElevenPeriodic.e_shift e p hper]; exact huA
  have huss' : ssCount (past e (u + z * p) 3) = 0 := by rw [past_shift e p hper]; exact huss
  have huP' := (p2_shift e p hper u z 3).mpr huP
  exact stream_ss2_aas_no_shared_endpoint_of_lag_lt_fifteen e t (u + z * p) d htA huA' hd_lt htss huss' htP huP' hzeq

/-- If an SS=2 donor window u₀ has lag < 15, then its donated subtraction phase
`endpointPhase p u₀ (lag u₀)` is strictly disjoint from all lag 3 AAS endpoint phases in U. -/
theorem ss2_lag_lt_fifteen_disjoint_from_aas (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x)
    (u0 u : Nat) (d : Nat)
    (hu0A : e (u0 : Int) = true) (huA : e (u : Int) = true)
    (hd_lt : d < 15)
    (hss0 : ssCount (past e (u0 : Int) d) = 2)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) d)
    (hP_u : ShortPeriodicSupply.P2 e (u : Int) 3)
    (haas_u : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    endpointPhase p (u0 : Int) d ≠ endpointPhase p (u : Int) 3 := by
  intro heq
  have huss : ssCount (past e (u : Int) 3) = 0 := by
    have hpast := past_three e (u : Int)
    rw [haas_u.1, haas_u.2.1, haas_u.2.2] at hpast
    rw [hpast]
    decide
  exact periodic_ss2_aas_no_shared_endpoint_of_lag_lt_fifteen e p hp hper (u0 : Int) (u : Int) d hu0A huA hd_lt hss0 huss hP0 hP_u heq

end Recaman.SS2AASCollisionObstruction
