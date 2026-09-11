import Recaman.SS2StrictSlackTheorem

/-!
# LowSSTwoSSJointCapacity: Unified Three-Tier Joint Capacity Bound

This module proves the comprehensive joint capacity theorem combining:
- Tier 0: Clean lag 3 AAS windows (`ssCount = 0`)
- Tier 1: SS=1 windows (`ssCount = 1`)
- Tier 2: SS=2 windows with `lag < 15` (`ssCount = 2`)

Key results:
1. `ss_le1_two_endpoint_mod_disjoint`: Any addition window in Tier 0 or Tier 1 is provably
   disjoint from any SS=2 window with `lag < 15` on modular endpoint phases.
2. `low_SS_two_SS_joint_capacity`: Unified joint capacity bound:
   `|U_{≤1}| + |U₂| ≤ |D|`.
3. `ss2_strict_capacity_deficit`: The presence of `k` distinct SS=2 windows with `lag < 15`
   strictly bounds the low-SS additions to `|U_{≤1}| ≤ |D| - k`.
-/

namespace Recaman.LowSSTwoSSJointCapacity

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem SS2StrictSlackTheorem OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- Modular endpoint disjointness between Tier 0/1 (SS ≤ 1) and Tier 2 (SS = 2, lag < 15). -/
theorem ss_le1_two_endpoint_mod_disjoint (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u v : Int) (d f : Nat)
    (huA : e u = true) (hvA : e v = true)
    (huss : ssCount (past e u d) ≤ 1)
    (haas : ssCount (past e u d) = 0 → d = 3)
    (hvss : ssCount (past e v f) = 2)
    (hf_lt : f < 15)
    (huP : ShortPeriodicSupply.P2 e u d) (hvP : ShortPeriodicSupply.P2 e v f)
    (heq : endpointPhase p u d = endpointPhase p v f) : False := by
  have hcases : ssCount (past e u d) = 0 ∨ ssCount (past e u d) = 1 := by omega
  rcases hcases with h0 | h1
  · have hd3 := haas h0
    subst d
    exact periodic_ss2_aas_no_shared_endpoint_of_lag_lt_fifteen e p hp hper v u f hvA huA hf_lt hvss h0 hvP huP heq.symm
  · exact ss_one_two_endpoint_mod_disjoint e p hp hper u v d f huA hvA h1 hvss huP hvP heq

/-- Unified Three-Tier Joint Capacity Bound:
The combined cardinality of low-SS additions (SS ≤ 1) and SS=2 additions with lag < 15
is bounded by the total subtraction capacity |D|. -/
theorem low_SS_two_SS_joint_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U1 U2 : List Nat) (hU1nodup : U1.Nodup) (hU2nodup : U2.Nodup)
    (hU1range : ∀ u, u ∈ U1 → u < p) (hU2range : ∀ u, u ∈ U2 → u < p)
    (hSupply1 : ∀ u, u ∈ U1 → e u = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d) ≤ 1 ∧
      (ssCount (past e u d) = 0 → d = 3) ∧ e (u - d) = false)
    (hSupply2 : ∀ u, u ∈ U2 → e u = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d) = 2 ∧
      d < 15 ∧ e (u - d) = false) :
    U1.length + U2.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  classical
  let lag1 := fun u : Nat => if hu : u ∈ U1 then Classical.choose (hSupply1 u hu).2 else 0
  have hlag1 : ∀ u, u ∈ U1 → ShortPeriodicSupply.P2 e u (lag1 u) ∧
      ssCount (past e u (lag1 u)) ≤ 1 ∧
      (ssCount (past e u (lag1 u)) = 0 → lag1 u = 3) ∧
      e (u - lag1 u) = false := by
    intro u hu; dsimp [lag1]; rw [dif_pos hu]; exact Classical.choose_spec (hSupply1 u hu).2
  let lag2 := fun u : Nat => if hu : u ∈ U2 then Classical.choose (hSupply2 u hu).2 else 0
  have hlag2 : ∀ u, u ∈ U2 → ShortPeriodicSupply.P2 e u (lag2 u) ∧
      ssCount (past e u (lag2 u)) = 2 ∧
      lag2 u < 15 ∧
      e (u - lag2 u) = false := by
    intro u hu; dsimp [lag2]; rw [dif_pos hu]; exact Classical.choose_spec (hSupply2 u hu).2
  let f1 := fun u : Nat => endpointPhase p u (lag1 u)
  let f2 := fun u : Nat => endpointPhase p u (lag2 u)
  have hinj1 : ∀ u v, u ∈ U1 → v ∈ U1 → f1 u = f1 v → u = v := by
    intro u v hu hv heq
    have hmod := LowSSPeriodicSupply.endpoint_mod_injective e p hp hper u v (lag1 u) (lag1 v)
      (hSupply1 u hu).1 (hSupply1 v hv).1 (hlag1 u hu).2.1 (hlag1 v hv).2.1
      (hlag1 u hu).1 (hlag1 v hv).1 heq
    have hult := hU1range u hu; have hvlt := hU1range v hv
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hinj2 : ∀ u v, u ∈ U2 → v ∈ U2 → f2 u = f2 v → u = v := by
    intro u v hu hv heq
    have hmod := two_SS_endpoint_mod_injective e p hp hper u v (lag2 u) (lag2 v)
      (hSupply2 u hu).1 (hSupply2 v hv).1 (hlag2 u hu).2.1 (hlag2 v hv).2.1
      (hlag2 u hu).1 (hlag2 v hv).1 heq
    have hult := hU2range u hu; have hvlt := hU2range v hv
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hdisj : ∀ a, a ∈ U1.map f1 → a ∉ U2.map f2 := by
    intro a ha1 ha2
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha1
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp ha2
    have hcontra := ss_le1_two_endpoint_mod_disjoint e p hp hper u v (lag1 u) (lag2 v)
      (hSupply1 u hu).1 (hSupply2 v hv).1
      (hlag1 u hu).2.1 (hlag1 u hu).2.2.1 (hlag2 v hv).2.1 (hlag2 v hv).2.2.1
      (hlag1 u hu).1 (hlag2 v hv).1 heq.symm
    exact hcontra
  have h1nodup := LagElevenPeriodic.nodup_map_of_inj hU1nodup hinj1
  have h2nodup := LagElevenPeriodic.nodup_map_of_inj hU2nodup hinj2
  have hnodup := LagElevenPeriodic.nodup_append h1nodup h2nodup hdisj
  have hsub : (U1.map f1 ++ U2.map f2) ⊆ LagElevenPeriodic.subPhases e 0 p := by
    apply List.append_subset.mpr
    constructor
    · intro q hq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
      apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
      refine ⟨phase_lt p hp _, ?_⟩
      simpa [f1] using endpoint_is_S e p hp hper u (lag1 u) (hlag1 u hu).2.2.2
    · intro q hq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
      apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
      refine ⟨phase_lt p hp _, ?_⟩
      simpa [f2] using endpoint_is_S e p hp hper u (lag2 u) (hlag2 u hu).2.2.2
  have hlen := hnodup.length_le_of_subset hsub
  simp only [List.length_append, List.length_map] at hlen
  exact hlen

/-- Each SS=2 window with lag < 15 consumes 1 unit of capacity, strictly bounding
the number of low-SS additions to |U_{≤1}| ≤ |D| - |U₂|. -/
theorem ss2_strict_capacity_deficit (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U1 U2 : List Nat) (hU1nodup : U1.Nodup) (hU2nodup : U2.Nodup)
    (hU1range : ∀ u, u ∈ U1 → u < p) (hU2range : ∀ u, u ∈ U2 → u < p)
    (hSupply1 : ∀ u, u ∈ U1 → e u = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d) ≤ 1 ∧
      (ssCount (past e u d) = 0 → d = 3) ∧ e (u - d) = false)
    (hSupply2 : ∀ u, u ∈ U2 → e u = true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d) = 2 ∧
      d < 15 ∧ e (u - d) = false) :
    U1.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - U2.length := by
  have h := low_SS_two_SS_joint_capacity e p hp hper U1 U2 hU1nodup hU2nodup hU1range hU2range hSupply1 hSupply2
  omega

end Recaman.LowSSTwoSSJointCapacity
