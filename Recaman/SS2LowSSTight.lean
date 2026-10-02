import Recaman.SS2ShortTight

/-!
# Minimal SS2 donors avoid arbitrary-length low-SS tight sets

All windows use the actual newest-first history. The donor is minimal P2
with exactly two overlapping SS pairs. Members have SS at most one, with
no lag bound and no minimality assumption. Their S-ended prefix endpoints
give an injection inside their original neighborhood; tightness makes it
onto. No ambient Hall, NoSAAS, owner-distance or orbit hypothesis is used.
This says nothing about tight sets containing high-SS member windows.
-/

namespace Recaman.SS2LowSSTight

open LeadingRunSupply LowSSEndpoint LowSSPeriodicSupply SharpPeriodicSupply
open OneSSMultiplicity (ssCount)
open SS2ShortTight
open LagSevenDonorCoverage (oldestOffset past_getD)
open TwoSSLeadingSibling (past_length)
open TwoSSTightDisjoint (neighborhood)

/-- General P2 suffixes, not just AAS, force a proper P2 prefix in this
SS2/current-A/terminal-A configuration. -/
theorem ss2_P2_suffix_has_prefix (x v : List Bool) (n : Nat)
    (hv : P2 v)
    (hP : P2 (((x ++ [true]) ++ v) ++ List.replicate n true))
    (hss : ssCount (((x ++ [true]) ++ v) ++ List.replicate n true) ≤ 2) :
    ∃ a z : List Bool,
      ((x ++ [true]) ++ v) ++ List.replicate n true = (a ++ [false]) ++ z ∧
      P2 (a ++ [false]) ∧ z ≠ [] := by
  have hdata := p2_append_A_tail_data (x ++ [true]) v n hP hv
  have hsx : ssCount (x ++ [true]) ≤ 2 := by
    have hs := ssCount_append_left_le (x ++ [true]) (v ++ List.replicate n true)
    rw [← List.append_assoc] at hs
    omega
  cases n with
  | zero =>
    have hm : mass (x ++ [true]) = 0 := by simpa using hdata.1
    have hM : moment (x ++ [true]) + (x ++ [true]).length ≤ 0 := by
      have h := hdata.2
      simp only [List.replicate_zero, moment, Int.natCast_zero, Int.mul_zero,
        Int.add_zero] at h
      omega
    obtain ⟨a, z, heq, ha, _⟩ := ss2_intervening_prefix x hm hM hsx
    refine ⟨a, z ++ v, ?_, ha, ?_⟩
    · simp only [List.replicate_zero, List.append_nil, heq, List.append_assoc]
    · intro hz
      have hvnil := (List.append_eq_nil_iff.mp hz).2
      have hm := hv.1
      simp [hvnil] at hm
  | succ n =>
    have hbound := moment_ending_A_budget x 2 hsx
    have hM := hdata.2
    have hn := moment_replicate_A_nonneg (n + 1)
    have hprod : 0 ≤ (((x ++ [true]).length : Int) + v.length) * (n : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    have heq : (((x ++ [true]).length : Int) + v.length) * ((n + 1 : Nat) : Int) =
        (((x ++ [true]).length : Int) + v.length) * (n : Int) +
          (x ++ [true]).length + v.length := by
      push_cast
      grind
    rw [heq] at hM
    omega

/-- Integer endpoints are disjoint for all donor and supplier lengths.
The supplier's current A is in the same actual stream. -/
theorem oldest_ne_lowSS_endpoint (e : Int → Bool) (u : Int) (d : Nat)
    (hP : P2 (past e u d)) (hss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j))
    (t : Int) (l : Nat) (htA : e t = true)
    (htP : P2 (past e t l)) (htss : ssCount (past e t l) ≤ 1) :
    t - (l : Int) ≠ u - (oldestOffset (past e u d) : Int) := by
  intro hend
  have htu := oldest_cover_clock_lt e u t d l hss htss hend
  obtain ⟨x, hx⟩ := past_oldest_cover_decomposition e u t d l htu htA hend
  obtain ⟨a, z, hz, ha, hne⟩ := ss2_P2_suffix_has_prefix x (past e t l)
    (d - oldestOffset (past e u d)) htP (hx ▸ hP) (by rw [← hx, hss]; omega)
  have he : past e u d = (a ++ [false]) ++ z := hx.trans hz
  have hlen := congrArg List.length he
  rw [past_length, List.length_append] at hlen
  have hpos : 0 < z.length := List.length_pos_iff.mpr hne
  have htake : (past e u d).take (a ++ [false]).length = a ++ [false] := by
    rw [he, List.take_left]
  apply hmin (a ++ [false]).length (by simp) (by omega)
  rwa [htake]

theorem oldest_phase_ne_lowSS_endpoint (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u : Int) (d : Nat)
    (hP : P2 (past e u d)) (hss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j))
    (t : Int) (l : Nat) (htA : e t = true)
    (htP : P2 (past e t l)) (htss : ssCount (past e t l) ≤ 1) :
    endpointPhase p t l ≠ phase p (u - oldestOffset (past e u d)) := by
  intro heq
  have hmod := phase_eq_mod p hp (t-l) (u-oldestOffset (past e u d)) heq
  obtain ⟨z, hz⟩ := lift_equal_mod p _ _ hmod.symm
  apply oldest_ne_lowSS_endpoint e u d hP hss hmin (t+z*p) l
    (by rw [LagElevenPeriodic.e_shift e p hper]; exact htA)
    (by rw [past_shift e p hper]; exact htP)
    (by rw [past_shift e p hper]; exact htss)
  omega

/-- Normalize inside each supplied window, retaining the real endpoint
image and its injection into the original subtraction neighborhood. -/
theorem lowSS_endpoint_image (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (A : List Nat) (lag : Nat → Nat)
    (hAn : A.Nodup) (hAp : ∀ b ∈ A, b < p) (hA : ∀ b ∈ A, e (b : Int) = true)
    (hP : ∀ b ∈ A, P2 (past e (b : Int) (lag b)))
    (hss : ∀ b ∈ A, ssCount (past e (b : Int) (lag b)) ≤ 1) :
    ∃ f : Nat → Nat,
      (A.map (fun b : Nat => endpointPhase p (b : Int) (f b))).Nodup ∧
      (∀ b ∈ A, 0 < f b ∧ f b ≤ lag b ∧ P2 (past e (b : Int) (f b)) ∧
        ssCount (past e (b : Int) (f b)) ≤ 1 ∧ e ((b : Int)-f b) = false) ∧
      A.map (fun b : Nat => endpointPhase p (b : Int) (f b)) ⊆ neighborhood e p A lag := by
  classical
  have hex : ∀ b ∈ A, ∃ f : Nat, 0 < f ∧ f ≤ lag b ∧
      P2 (past e (b : Int) f) ∧ ssCount (past e (b : Int) f) ≤ 1 ∧
      e ((b : Int)-f) = false := by
    intro b hb
    obtain ⟨f, hf, hfl, hfP, hfss, hfS⟩ := stream_S_witness e b (lag b)
      ((past_p2_iff e b (lag b)).mp (hP b hb)) (hss b hb)
    exact ⟨f, hf, hfl, (past_p2_iff e b f).mpr hfP, hfss, hfS⟩
  let f := fun b : Nat => if hb : b ∈ A then Classical.choose (hex b hb) else 0
  have hf : ∀ b ∈ A, 0 < f b ∧ f b ≤ lag b ∧ P2 (past e (b : Int) (f b)) ∧
      ssCount (past e (b : Int) (f b)) ≤ 1 ∧ e ((b : Int)-f b) = false := by
    intro b hb
    dsimp [f]
    rw [dif_pos hb]
    exact Classical.choose_spec (hex b hb)
  refine ⟨f, ?_, hf, ?_⟩
  · apply LagElevenPeriodic.nodup_map_of_inj hAn
    intro a b ha hb heq
    have hmod := endpoint_mod_injective e p hp hper a b (f a) (f b)
      (hA a ha) (hA b hb) (hf a ha).2.2.2.1 (hf b hb).2.2.2.1
      ((past_p2_iff e a (f a)).mp (hf a ha).2.2.1)
      ((past_p2_iff e b (f b)).mp (hf b hb).2.2.1) heq
    have hal := hAp a ha
    have hbl := hAp b hb
    rw [Int.emod_eq_of_lt (by omega) (by omega),
      Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  · intro s hs
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
    have hbdata := hf b hb
    rw [TwoSSAvoidTight.mem_neighborhood_iff]
    constructor
    · apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
      exact ⟨phase_lt p hp _, by simpa using endpoint_is_S e p hp hper b (f b) hbdata.2.2.2.2⟩
    · rw [TwoSSTightDisjoint.isCoveredBySubset_iff]
      refine ⟨b, hb, f b - 1, by omega, ?_, ?_⟩
      · have he : (b : Int)-1-((f b-1 : Nat) : Int) = (b : Int)-f b := by omega
        rw [he]
        exact hbdata.2.2.2.2
      · have he : (b : Int)-1-((f b-1 : Nat) : Int) = (b : Int)-f b := by omega
        rw [he]
        exact (phase_cast p hp _).symm

/-- Tightness derives endpoint surjectivity for this low-SS class. There
is no lag cutoff, assumed Hall condition, or assumed owner map. -/
theorem lowSS_tight_avoids_donor (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (B : List Nat) (lag : Nat → Nat)
    (hBn : B.Nodup) (hBp : ∀ b ∈ B, b < p) (hA : ∀ b ∈ B, e (b : Int) = true)
    (hP : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hss : ∀ b ∈ B, ssCount (past e (b : Int) (lag b)) ≤ 1)
    (htight : (neighborhood e p B lag).length = B.length)
    (u : Int) (d : Nat) (huP : P2 (past e u d)) (huss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j)) :
    phase p (u - oldestOffset (past e u d)) ∉ neighborhood e p B lag := by
  obtain ⟨f, hn, hf, hsub⟩ := lowSS_endpoint_image e p hp hper B lag hBn hBp hA hP hss
  intro hmem
  have hlen : (B.map (fun b : Nat => endpointPhase p (b : Int) (f b))).length =
      (neighborhood e p B lag).length := by rw [List.length_map, htight]
  have him := TightSubsetDecomposition.mem_of_subset_nodup_length_eq hsub hn hlen hmem
  obtain ⟨b, hb, heq⟩ := List.mem_map.mp him
  exact oldest_phase_ne_lowSS_endpoint e p hp hper u d huP huss hmin b (f b)
    (hA b hb) (hf b hb).2.2.1 (hf b hb).2.2.2.1 heq

/-- A positive recursive oldest offset selects an actual S, for any word. -/
theorem oldestOffset_getD (w : List Bool) (hpos : 0 < oldestOffset w) :
    w.getD (oldestOffset w - 1) true = false := by
  induction w with
  | nil => simp [oldestOffset] at hpos
  | cons b w ih =>
    by_cases h0 : oldestOffset w = 0
    · cases b <;> simp_all [oldestOffset]
    · have hp : 0 < oldestOffset w := by omega
      have he : oldestOffset w = (oldestOffset w - 1) + 1 := by omega
      simp only [oldestOffset, h0, if_false, Nat.add_sub_cancel]
      rw [he, List.getD_cons_succ]
      exact ih hp

/-- Positive SS count ensures the selected oldest S lies inside the word. -/
theorem oldestOffset_pos_of_ss_pos (w : List Bool) (hss : 0 < ssCount w) :
    0 < oldestOffset w := by
  by_cases hn : 0 < oldestOffset w
  · exact hn
  have h0 : oldestOffset w = 0 := by omega
  have hw : w = List.replicate w.length true := by
    simpa [h0] using oldestOffset_split w
  have hs : ssCount (List.replicate w.length true) = 0 := by
    simpa [ssCount] using ssCount_append_replicate_A [] w.length
  rw [hw, hs] at hss
  omega

theorem donor_oldest_is_S (e : Int → Bool) (u : Int) (d : Nat)
    (hss : 0 < ssCount (past e u d)) :
    e (u - oldestOffset (past e u d)) = false := by
  have hp := oldestOffset_pos_of_ss_pos (past e u d) hss
  have hb := oldestOffset_le_length (past e u d)
  rw [past_length] at hb
  have hs := oldestOffset_getD (past e u d) hp
  rw [past_getD e u d _ (by omega) true] at hs
  have he : u - 1 - ((oldestOffset (past e u d) - 1 : Nat) : Int) =
      u - oldestOffset (past e u d) := by omega
  rwa [he] at hs

/-- One minimal SS2 donor supplies one S phase outside the low-SS endpoint
image. The statement does not add one unit per donor. -/
theorem lowSS_strict_capacity (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (U : List Nat) (lag : Nat → Nat)
    (hUn : U.Nodup) (hUp : ∀ b ∈ U, b < p) (hA : ∀ b ∈ U, e (b : Int) = true)
    (hP : ∀ b ∈ U, P2 (past e (b : Int) (lag b)))
    (hss : ∀ b ∈ U, ssCount (past e (b : Int) (lag b)) ≤ 1)
    (u : Int) (d : Nat) (huP : P2 (past e u d)) (huss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j)) :
    U.length + 1 ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  obtain ⟨f, hn, hf, hsub⟩ := lowSS_endpoint_image e p hp hper U lag hUn hUp hA hP hss
  let s := phase p (u - oldestOffset (past e u d))
  have hs : s ∈ LagElevenPeriodic.subPhases e 0 p := by
    apply (LagElevenPeriodic.mem_subPhases e 0 p s).mpr
    refine ⟨phase_lt p hp _, ?_⟩
    simpa [s, endpointPhase] using endpoint_is_S e p hp hper u
      (oldestOffset (past e u d)) (donor_oldest_is_S e u d (by omega))
  have hnot : s ∉ U.map (fun b : Nat => endpointPhase p (b : Int) (f b)) := by
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact oldest_phase_ne_lowSS_endpoint e p hp hper u d huP huss hmin b (f b)
      (hA b hb) (hf b hb).2.2.1 (hf b hb).2.2.2.1 he
  have hnodup := List.nodup_cons.mpr ⟨hnot, hn⟩
  have hsub' : s :: U.map (fun b : Nat => endpointPhase p (b : Int) (f b)) ⊆
      LagElevenPeriodic.subPhases e 0 p := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hm
    · exact hs
    · have hxN := hsub hm
      rw [TwoSSAvoidTight.mem_neighborhood_iff] at hxN
      exact hxN.1
  have hlen := hnodup.length_le_of_subset hsub'
  simpa using hlen

end Recaman.SS2LowSSTight
