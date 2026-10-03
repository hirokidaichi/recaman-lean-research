import Recaman.PeriodicOwnerFamilyLagEleven
import Recaman.PairedSubtractionCoverage
import Recaman.TrueOldestGateT6
import Recaman.ShortReservoirCapacity

/-!
# Short tight subsets avoid a lag-11 SS=2 donor's true oldest subtraction

The new local input is that a w1 member of an owner family has next sign A.
Hall is a hypothesis in the periodic consequence, and all member windows of the tight
subset have minimal lag 3, 7 or 11. There is no upper bound on the period.
The existing short injection also supplies Hall on each short subset, so the final
corollaries have no Hall assumption. This does not establish all-lag capacity,
general Gate T6, or an orbit claim.
-/

namespace Recaman.ShortTightDonorAvoidance

open Recaman.LeadingRunSupply (past P2)
open Recaman.OwnerFamilyLagEleven
open Recaman.LagSevenPrefixRigidity (w1 w2)
open Recaman.LagSevenDonorCoverage (past_getD donors oldestOffset)
open Recaman.TwoSSLeadingSibling (past_length)
open Recaman.PairedSubtractionCoverage
open Recaman.PeriodicOwnerFamilyLagEleven
open Recaman.SharpPeriodicSupply (phase)
open Recaman.TwoSSTightDisjoint (neighborhood)

/-- The existing short injection charges a subtraction inside the actual supplied window,
not just somewhere among the period's subtraction phases. -/
theorem shortOff_le_window (e : Int → Bool) (p u d : Nat) (hu : u < p)
    (hA : e (u : Int) = true) (hd : d ≤ 11) (hP : P2 (past e (u : Int) d)) :
    1 ≤ Recaman.ShortReservoirCapacity.shortOff e u ∧
      Recaman.ShortReservoirCapacity.shortOff e u ≤ d := by
  have hPs := (Recaman.LeadingRunSupply.past_p2_iff e (u : Int) d).mp hP
  have hmem := (Recaman.ShortReservoirCapacity.mem_shortPhases e p u).mpr
    ⟨hu, hA, d, hd, hPs⟩
  have hb := Recaman.ShortReservoirCapacity.shortOff_bounds e p u hmem
  refine ⟨hb.1, ?_⟩
  rcases Recaman.ShortReservoirCapacity.small_P2_lags e (u : Int) d hd hPs with h3 | h7 | h11
  · subst d
    have haas := Recaman.TightP2ParityRigidity.aas_of_past_three_eq e (u : Int)
      (Recaman.TightP2ParityRigidity.p2_length_three_eq_aas _ (past_length e _ 3) hP)
    have hs := (Recaman.ShortPeriodicSupply.supplied_window_iff e (u : Int)).mpr
      ⟨3, by decide, by decide, hPs⟩
    have hwin : Recaman.LagElevenPeriodic.isLag3Win (Recaman.ShortPeriodicSupply.window e u) = true := by
      simp only [Recaman.LagElevenPeriodic.isLag3Win,
        Recaman.ShortPeriodicSupply.window_bit e (u : Int) 0 (by decide),
        Recaman.ShortPeriodicSupply.window_bit e (u : Int) 1 (by decide),
        Recaman.ShortPeriodicSupply.window_bit e (u : Int) 2 (by decide)]
      simpa using And.intro (And.intro haas.1 haas.2.1) haas.2.2
    simp [Recaman.ShortReservoirCapacity.shortOff, hs, Recaman.LagElevenPeriodic.phi7Off, hwin]
  · subst d
    have hs := (Recaman.ShortPeriodicSupply.supplied_window_iff e (u : Int)).mpr
      ⟨7, by decide, by decide, hPs⟩
    have h := (Recaman.LagElevenPeriodic.phi7Off_bounds hs).2
    simpa only [Recaman.ShortReservoirCapacity.shortOff, hs, ↓reduceIte] using h
  · omega

/-- Hall on an arbitrary list of short supplied windows follows from the established
short injection and its image lying in that list's actual neighborhood. -/
theorem short_window_hall (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (A : List Nat) (lag : Nat → Nat)
    (hAn : A.Nodup) (hAp : ∀ u ∈ A, u < p) (hA : ∀ u ∈ A, e (u : Int) = true)
    (hlag : ∀ u ∈ A, lag u ≤ 11) (hP : ∀ u ∈ A, P2 (past e (u : Int) (lag u))) :
    A.length ≤ (neighborhood e p A lag).length := by
  let f := fun u : Nat => phase p ((u : Int) - Recaman.ShortReservoirCapacity.shortOff e u)
  have hm : ∀ u ∈ A, u ∈ Recaman.ShortReservoirCapacity.shortPhases e p := by
    intro u hu
    apply (Recaman.ShortReservoirCapacity.mem_shortPhases e p u).mpr
    exact ⟨hAp u hu, hA u hu, lag u, hlag u hu,
      (Recaman.LeadingRunSupply.past_p2_iff e (u : Int) (lag u)).mp (hP u hu)⟩
  have hn : (A.map f).Nodup := Recaman.LagElevenPeriodic.nodup_map_of_inj hAn
    (fun u v hu hv heq => Recaman.ShortReservoirCapacity.short_phase_injective
      e p hp hper u v (hm u hu) (hm v hv) heq)
  have himage : A.map f ⊆ neighborhood e p A lag := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
    have hb := shortOff_le_window e p u (lag u) (hAp u hu) (hA u hu) (hlag u hu) (hP u hu)
    have hsub := Recaman.ShortReservoirCapacity.short_image_is_S e p hp hper u (hm u hu)
    rw [Recaman.TwoSSAvoidTight.mem_neighborhood_iff]
    constructor
    · apply (Recaman.LagElevenPeriodic.mem_subPhases e 0 p (f u)).mpr
      exact ⟨Recaman.SharpPeriodicSupply.phase_lt p hp _, by simpa [f] using hsub⟩
    · rw [Recaman.TwoSSTightDisjoint.isCoveredBySubset_iff]
      refine ⟨u, hu, Recaman.ShortReservoirCapacity.shortOff e u - 1, by omega, ?_, ?_⟩
      · have hx : (u : Int) - 1 - ((Recaman.ShortReservoirCapacity.shortOff e u - 1 : Nat) : Int) =
            (u : Int) - (Recaman.ShortReservoirCapacity.shortOff e u : Int) := by omega
        rw [hx]
        rw [e_phase e p hp hper] at hsub
        exact hsub
      · have hx : (u : Int) - 1 - ((Recaman.ShortReservoirCapacity.shortOff e u - 1 : Nat) : Int) =
            (u : Int) - (Recaman.ShortReservoirCapacity.shortOff e u : Int) := by omega
        rw [hx]
        exact (Recaman.SharpPeriodicSupply.phase_cast p hp _).symm
  have hlen := hn.length_le_of_subset himage
  simpa only [List.length_map] using hlen

/-- Existing exclusions leave precisely AAS and w1 in a short owner family. -/
theorem member_window_aas_or_w1 (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t) :
    past e t (lag t) = aas ∨ past e t (lag t) = w1 := by
  have hw := hF.window t ht
  have h11 := no_lag_eleven_member e mem own lag hF t ht
  have hw2 := no_w2_member e mem own lag hF t ht
  have hlen := past_length e t (lag t)
  simp only [ownerWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hw2 h).elim
  all_goals exfalso; apply h11; rw [h] at hlen; exact hlen.symm

/-- A w1 member must own its oldest S: only that same member can cover the older SS bit. -/
theorem w1_owns_oldest (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : own t = t - 7 := by
  have hlen : lag t = 7 := by
    have h := congrArg List.length hw
    simpa only [past_length, w1, List.length_cons, List.length_nil] using h
  have hw7 : past e t 7 = w1 := by simpa only [hlen] using hw
  have hs : PairedOlderS e (t - 7) := by
    constructor
    · have h := past_getD e t 7 6 (by decide) true
      rw [hw7] at h
      simpa [w1, show t - 1 - (6 : Int) = t - 7 by omega] using h.symm
    · have h := past_getD e t 7 5 (by decide) true
      rw [hw7] at h
      simpa [w1, show t - 1 - (5 : Int) = t - 7 + 1 by omega] using h.symm
  have hk : 7 ∈ sOffsets (past e t (lag t)) := by rw [hw]; decide
  obtain ⟨v, hv, hvown⟩ := hF.onto t ht 7 hk
  obtain ⟨k, hkv, hown⟩ := hF.own_mem v hv
  rw [sOffsets_mem, past_length] at hkv
  rcases member_window_aas_or_w1 e mem own lag hF v hv with ha | h1
  · have hvlen : lag v = 3 := by
      have h := congrArg List.length ha
      simpa only [past_length, aas, List.length_cons, List.length_nil] using h
    have ha3 : past e v 3 = [true, true, false] := by simpa only [hvlen, aas] using ha
    exact (aas_window_no_paired_older e v (t - 7) ha3 (hF.addA v hv) hs
      ⟨k - 1, by omega, by omega⟩).elim
  · have hvlen : lag v = 7 := by
      have h := congrArg List.length h1
      simpa only [past_length, w1, List.length_cons, List.length_nil] using h
    have h17 : past e v 7 = w1 := by simpa only [hvlen] using h1
    have heq := (lag7_window_paired_older e v (t - 7) (Or.inl h17) (hF.addA v hv)
      hs ⟨k - 1, by omega, by omega⟩).2
    have hvt : v = t := by omega
    simpa [hvt] using hvown

/-- The newest S of w1 has the AAS member two clocks later as its owner.
This is an actual member and ownership statement, not just a next-sign claim. -/
theorem w1_future_aas_member (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) :
    mem (t + 2) ∧ lag (t + 2) = 3 ∧ past e (t + 2) 3 = aas ∧ own (t + 2) = t - 1 := by
  have ho := w1_owns_oldest e mem own lag hF t ht hw
  have hlen : lag t = 7 := by
    have h := congrArg List.length hw
    simpa only [past_length, w1, List.length_cons, List.length_nil] using h
  have hw7 : past e t 7 = w1 := by simpa only [hlen] using hw
  have hk : 1 ∈ sOffsets (past e t (lag t)) := by rw [hw]; decide
  obtain ⟨v, hv, hvown⟩ := hF.onto t ht 1 hk
  obtain ⟨k, hkv, hown⟩ := hF.own_mem v hv
  rcases member_window_aas_or_w1 e mem own lag hF v hv with ha | h1
  · rw [ha] at hkv
    have hoff : sOffsets aas = [3] := by decide
    have hk3 : k = 3 := by simpa only [hoff, List.mem_singleton] using hkv
    have hvlen : lag v = 3 := by
      have h := congrArg List.length ha
      simpa only [past_length, aas, List.length_cons, List.length_nil] using h
    have hvpos : v = t + 2 := by omega
    have ha3 : past e v 3 = aas := by simpa only [hvlen] using ha
    subst v
    exact ⟨hv, hvlen, ha3, hvown⟩
  · rw [h1] at hkv
    have hoff : sOffsets w1 = [1, 6, 7] := by decide
    have hkcases : k = 1 ∨ k = 6 ∨ k = 7 := by simp only [hoff, List.mem_cons, List.not_mem_nil, or_false] at hkv; exact hkv
    have hvlen : lag v = 7 := by
      have h := congrArg List.length h1
      simpa only [past_length, w1, List.length_cons, List.length_nil] using h
    have hv7 : past e v 7 = w1 := by simpa only [hvlen] using h1
    rcases hkcases with hk1 | hk6 | hk7
    · have hvt : v = t := by omega
      rw [hvt, ho] at hvown
      omega
    · have hs := past_getD e v 7 6 (by decide) true
      have ha := past_getD e t 7 1 (by decide) true
      rw [hv7] at hs
      rw [hw7] at ha
      have hx : v - 1 - (6 : Int) = t - 1 - (1 : Int) := by omega
      simp [w1] at hs ha
      rw [hx, ha] at hs
      contradiction
    · have hs := past_getD e v 7 5 (by decide) true
      rw [hv7] at hs
      have hx : v - 1 - (5 : Int) = t := by omega
      simp [w1] at hs
      rw [hx, hF.addA t ht] at hs
      contradiction

/-- The forced future AAS member puts A at the next clock of w1. -/
theorem w1_next_addition (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : e (t + 1) = true := by
  obtain ⟨_, _, ha, _⟩ := w1_future_aas_member e mem own lag hF t ht hw
  have h := past_getD e (t + 2) 3 0 (by decide) true
  rw [ha] at h
  simpa [aas, show t + 2 - 1 = t + 1 by omega] using h.symm

/-- The local future-sign theorem transported to any periodic tight subset of short windows. -/
theorem tight_w1_next_addition (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U B : List Nat) (lag : Nat → Nat) (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p)
    (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d))
    (t : Int) (ht : phase p t ∈ B)
    (hw : past e t (lag (phase p t)) = w1) : e (t + 1) = true := by
  obtain ⟨own, hF⟩ := tight_owner_family e p hp hper U B lag hU hhall hB htight
    hBp hB_A hB_lag hB_P2 hB_min
  exact w1_next_addition e _ own _ hF t ht hw

/-- All three donor/w1 overlaps force S at the next clock of the covering w1. -/
theorem donor_cover_next_subtraction (e : Int → Bool) (u0 t : Int)
    (hdon : past e u0 11 ∈ donors) (htA : e t = true)
    (hw : past e t 7 = w1)
    (hcov : ∃ k : Nat, k < 7 ∧ e (t - 1 - (k : Int)) = false ∧
      t - 1 - (k : Int) = u0 - (oldestOffset (past e u0 11) : Int)) :
    e (t + 1) = false := by
  obtain ⟨_, hpos, hd⟩ := Recaman.LagSevenDonorCoverage.lag7_cover_classification
    e u0 t hdon htA (Or.inl hw) hcov
  have htab : ∀ w ∈ [Recaman.LagSevenDonorCoverage.d1, Recaman.LagSevenDonorCoverage.d2,
      Recaman.LagSevenDonorCoverage.d4], w.getD (oldestOffset w - 3) true = false := by decide
  have hmem : past e u0 11 ∈ [Recaman.LagSevenDonorCoverage.d1,
      Recaman.LagSevenDonorCoverage.d2, Recaman.LagSevenDonorCoverage.d4] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hd
  have hb := htab _ hmem
  have hbounds : 10 ≤ oldestOffset (past e u0 11) ∧ oldestOffset (past e u0 11) ≤ 11 := by
    rcases Recaman.TrueOldestGateT6.donor_oldestOffset e u0 hdon with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  rw [past_getD e u0 11 _ (by omega)] at hb
  have hx : u0 - 1 - ((oldestOffset (past e u0 11) - 3 : Nat) : Int) = t + 1 := by omega
  rwa [hx] at hb

set_option maxHeartbeats 1000000 in
/-- Any lag-11 SS=2 donor avoids every periodic tight subset whose minimal windows have
lengths 3/7/11. Hall is assumed. Neither full U nor positive period mass is needed. -/
theorem short_tight_avoids_trueOldest (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U B : List Nat) (lag : Nat → Nat) (hU : U.Nodup)
    (hhall : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hB : List.Sublist B U)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p)
    (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Nat) (hdon : past e (u0 : Int) 11 ∈ donors) :
    Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉ neighborhood e p B lag := by
  obtain ⟨own, hF⟩ := tight_owner_family e p hp hper U B lag hU hhall hB htight
    hBp hB_A hB_lag hB_P2 hB_min
  intro hcovered
  rw [Recaman.TwoSSAvoidTight.mem_neighborhood_iff,
    Recaman.TwoSSTightDisjoint.isCoveredBySubset_iff] at hcovered
  obtain ⟨_, b, hb, i, hi, he, hmod⟩ := hcovered
  let s : Int := (u0 : Int) - (oldestOffset (past e (u0 : Int) 11) : Int)
  let t : Int := s + 1 + (i : Int)
  have hmod' : ((b : Int) - 1 - (i : Int)) % (p : Int) = s % (p : Int) := by
    change ((b : Int) - 1 - (i : Int)) % (p : Int) = (phase p s : Int) at hmod
    rw [Recaman.SharpPeriodicSupply.phase_cast p hp] at hmod
    exact hmod
  have htmod : t % (p : Int) = (b : Int) % (p : Int) :=
    emod_congr p _ _ _ _ hmod'.symm (by dsimp [t]; omega)
  have htphase : phase p t = b := phase_eq_of_emod p hp t b (hBp b hb) htmod
  have ht : phase p t ∈ B := by simpa only [htphase] using hb
  have hts : t - 1 - (i : Int) = s := by dsimp [t]; omega
  have het : e (t - 1 - (i : Int)) = false := by
    rw [e_of_emod_eq e p hper _ ((b : Int) - 1 - (i : Int))
      (emod_congr p _ _ _ _ htmod (by omega))]
    exact he
  have hi' : i < lag (phase p t) := by simpa only [htphase] using hi
  have hso : i + 1 ∈ sOffsets (past e t (lag (phase p t))) := by
    rw [sOffsets_mem, past_length]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel, past_getD e t _ i hi']
    exact het
  rcases member_window_aas_or_w1 e _ own _ hF t ht with ha | hw
  · have hoff : sOffsets aas = [3] := by decide
    rw [ha, hoff, List.mem_singleton] at hso
    have hi2 : i = 2 := by omega
    have hlen : lag (phase p t) = 3 := by
      have h := congrArg List.length ha
      simpa only [past_length, aas, List.length_cons, List.length_nil] using h
    have hat : past e t 3 = aas := by simpa only [hlen] using ha
    have hab : past e (b : Int) 3 = aas :=
      (past_of_emod_eq e p hper t (b : Int) htmod 3).symm.trans hat
    have h1 := past_getD e (b : Int) 3 0 (by decide) true
    have h2 := past_getD e (b : Int) 3 1 (by decide) true
    have h3 := past_getD e (b : Int) 3 2 (by decide) true
    rw [hab] at h1 h2 h3
    have haas : e ((b : Int) - 1) = true ∧ e ((b : Int) - 2) = true ∧
        e ((b : Int) - 3) = false := by
      simp [aas] at h1 h2 h3
      have hx2 : (b : Int) - 1 - 1 = (b : Int) - 2 := by omega
      have hx3 : (b : Int) - 1 - 2 = (b : Int) - 3 := by omega
      exact ⟨h1, hx2 ▸ h2, hx3 ▸ h3⟩
    have hneq := Recaman.TrueOldestGateT6.aas_endpoint_ne_trueOldest
      e p hp hper u0 b hdon (hB_A b hb) haas
    apply hneq
    have heq := congrArg Int.toNat hmod
    subst hi2
    simp at heq
    rw [show (b : Int) - 1 - 2 = (b : Int) - 3 by omega] at heq
    exact heq
  · have hlen : lag (phase p t) = 7 := by
      have h := congrArg List.length hw
      simpa only [past_length, w1, List.length_cons, List.length_nil] using h
    have hw7 : past e t 7 = w1 := by simpa only [hlen] using hw
    have hnextA := w1_next_addition e _ own _ hF t ht hw
    have hnextS := donor_cover_next_subtraction e (u0 : Int) t hdon (hF.addA t ht) hw7
      ⟨i, by omega, het, hts⟩
    rw [hnextA] at hnextS
    contradiction

/-- Semantic donor statement, with Hall discharged by the existing short injection.
There is no ambient supply set and no period bound. The tight subset itself must have
minimal P2 windows of lengths 3, 7 or 11. -/
theorem short_tight_avoids_ss2_donor (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat) (hBn : B.Nodup)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p)
    (hB_A : ∀ b ∈ B, e (b : Int) = true)
    (hB_lag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hB_P2 : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hB_min : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11))
    (hmindon : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2) :
    Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11 ∉ neighborhood e p B lag := by
  have hbound : ∀ b ∈ B, lag b ≤ 11 := by
    intro b hb
    rcases hB_lag b hb with h | h | h <;> omega
  have hhall : ∀ A : List Nat, List.Sublist A B → A.length ≤ (neighborhood e p A lag).length := by
    intro A hA
    exact short_window_hall e p hp hper A lag (hBn.sublist hA)
      (fun u hu => hBp u (hA.subset hu)) (fun u hu => hB_A u (hA.subset hu))
      (fun u hu => hbound u (hA.subset hu)) (fun u hu => hB_P2 u (hA.subset hu))
  have hdon := Recaman.LagSevenDonorCoverage.minimal_ss2_eleven_mem_donors
    (past e (u0 : Int) 11) (past_length e _ 11) hPdon
    (fun d hd hd0 => hmindon d (by simpa only [past_length] using hd) hd0) hss
  exact short_tight_avoids_trueOldest e p hp hper B B lag hBn hhall
    (List.Sublist.refl B) htight hBp hB_A hB_lag hB_P2 hB_min u0 hdon

/-- Removing the true oldest S of a minimal lag-11 SS=2 donor preserves Hall for
every sublist of any short minimal supply list, at every period. The short-lag
restriction is on all of U; it is not a theorem about the full all-lag supply set. -/
theorem short_supply_donor_deletion (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (hUn : U.Nodup)
    (hUp : ∀ u ∈ U, u < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (hU_lag : ∀ u ∈ U, lag u = 3 ∨ lag u = 7 ∨ lag u = 11)
    (hU_P2 : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hU_min : ∀ u ∈ U, ∀ d, d < lag u → 0 < d → ¬ P2 ((past e (u : Int) (lag u)).take d))
    (u0 : Nat) (hPdon : P2 (past e (u0 : Int) 11))
    (hmindon : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e (u0 : Int) 11).take d))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e (u0 : Int) 11) = 2)
    (B : List Nat) (hBU : List.Sublist B U) :
    B.length ≤ (Recaman.TwoSSTightDisjoint.deletedNeighborhood e p B lag
      (Recaman.TrueOldestGateT6.trueOldestPhase e p u0 11)).length := by
  have hBp := fun b hb => hUp b (hBU.subset hb)
  have hBA := fun b hb => hU_A b (hBU.subset hb)
  have hBlag := fun b hb => hU_lag b (hBU.subset hb)
  have hBP := fun b hb => hU_P2 b (hBU.subset hb)
  have hBmin := fun b hb => hU_min b (hBU.subset hb)
  have hBn := hUn.sublist hBU
  have hbound : ∀ b ∈ B, lag b ≤ 11 := by
    intro b hb
    rcases hBlag b hb with h | h | h <;> omega
  have hhall := short_window_hall e p hp hper B lag hBn hBp hBA hbound hBP
  by_cases htight : (neighborhood e p B lag).length = B.length
  · apply Recaman.TwoSSAvoidTight.deleted_hall_of_not_mem e p B lag _ _ hhall
    exact short_tight_avoids_ss2_donor e p hp hper B lag hBn htight hBp hBA hBlag hBP hBmin
      u0 hPdon hmindon hss
  · exact Recaman.TwoSSAvoidTight.deleted_hall_of_slack e p B lag _ (by omega)

/-- All length-11 P2 words with two overlapping SS pairs, including nonminimal words. -/
def ss2Windows : List (List Bool) :=
  (Recaman.TwoSSEndpoint.bitWords 11).filter fun w =>
    Recaman.LagSevenPrefixRigidity.isP2Word w && Recaman.OneSSMultiplicity.ssCount w == 2

/-- Semantic membership requires P2 and SS count 2; no minimality premise. -/
theorem mem_ss2Windows (w : List Bool) (hlen : w.length = 11) (hP : P2 w)
    (hss : Recaman.OneSSMultiplicity.ssCount w = 2) : w ∈ ss2Windows := by
  apply List.mem_filter.mpr
  constructor
  · have h := Recaman.TwoSSEndpoint.mem_bitWords w
    rwa [hlen] at h
  · simp [Recaman.LagSevenPrefixRigidity.isP2Word, hP.1, hP.2, hss]

set_option maxRecDepth 100000 in
/-- The finite obstruction for all twelve words: AAS cannot cover oldest S;
a w1 cover has its newest S there, and its next or second-next sign is S. -/
theorem ss2_oldest_cover_table :
    ∀ w ∈ ss2Windows,
      (10 ≤ oldestOffset w ∧ oldestOffset w ≤ 11) ∧
      Recaman.TrueOldestGateT6.aasClash w = false ∧
      ∀ k ∈ List.range 7,
        Recaman.LagSevenDonorCoverage.coverOK w w1 (oldestOffset w) k = true →
          k = 0 ∧ (w.getD (oldestOffset w - 3) true = false ∨
            w.getD (oldestOffset w - 4) true = false) := by
  decide

/-- No member of a short owner family covers the oldest subtraction of an arbitrary
lag-11 P2 SS=2 window. Donor minimality and donor-current-A are not assumed. -/
theorem owner_member_avoids_ss2_window (e : Int → Bool) (mem : Int → Prop)
    (own : Int → Int) (lag : Int → Nat) (hF : OwnerFamily e mem own lag)
    (u0 : Int) (hP : P2 (past e u0 11))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e u0 11) = 2)
    (t : Int) (ht : mem t) (k : Nat)
    (hk : k < lag t) (hS : e (t - 1 - (k : Int)) = false) :
    t - 1 - (k : Int) ≠ u0 - (oldestOffset (past e u0 11) : Int) := by
  intro hpos
  have hdon := mem_ss2Windows _ (past_length e u0 11) hP hss
  obtain ⟨hb, hclash, hcover⟩ := ss2_oldest_cover_table _ hdon
  rcases member_window_aas_or_w1 e mem own lag hF t ht with ha | hw
  · have hlen : lag t = 3 := by
      have h := congrArg List.length ha
      simpa only [past_length, aas, List.length_cons, List.length_nil] using h
    have ha3 : past e t 3 = aas := by simpa only [hlen] using ha
    have hbit : aas.getD k true = false := by
      rw [← ha3, past_getD e t 3 k (by omega)]
      exact hS
    have hk2 : k = 2 := by
      have hr : k < 3 := by omega
      match k with
      | 0 => simp [aas] at hbit
      | 1 => simp [aas] at hbit
      | 2 => rfl
      | n + 3 => omega
    have hA1 := past_getD e t 3 0 (by decide) true
    have hA2 := past_getD e t 3 1 (by decide) true
    rw [ha3] at hA1 hA2
    simp [aas] at hA1 hA2
    unfold Recaman.TrueOldestGateT6.aasClash at hclash
    rw [past_getD e u0 11 _ (by omega) true,
      past_getD e u0 11 _ (by omega) true] at hclash
    have hx1 : u0 - 1 - ((oldestOffset (past e u0 11) - 3 : Nat) : Int) = t - 1 := by omega
    have hx2 : u0 - 1 - ((oldestOffset (past e u0 11) - 2 : Nat) : Int) = t - 1 - 1 := by omega
    rw [hx1, hx2, hA1, hA2] at hclash
    contradiction
  · have hlen : lag t = 7 := by
      have h := congrArg List.length hw
      simpa only [past_length, w1, List.length_cons, List.length_nil] using h
    have hw7 : past e t 7 = w1 := by simpa only [hlen] using hw
    have hok := Recaman.LagSevenDonorCoverage.coverOK_of_stream
      e u0 t (oldestOffset (past e u0 11)) k (hF.addA t ht) hpos
    rw [hw7] at hok
    obtain ⟨hk0, hfalse⟩ := hcover k (List.mem_range.mpr (by omega)) hok
    have hA1 := w1_next_addition e mem own lag hF t ht hw
    obtain ⟨hfuture, _, _, _⟩ := w1_future_aas_member e mem own lag hF t ht hw
    have hA2 := hF.addA (t + 2) hfuture
    rcases hfalse with hfalse | hfalse
    · rw [past_getD e u0 11 _ (by omega) true] at hfalse
      have hx : u0 - 1 - ((oldestOffset (past e u0 11) - 3 : Nat) : Int) = t + 1 := by omega
      rw [hx, hA1] at hfalse
      contradiction
    · rw [past_getD e u0 11 _ (by omega) true] at hfalse
      have hx : u0 - 1 - ((oldestOffset (past e u0 11) - 4 : Nat) : Int) = t + 2 := by omega
      rw [hx, hA2] at hfalse
      contradiction

/-- Arbitrary-period tight-set avoidance for all length-11 P2 SS=2 windows.
Only the members of B, not the donor, are required to have minimal windows.
The donor clock may be any integer and need not itself be an addition. -/
theorem short_tight_avoids_ss2_window (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat) (hBn : B.Nodup)
    (htight : (neighborhood e p B lag).length = B.length)
    (hBp : ∀ b ∈ B, b < p)
    (hBA : ∀ b ∈ B, e (b : Int) = true)
    (hlag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hP : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hmin : ∀ b ∈ B, ∀ d, d < lag b → 0 < d → ¬ P2 ((past e (b : Int) (lag b)).take d))
    (u0 : Int) (hPdon : P2 (past e u0 11))
    (hss : Recaman.OneSSMultiplicity.ssCount (past e u0 11) = 2) :
    phase p (u0 - (oldestOffset (past e u0 11) : Int)) ∉ neighborhood e p B lag := by
  have hbound : ∀ b ∈ B, lag b ≤ 11 := by
    intro b hb
    rcases hlag b hb with h | h | h <;> omega
  have hhall : ∀ A : List Nat, List.Sublist A B → A.length ≤ (neighborhood e p A lag).length := by
    intro A hA
    exact short_window_hall e p hp hper A lag (hBn.sublist hA)
      (fun u hu => hBp u (hA.subset hu)) (fun u hu => hBA u (hA.subset hu))
      (fun u hu => hbound u (hA.subset hu)) (fun u hu => hP u (hA.subset hu))
  obtain ⟨own, hF⟩ := tight_owner_family e p hp hper B B lag hBn hhall
    (List.Sublist.refl B) htight hBp hBA hlag hP hmin
  intro hcovered
  rw [Recaman.TwoSSAvoidTight.mem_neighborhood_iff,
    Recaman.TwoSSTightDisjoint.isCoveredBySubset_iff] at hcovered
  obtain ⟨_, b, hb, i, hi, he, hmod⟩ := hcovered
  let s : Int := u0 - (oldestOffset (past e u0 11) : Int)
  let t : Int := s + 1 + (i : Int)
  have hmod' : ((b : Int) - 1 - (i : Int)) % (p : Int) = s % (p : Int) := by
    change ((b : Int) - 1 - (i : Int)) % (p : Int) = (phase p s : Int) at hmod
    rw [Recaman.SharpPeriodicSupply.phase_cast p hp] at hmod
    exact hmod
  have htmod : t % (p : Int) = (b : Int) % (p : Int) :=
    emod_congr p _ _ _ _ hmod'.symm (by dsimp [t]; omega)
  have htphase : phase p t = b := phase_eq_of_emod p hp t b (hBp b hb) htmod
  have ht : phase p t ∈ B := by simpa only [htphase] using hb
  have hts : t - 1 - (i : Int) = s := by dsimp [t]; omega
  have het : e (t - 1 - (i : Int)) = false := by
    rw [e_of_emod_eq e p hper _ ((b : Int) - 1 - (i : Int))
      (emod_congr p _ _ _ _ htmod (by omega))]
    exact he
  have hi' : i < lag (phase p t) := by simpa only [htphase] using hi
  exact owner_member_avoids_ss2_window e _ own _ hF u0 hPdon hss t ht i hi' het hts

end Recaman.ShortTightDonorAvoidance
