import Recaman.PeriodicOwnerFamilyLagEleven
import Recaman.PairedSubtractionCoverage
import Recaman.TrueOldestGateT6

/-!
# Short tight subsets avoid a lag-11 SS=2 donor's true oldest subtraction

The new local input is that a w1 member of an owner family has next sign A.
Hall is a hypothesis in the periodic consequence, and all member windows of the tight
subset have minimal lag 3, 7 or 11. There is no upper bound on the period.
This does not establish Hall, all-lag capacity, general Gate T6, or an orbit claim.
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

/-- The newest S of w1 needs a different owner, forcing A at the next clock. -/
theorem w1_next_addition (e : Int → Bool) (mem : Int → Prop) (own : Int → Int)
    (lag : Int → Nat) (hF : OwnerFamily e mem own lag) (t : Int) (ht : mem t)
    (hw : past e t (lag t) = w1) : e (t + 1) = true := by
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
    have hx : v - 1 = t + 1 := by omega
    have h := past_getD e v 3 0 (by decide) true
    have ha3 : past e v 3 = aas := by simpa only [hvlen] using ha
    rw [ha3] at h
    simpa [aas, hx] using h.symm
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

end Recaman.ShortTightDonorAvoidance
