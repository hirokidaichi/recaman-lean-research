import Recaman.OwnerFamilyLagEleven
import Recaman.HallMatching

/-!
# PeriodicOwnerFamilyLagEleven: lifting a periodic tight subset to an owner family

Convention: `e : Int → Bool` is a sign word (`true` = A, `false` = S) that is periodic with
period `p` (`e (x + p) = e x`); `past e u d = [e (u-1), ..., e (u-d)]` (newest first); `phase p t`
is the residue of the clock `t` modulo `p` as a natural number; `neighborhood e p A lag` is the
list of subtraction phases covered by the windows of the addition phases in `A`.

## What is proved

1. Periodicity transfer: two clocks with the same residue modulo `p` carry the same sign
   (`e_of_emod_eq`) and the same window of every length (`past_of_emod_eq`); a natural number
   `b < p` is its own phase (`phase_of_lt`); residue equality is stable under a common shift of
   both sides (`emod_congr`); a clock and its phase carry the same sign (`e_phase`).
2. `tight_no_lag_eleven`: in a periodic sign word with Hall's condition on `U`, a tight sublist
   `B ⊆ U` (|N(B)| = |B|) whose members are addition phases `b < p` with minimal P2 windows of
   lag 3, 7 or 11 has no member of lag 11. The owner map of `B` (`HallMatching.tight_owner_map`)
   is lifted to the integer line: the members of the lifted family are the clocks whose phase
   lies in `B`, the lag and the owned subtraction of a clock are read off its phase, and the
   "every subtraction of a member's window is owned" half of the bijection is transported by
   periodicity. The lifted family satisfies the hypotheses of
   `OwnerFamilyLagEleven.no_lag_eleven_member_of_minimal`, which excludes a lag-11 member.
3. `tight_lag_three_or_seven`: under the same hypotheses every member of `B` has lag 3 or 7.

## What is not proved

Nothing here concerns Gate T6, deletability, or E-070: Hall's condition is a hypothesis, never a
conclusion, and no deletability statement is established. Members with windows of lag ≥ 15 are
outside the hypotheses (`hB_lag` restricts the lags to 3, 7, 11), so the result is statement T
for lag-max 11 in the periodic setting: a tight subset all of whose members have minimal windows
of lag ≤ 11 has no lag-11 member. Nothing is said about a tight subset containing a member of
lag ≥ 15.
-/

namespace Recaman.PeriodicOwnerFamilyLagEleven

open Recaman.LeadingRunSupply (past P2)
open Recaman.TwoSSTightDisjoint (neighborhood isCoveredBySubset_iff)
open Recaman.TwoSSAvoidTight (mem_neighborhood_iff)
open Recaman.LagElevenPeriodic (e_shift mem_subPhases)
open Recaman.SharpPeriodicSupply (phase phase_cast phase_lt phase_eq_mod past_shift lift_equal_mod)
open Recaman.TwoSSLeadingSibling (past_length)
open Recaman.LagSevenDonorCoverage (past_getD)
open Recaman.OwnerFamilyLagEleven (sOffsets sOffsets_mem no_lag_eleven_member_of_minimal)
open Recaman.HallMatching (tight_owner_map)

/-- Residue equality modulo `p` is preserved by any common shift of both sides. -/
theorem emod_congr (p : Nat) (a b a' b' : Int) (h : a % p = b % p) (hab : a - b = a' - b') :
    a' % p = b' % p := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h ⊢
  rw [← hab]
  exact h

/-- In a periodic sign word, clocks with the same residue modulo `p` carry the same sign. -/
theorem e_of_emod_eq (e : Int → Bool) (p : Nat) (hper : ∀ x : Int, e (x + p) = e x)
    (t t' : Int) (h : t % p = t' % p) : e t = e t' := by
  obtain ⟨k, hk⟩ := lift_equal_mod p t t' h
  rw [hk, e_shift e p hper]

/-- In a periodic sign word, clocks with the same residue modulo `p` have the same window of
every length. -/
theorem past_of_emod_eq (e : Int → Bool) (p : Nat) (hper : ∀ x : Int, e (x + p) = e x)
    (t t' : Int) (h : t % p = t' % p) (d : Nat) : past e t d = past e t' d := by
  obtain ⟨k, hk⟩ := lift_equal_mod p t t' h
  rw [hk, past_shift e p hper]

/-- Residue equality modulo `p` gives phase equality. -/
theorem phase_congr (p : Nat) (x y : Int) (h : x % p = y % p) : phase p x = phase p y :=
  congrArg Int.toNat h

/-- A natural number below `p` is its own phase. -/
theorem phase_of_lt (p : Nat) (hp : 0 < p) (b : Nat) (hb : b < p) : phase p (b : Int) = b := by
  have hc := phase_cast p hp (b : Int)
  have hmod : (b : Int) % (p : Int) = (b : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  omega

/-- A clock whose residue is that of a natural number `b < p` has phase `b`. -/
theorem phase_eq_of_emod (p : Nat) (hp : 0 < p) (x : Int) (b : Nat) (hb : b < p)
    (h : x % p = (b : Int) % p) : phase p x = b := by
  rw [phase_congr p x (b : Int) h]
  exact phase_of_lt p hp b hb

/-- The sign at a clock equals the sign at its phase. -/
theorem e_phase (e : Int → Bool) (p : Nat) (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x)
    (x : Int) : e (phase p x : Int) = e x := by
  apply e_of_emod_eq e p hper
  rw [phase_cast p hp, Int.emod_emod]

/-- Lift a periodic tight subset to an actual owner family on the integer line. -/
theorem tight_owner_family (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    : ∃ own : Int → Int, Recaman.OwnerFamilyLagEleven.OwnerFamily e
      (fun t => phase p t ∈ B) own (fun t => lag (phase p t)) := by
  obtain ⟨own, hown_mem, _, hown_onto⟩ := tight_owner_map e p U B lag hU hhall hB htight
  -- Each member owns a subtraction of its own window: record the offset of that subtraction.
  have hspec : ∀ b, ∃ i : Nat, b ∈ B → (i < lag b ∧ e ((b : Int) - 1 - (i : Int)) = false ∧
      ((b : Int) - 1 - (i : Int)) % (p : Int) = (own b : Int)) := by
    intro b
    by_cases hb : b ∈ B
    · have h := hown_mem b hb
      rw [mem_neighborhood_iff, isCoveredBySubset_iff] at h
      obtain ⟨_, u, hu, i, hi, he, hmod⟩ := h
      rw [List.mem_singleton] at hu
      subst hu
      exact ⟨i, fun _ => ⟨hi, he, hmod⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  obtain ⟨idx, hidx⟩ : ∃ idx : Nat → Nat, ∀ b, b ∈ B → (idx b < lag b ∧
      e ((b : Int) - 1 - (idx b : Int)) = false ∧
      ((b : Int) - 1 - (idx b : Int)) % (p : Int) = (own b : Int)) :=
    ⟨fun b => Classical.choose (hspec b), fun b hb => Classical.choose_spec (hspec b) hb⟩
  -- A clock whose phase is a member has the residue, the window and the sign of that member.
  have hres : ∀ t : Int, phase p t ∈ B → t % p = ((phase p t : Nat) : Int) % p := by
    intro t ht
    exact phase_eq_mod p hp t _ (phase_of_lt p hp _ (hBp _ ht)).symm
  have hwin : ∀ t : Int, phase p t ∈ B → ∀ d, past e t d = past e ((phase p t : Nat) : Int) d :=
    fun t ht d => past_of_emod_eq e p hper t _ (hres t ht) d
  have hsign : ∀ t : Int, phase p t ∈ B → e t = e ((phase p t : Nat) : Int) :=
    fun t ht => e_of_emod_eq e p hper t _ (hres t ht)
  -- The lifted family: members are the clocks whose phase lies in `B`; lag and owned
  -- subtraction are read off the phase.
  have hlag' : ∀ t : Int, phase p t ∈ B →
      lag (phase p t) = 3 ∨ lag (phase p t) = 7 ∨ lag (phase p t) = 11 :=
    fun t ht => hB_lag _ ht
  have hP' : ∀ t : Int, phase p t ∈ B → P2 (past e t (lag (phase p t))) := by
    intro t ht
    rw [hwin t ht]
    exact hB_P2 _ ht
  have hmin' : ∀ t : Int, phase p t ∈ B → ∀ d, d < lag (phase p t) → 0 < d →
      ¬ P2 ((past e t (lag (phase p t))).take d) := by
    intro t ht d hd hd0
    rw [hwin t ht]
    exact hB_min _ ht d hd hd0
  have haddA' : ∀ t : Int, phase p t ∈ B → e t = true := by
    intro t ht
    rw [hsign t ht]
    exact hB_A _ ht
  -- Every member owns a subtraction of its own window.
  have hown' : ∀ t : Int, phase p t ∈ B → ∃ k ∈ sOffsets (past e t (lag (phase p t))),
      t - 1 - (idx (phase p t) : Int) = t - (k : Int) := by
    intro t ht
    obtain ⟨hi, he, _⟩ := hidx (phase p t) ht
    refine ⟨idx (phase p t) + 1, ?_, by omega⟩
    rw [sOffsets_mem, past_length]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel, past_getD e t _ _ hi]
    refine (e_of_emod_eq e p hper _
      (((phase p t : Nat) : Int) - 1 - (idx (phase p t) : Int)) ?_).trans he
    exact emod_congr p t _ _ _ (hres t ht) (by omega)
  -- Every subtraction of a member's window is owned by some member.
  have honto' : ∀ t : Int, phase p t ∈ B → ∀ k ∈ sOffsets (past e t (lag (phase p t))),
      ∃ t' : Int, phase p t' ∈ B ∧ t' - 1 - (idx (phase p t') : Int) = t - (k : Int) := by
    intro t ht k hk
    rw [sOffsets_mem, past_length] at hk
    obtain ⟨hk1, hk2, hkS⟩ := hk
    rw [past_getD e t _ (k - 1) (by omega)] at hkS
    have hS : e (t - (k : Int)) = false := by
      have heq : t - 1 - ((k - 1 : Nat) : Int) = t - (k : Int) := by omega
      rw [heq] at hkS
      exact hkS
    -- The subtraction phase of `t - k` lies in `N(B)`: it is an S phase covered by the window
    -- of the member `phase p t`.
    have hs : phase p (t - (k : Int)) ∈ neighborhood e p B lag := by
      rw [mem_neighborhood_iff]
      constructor
      · rw [mem_subPhases]
        refine ⟨phase_lt p hp _, ?_⟩
        rw [Int.zero_add, e_phase e p hp hper]
        exact hS
      · rw [isCoveredBySubset_iff]
        refine ⟨phase p t, ht, k - 1, by omega, ?_, ?_⟩
        · refine (e_of_emod_eq e p hper _ (t - (k : Int)) ?_).trans hS
          exact emod_congr p _ _ _ _ (hres t ht).symm (by omega)
        · rw [phase_cast p hp (t - (k : Int))]
          exact emod_congr p _ _ _ _ (hres t ht).symm (by omega)
    obtain ⟨b', hb', hownb'⟩ := hown_onto _ hs
    obtain ⟨_, _, hmod'⟩ := hidx b' hb'
    rw [hownb', phase_cast p hp (t - (k : Int))] at hmod'
    -- The owner `b'` of that phase, shifted so that its owned subtraction sits at `t - k`.
    have hph : phase p (t - (k : Int) + 1 + (idx b' : Int)) = b' :=
      phase_eq_of_emod p hp _ b' (hBp b' hb')
        (emod_congr p _ _ _ _ hmod'.symm (by omega))
    refine ⟨t - (k : Int) + 1 + (idx b' : Int), ?_, ?_⟩
    · rw [hph]
      exact hb'
    · rw [hph]
      omega
  exact ⟨_, Recaman.OwnerFamilyLagEleven.ownerFamily_of_minimal e _ _ _
    hlag' hP' hmin' haddA' hown' honto'⟩

/-- **No lag-11 member in a tight subset of short minimal windows.** In a periodic sign word
(`e (x + p) = e x`) with Hall's condition on `U`, a tight sublist `B ⊆ U` (|N(B)| = |B|) whose
members are addition phases `b < p` with minimal P2 windows of lag 3, 7 or 11 has no member of
lag 11. -/
theorem tight_no_lag_eleven (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (b0 : Nat) (hb0 : b0 ∈ B) (hlag11 : lag b0 = 11) : False := by
  obtain ⟨own, hF⟩ := tight_owner_family e p hp hper U B lag hU hhall hB htight
    hBp hB_A hB_lag hB_P2 hB_min
  have hph := phase_of_lt p hp b0 (hBp b0 hb0)
  apply Recaman.OwnerFamilyLagEleven.no_lag_eleven_member e _ own _ hF (b0 : Int)
  · simpa only [hph] using hb0
  · simpa only [hph] using hlag11

/-- **Every member of a tight subset of short minimal windows has lag 3 or 7.** Under the
hypotheses of `tight_no_lag_eleven`, the lag-11 alternative of `hB_lag` is excluded for every
member of `B`. -/
theorem tight_lag_three_or_seven (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (b : Nat) (hb : b ∈ B) : lag b = 3 ∨ lag b = 7 := by
  rcases hB_lag b hb with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (tight_no_lag_eleven e p hp hper U B lag hU hhall hB htight hBp hB_A hB_lag hB_P2
      hB_min b hb h).elim

end Recaman.PeriodicOwnerFamilyLagEleven
