import Recaman.PeriodicOwnerFamilyLagEleven
import Recaman.PairedSubtractionCoverage
import Recaman.ShortReservoirCapacity
import Recaman.TerminalASSBound

/-! Arbitrary-length minimal SS=2 donors avoid the neighborhood of a tight
subset of minimal windows of lengths 3,7,11. The short restriction is on
members only. No ambient Hall, drift, NoSAAS, OS or distance bound is assumed.
Selected short-family and decomposition proofs derive from the separately
hashed September drafts; this module supplies the all-length stream theorem. -/
namespace Recaman.SS2ShortTight
open Recaman.LeadingRunSupply
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.LowSSEndpoint
open Recaman.OwnerFamilyLagEleven
open Recaman.LagSevenPrefixRigidity (w1 w2)
open Recaman.LagSevenDonorCoverage (past_getD oldestOffset)
open Recaman.TwoSSLeadingSibling (past_length)
open Recaman.PairedSubtractionCoverage
open Recaman.PeriodicOwnerFamilyLagEleven
open Recaman.SharpPeriodicSupply (phase)
open Recaman.TwoSSTightDisjoint (neighborhood)

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


theorem moment_ending_A_budget (w : List Bool) (q : Nat)
    (hss : ssCount (w ++ [true]) ≤ q) :
    (q : Int) + 1 ≤ moment (w ++ [true]) + q * (w ++ [true]).length := by
  induction w with
  | nil => simp [moment, mass, Recaman.ShortPeriodicSupply.sign]; omega
  | cons b w ih =>
    have hs := ssCount_tail_le b (w ++ [true])
    have hi := ih (by simpa using Nat.le_trans hs hss)
    have hm := mass_ending_A (b :: w)
    have hl : -(q : Int) ≤ mass ((b :: w) ++ [true]) := by omega
    simp only [List.cons_append, moment, List.length_cons, Int.natCast_add,
      Int.cast_ofNat_Int] at hi ⊢
    rw [List.cons_append, mass_cons] at hl
    grind


/-- An A-ended suffix cannot have mass below minus the total SS budget. -/
theorem suffix_mass_ending_A (w : List Bool) (q : Nat)
    (hss : ssCount (w ++ [true]) ≤ q) :
    ∀ j, -(q : Int) ≤ mass ((w ++ [true]).drop j) := by
  induction w with
  | nil =>
    intro j
    cases j <;> simp [mass, Recaman.ShortPeriodicSupply.sign] <;> omega
  | cons b w ih =>
    have hs := ssCount_tail_le b (w ++ [true])
    have hi := ih (by simpa using Nat.le_trans hs hss)
    intro j
    cases j with
    | zero =>
      have hm := mass_ending_A (b :: w)
      simp only [List.drop_zero]
      omega
    | succ j => simpa only [List.cons_append, List.drop_succ_cons] using hi j

/-- The ceiling and positivity used here are derived, not extra premises. -/
theorem ss2_intervening_prefix (w : List Bool)
    (hm : mass (w ++ [true]) = 0)
    (hM : moment (w ++ [true]) + (w ++ [true]).length ≤ 0)
    (hss : ssCount (w ++ [true]) ≤ 2) :
    ∃ u v : List Bool, w ++ [true] = (u ++ [false]) ++ v ∧
      P2 (u ++ [false]) ∧ v ≠ [] := by
  classical
  have hceil : ∀ j, j ≤ (w ++ [true]).length → mass ((w ++ [true]).take j) ≤ 2 := by
    intro j _
    have hs := suffix_mass_ending_A w 2 hss j
    have he := mass_append ((w ++ [true]).take j) ((w ++ [true]).drop j)
    rw [List.take_append_drop, hm] at he
    omega
  have hex : ∃ j, 0 < j ∧ j ≤ (w ++ [true]).length ∧ P2 ((w ++ [true]).take j) := by
    apply Decidable.byContradiction
    intro hn
    have hno : ∀ j, 0 < j → j ≤ (w ++ [true]).length → ¬ P2 ((w ++ [true]).take j) := by
      intro j hj hjlen hp
      exact hn ⟨j, hj, hjlen, hp⟩
    have hpos := Recaman.FirstP2EndingS.defect_pos_before_p2 (w ++ [true])
      (by simp) hceil hno
    simp only [Recaman.FirstP2EndingS.defect, hm] at hpos
    omega
  obtain ⟨j, _, _, hp, _, u, hu⟩ :=
    Recaman.FirstP2EndingS.first_p2_prefix_ends_S (w ++ [true]) hceil hex
  refine ⟨u, (w ++ [true]).drop j, ?_, ?_, ?_⟩
  · rw [← hu, List.take_append_drop]
  · rwa [← hu]
  · intro hn
    have he : w ++ [true] = u ++ [false] := by
      have hh := List.take_append_drop j (w ++ [true])
      rw [hu, hn, List.append_nil] at hh
      exact hh.symm
    have hr := congrArg List.reverse he
    simp at hr

theorem moment_replicate_A_nonneg (n : Nat) : 0 ≤ moment (List.replicate n true) := by
  have h := twice_moment_replicate_A n
  have hp : 0 ≤ (n : Int) * ((n : Int) + 1) := Int.mul_nonneg (by omega) (by omega)
  omega

/-- Exact mass and moment equations when an earlier P2 suffix is followed only by A. -/
theorem p2_append_A_tail_data (x v : List Bool) (n : Nat)
    (hx : P2 ((x ++ v) ++ List.replicate n true)) (hv : P2 v) :
    mass x = -(n : Int) ∧
      moment x + x.length + ((x.length : Int) + v.length) * n +
        moment (List.replicate n true) = 0 := by
  have hm := hx.1
  have hM := hx.2
  rw [mass_append, mass_append, hv.1, mass_replicate_A] at hm
  rw [moment_append, moment_append, hv.1, hv.2, mass_replicate_A,
    List.length_append] at hM
  simp only [Int.natCast_add] at hM
  constructor <;> omega

/-- If an SS<=2 P2 word has an AAS suffix preceded by its current A, then it
has a strict P2 prefix; arbitrary trailing A signs after that oldest S are allowed. -/
theorem ss2_aas_oldest_has_prefix (x : List Bool) (n : Nat)
    (hP : P2 (((x ++ [true]) ++ Recaman.OwnerFamilyLagEleven.aas) ++ List.replicate n true))
    (hss : ssCount (((x ++ [true]) ++ Recaman.OwnerFamilyLagEleven.aas) ++
      List.replicate n true) ≤ 2) :
    ∃ u v : List Bool,
      ((x ++ [true]) ++ Recaman.OwnerFamilyLagEleven.aas) ++ List.replicate n true =
        (u ++ [false]) ++ v ∧ P2 (u ++ [false]) ∧ v ≠ [] := by
  have ha : P2 Recaman.OwnerFamilyLagEleven.aas := by decide
  have hdata := p2_append_A_tail_data (x ++ [true]) Recaman.OwnerFamilyLagEleven.aas n hP ha
  have hsx : ssCount (x ++ [true]) ≤ 2 := by
    have hs := ssCount_append_left_le (x ++ [true])
      (Recaman.OwnerFamilyLagEleven.aas ++ List.replicate n true)
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
    obtain ⟨u, v, heq, hu, _⟩ := ss2_intervening_prefix x hm hM hsx
    refine ⟨u, v ++ Recaman.OwnerFamilyLagEleven.aas, ?_, hu, ?_⟩
    · simp only [List.replicate_zero, List.append_nil, heq, List.append_assoc]
    · simp [Recaman.OwnerFamilyLagEleven.aas]
  | succ n =>
    have hbound := moment_ending_A_budget x 2 hsx
    have hM := hdata.2
    have hn := moment_replicate_A_nonneg (n + 1)
    have hprod : 0 ≤ (((x ++ [true]).length : Int) + 3) * (n : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    have heq : (((x ++ [true]).length : Int) + 3) * ((n + 1 : Nat) : Int) =
        (((x ++ [true]).length : Int) + 3) * (n : Int) + (x ++ [true]).length + 3 := by
      push_cast
      grind
    change moment (x ++ [true]) + (x ++ [true]).length +
      (((x ++ [true]).length : Int) + 3) * ((n + 1 : Nat) : Int) +
      moment (List.replicate (n + 1) true) = 0 at hM
    rw [heq] at hM
    omega

/-- An SS<=2 P2 word cannot have an earlier current-A w1 window ending at its
oldest S, even if an arbitrary run of A follows that S in the backward word. -/
theorem ss2_no_w1_oldest (x : List Bool) (n : Nat)
    (hP : P2 (((x ++ [true]) ++ Recaman.LagSevenPrefixRigidity.w1) ++ List.replicate n true))
    (hss : ssCount (((x ++ [true]) ++ Recaman.LagSevenPrefixRigidity.w1) ++
      List.replicate n true) ≤ 2) : False := by
  have hw : P2 Recaman.LagSevenPrefixRigidity.w1 := by decide
  have hdata := p2_append_A_tail_data (x ++ [true]) Recaman.LagSevenPrefixRigidity.w1 n hP hw
  have hsx : ssCount (x ++ [true]) ≤ 1 := by
    have h1 := Recaman.EndpointRepetitionBudget.ssCount_append_superadditive
      (x ++ [true]) Recaman.LagSevenPrefixRigidity.w1
    have h2 := ssCount_append_left_le ((x ++ [true]) ++ Recaman.LagSevenPrefixRigidity.w1)
      (List.replicate n true)
    have hwss : ssCount Recaman.LagSevenPrefixRigidity.w1 = 1 := by decide
    rw [hwss] at h1
    omega
  have hbound := moment_ending_A x hsx
  have hn := moment_replicate_A_nonneg n
  have hprod : 0 ≤ (((x ++ [true]).length : Int) + Recaman.LagSevenPrefixRigidity.w1.length) * n :=
    Int.mul_nonneg (by omega) (by omega)
  have hM := hdata.2
  omega


theorem oldestOffset_le_length (w : List Bool) : oldestOffset w ≤ w.length := by
  induction w with
  | nil => decide
  | cons b w ih =>
    simp only [oldestOffset, List.length_cons]
    split
    · cases b <;> simp <;> omega
    · omega

/-- Everything strictly older than the actual oldest S is A, for every word. -/
theorem oldestOffset_split (w : List Bool) :
    w = w.take (oldestOffset w) ++ List.replicate (w.length - oldestOffset w) true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    by_cases h0 : oldestOffset w = 0
    · have hw : w = List.replicate w.length true := by simpa [h0] using ih
      cases b
      · simpa [oldestOffset, h0] using congrArg (List.cons false) hw
      · simpa [oldestOffset, h0, List.replicate_succ] using congrArg (List.cons true) hw
    · simpa [oldestOffset, h0, List.take_succ_cons] using congrArg (List.cons b) ih

theorem ssCount_append_replicate_A (w : List Bool) (n : Nat) :
    ssCount (w ++ List.replicate n true) = ssCount w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have heq : w ++ List.replicate (n + 1) true = (w ++ [true]) ++ List.replicate n true := by
      simp [List.replicate_succ, List.append_assoc]
    rw [heq, ih, ssCount_post_A]

theorem past_oldest_split (e : Int → Bool) (u : Int) (d : Nat) :
    past e u d = past e u (oldestOffset (past e u d)) ++
      List.replicate (d - oldestOffset (past e u d)) true := by
  have hb := oldestOffset_le_length (past e u d)
  rw [past_length] at hb
  have h := oldestOffset_split (past e u d)
  rwa [past_length, take_past e u d _ hb] at h

/-- A low-SS window ending at a donor's true oldest S must begin earlier than
the donor clock; otherwise the entire donor is a suffix of that low-SS window. -/
theorem oldest_cover_clock_lt (e : Int → Bool) (u t : Int) (d l : Nat)
    (hss : ssCount (past e u d) = 2) (hlow : ssCount (past e t l) ≤ 1)
    (hend : t - (l : Int) = u - (oldestOffset (past e u d) : Int)) : t < u := by
  by_cases htu : t < u
  · exact htu
  · have hoff : oldestOffset (past e u d) ≤ l := by omega
    have heq : l - oldestOffset (past e u d) + oldestOffset (past e u d) = l := by omega
    have htime : t - ((l - oldestOffset (past e u d) : Nat) : Int) = u := by omega
    have hpast := past_append e t (l - oldestOffset (past e u d)) (oldestOffset (past e u d))
    rw [heq, htime] at hpast
    have hmon := Recaman.EndpointRepetitionBudget.ssCount_append_superadditive
      (past e t (l - oldestOffset (past e u d))) (past e u (oldestOffset (past e u d)))
    rw [← hpast] at hmon
    have hsplit := past_oldest_split e u d
    rw [hsplit, ssCount_append_replicate_A] at hss
    omega

/-- The actual donor word splits around an earlier current-A window ending at
its true oldest S; no arbitrary history or suffix is assumed. -/
theorem past_oldest_cover_decomposition (e : Int → Bool) (u t : Int) (d l : Nat)
    (htu : t < u) (htA : e t = true)
    (hend : t - (l : Int) = u - (oldestOffset (past e u d) : Int)) :
    ∃ x : List Bool, past e u d = ((x ++ [true]) ++ past e t l) ++
      List.replicate (d - oldestOffset (past e u d)) true := by
  let off := oldestOffset (past e u d)
  have hbound : l < off := by dsimp [off]; omega
  have hlen : off - l - 1 + 1 + l = off := by omega
  have htime : u - ((off - l - 1 : Nat) : Int) - 1 = t := by omega
  have hone : past e (u - ((off - l - 1 : Nat) : Int)) 1 = [true] := by
    simp [past, htime, htA]
  have hx : past e u off = (past e u (off - l - 1) ++ [true]) ++ past e t l := by
    calc
      past e u off = past e u (off - l - 1 + 1 + l) := congrArg (past e u) hlen.symm
      _ = _ := by
        rw [past_append, past_append]
        have htime' : u - ((off - l - 1 + 1 : Nat) : Int) = t := by omega
        rw [hone, htime']
  refine ⟨past e u (off - l - 1), ?_⟩
  exact (past_oldest_split e u d).trans
    (congrArg (fun w => w ++ List.replicate (d - off) true) hx)


/-- A current-A AAS window cannot end at this donor's true oldest S. -/
theorem oldest_not_aas_endpoint (e : Int → Bool) (u : Int) (d : Nat)
    (hP : P2 (past e u d)) (hss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j))
    (t : Int) (hA : e t = true) (hw : past e t 3 = aas)
    (hend : t - 3 = u - (oldestOffset (past e u d) : Int)) : False := by
  have hl : ssCount (past e t 3) ≤ 1 := by rw [hw]; decide
  have htu := oldest_cover_clock_lt e u t d 3 hss hl hend
  obtain ⟨x, hx⟩ := past_oldest_cover_decomposition e u t d 3 htu hA hend
  rw [hw] at hx
  obtain ⟨a, v, hv, hp, hne⟩ := ss2_aas_oldest_has_prefix x
    (d - oldestOffset (past e u d)) (hx ▸ hP) (by rw [← hx, hss]; omega)
  have he : past e u d = (a ++ [false]) ++ v := hx.trans hv
  have hlen := congrArg List.length he
  rw [past_length, List.length_append] at hlen
  have hvpos : 0 < v.length := List.length_pos_iff.mpr hne
  have hlt : (a ++ [false]).length < d := by omega
  have htake : (past e u d).take (a ++ [false]).length = a ++ [false] := by
    rw [he, List.take_left]
  apply hmin _ (by simp) hlt
  rwa [htake]

/-- The SS budget also excludes w1 ending at the donor's true oldest S. -/
theorem oldest_not_w1_endpoint (e : Int → Bool) (u : Int) (d : Nat)
    (hP : P2 (past e u d)) (hss : ssCount (past e u d) = 2)
    (t : Int) (hA : e t = true) (hw : past e t 7 = w1)
    (hend : t - 7 = u - (oldestOffset (past e u d) : Int)) : False := by
  have hl : ssCount (past e t 7) ≤ 1 := by rw [hw]; decide
  have htu := oldest_cover_clock_lt e u t d 7 hss hl hend
  obtain ⟨x, hx⟩ := past_oldest_cover_decomposition e u t d 7 htu hA hend
  rw [hw] at hx
  exact ss2_no_w1_oldest x (d - oldestOffset (past e u d))
    (hx ▸ hP) (by rw [← hx, hss]; omega)

/-- All offsets of every actual short-family member avoid the donor's oldest S.
The family supplies the future AAS used for w1's newest S. -/
theorem owner_member_avoids_oldest (e : Int → Bool) (mem : Int → Prop)
    (own : Int → Int) (lag : Int → Nat) (hF : OwnerFamily e mem own lag)
    (u : Int) (d : Nat) (hP : P2 (past e u d))
    (hss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j))
    (t : Int) (ht : mem t) (k : Nat) (hk : k ∈ sOffsets (past e t (lag t))) :
    t - (k : Int) ≠ u - (oldestOffset (past e u d) : Int) := by
  intro hend
  rcases member_window_aas_or_w1 e mem own lag hF t ht with ha | hw
  · have hlen : lag t = 3 := by
      have h := congrArg List.length ha
      simpa [past_length, aas] using h
    have hk3 : k = 3 := by
      rw [ha] at hk
      have ho : sOffsets aas = [3] := by decide
      simpa only [ho, List.mem_singleton] using hk
    exact oldest_not_aas_endpoint e u d hP hss hmin t (hF.addA t ht)
      (by simpa [hlen] using ha) (by simpa [hk3] using hend)
  · have hlen : lag t = 7 := by
      have h := congrArg List.length hw
      simpa [past_length, w1] using h
    have hw7 : past e t 7 = w1 := by simpa [hlen] using hw
    have ho : sOffsets w1 = [1, 6, 7] := by decide
    rw [hw, ho] at hk
    have hc : k = 1 ∨ k = 6 ∨ k = 7 := by simpa using hk
    rcases hc with hk1 | hk6 | hk7
    · obtain ⟨hmem, _, hwin, _⟩ := w1_future_aas_member e mem own lag hF t ht hw
      exact oldest_not_aas_endpoint e u d hP hss hmin (t + 2)
        (hF.addA _ hmem) hwin (by simp only [hk1, Int.natCast_one] at hend; omega)
    · have hbit : ∀ i : Nat, i < 7 → e (t - 1 - (i : Int)) = w1.getD i false := by
        intro i hi
        have h := past_getD e t 7 i hi false
        rw [hw7] at h
        exact h.symm
      have hA : e (t - 3) = true := by
        have h := hbit 2 (by decide)
        simpa [w1, show t - 1 - (2 : Int) = t - 3 by omega] using h
      have h3 : e (t - 1 - 3) = true := by simpa [w1] using hbit 3 (by decide)
      have h4 : e (t - 1 - 4) = true := by simpa [w1] using hbit 4 (by decide)
      have h5 : e (t - 1 - 5) = false := by simpa [w1] using hbit 5 (by decide)
      have hwin : past e (t - 3) 3 = aas := by
        change [e (t - 3 - 1), e (t - 3 - 2), e (t - 3 - 3)] = [true,true,false]
        rw [show t - 3 - 1 = t - 1 - (3 : Int) by omega,
          show t - 3 - 2 = t - 1 - (4 : Int) by omega,
          show t - 3 - 3 = t - 1 - (5 : Int) by omega,
          h3, h4, h5]
      exact oldest_not_aas_endpoint e u d hP hss hmin (t - 3) hA hwin
        (by simp only [hk6, Int.cast_ofNat_Int] at hend; omega)
    · exact oldest_not_w1_endpoint e u d hP hss t (hF.addA t ht) hw7
        (by simpa [hk7] using hend)

/-- Exact issue #81 theorem. The donor has arbitrary length; only B is short.
Hall is derived on B, not an ambient hypothesis. -/
theorem short_tight_avoids_donor (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat) (hBn : B.Nodup)
    (hBp : ∀ b ∈ B, b < p) (hBA : ∀ b ∈ B, e (b : Int) = true)
    (hBlag : ∀ b ∈ B, lag b = 3 ∨ lag b = 7 ∨ lag b = 11)
    (hBP : ∀ b ∈ B, P2 (past e (b : Int) (lag b)))
    (hBmin : ∀ b ∈ B, ∀ j, 0 < j → j < lag b → ¬ P2 ((past e (b : Int) (lag b)).take j))
    (htight : (neighborhood e p B lag).length = B.length)
    (u : Int) (d : Nat) (_hA : e u = true)
    (hP : P2 (past e u d)) (hss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j)) :
    phase p (u - (oldestOffset (past e u d) : Int)) ∉ neighborhood e p B lag := by
  have hbound : ∀ b ∈ B, lag b ≤ 11 := by
    intro b hb
    rcases hBlag b hb with h | h | h <;> omega
  have hhall : ∀ A : List Nat, A.Sublist B → A.length ≤ (neighborhood e p A lag).length := by
    intro A hAB
    exact short_window_hall e p hp hper A lag (hBn.sublist hAB)
      (fun b hb => hBp b (hAB.subset hb)) (fun b hb => hBA b (hAB.subset hb))
      (fun b hb => hbound b (hAB.subset hb)) (fun b hb => hBP b (hAB.subset hb))
  obtain ⟨own, hF⟩ := tight_owner_family e p hp hper B B lag hBn hhall
    (List.Sublist.refl B) htight hBp hBA hBlag hBP (fun b hb j hj hj0 => hBmin b hb j hj0 hj)
  intro hcovered
  rw [Recaman.TwoSSAvoidTight.mem_neighborhood_iff,
    Recaman.TwoSSTightDisjoint.isCoveredBySubset_iff] at hcovered
  obtain ⟨_, b, hb, i, hi, he, hmod⟩ := hcovered
  let s : Int := u - (oldestOffset (past e u d) : Int)
  let t : Int := s + 1 + (i : Int)
  have hmod' : ((b : Int) - 1 - (i : Int)) % (p : Int) = s % (p : Int) := by
    change ((b : Int) - 1 - (i : Int)) % (p : Int) = (phase p s : Int) at hmod
    rw [Recaman.SharpPeriodicSupply.phase_cast p hp] at hmod
    exact hmod
  have htmod : t % (p : Int) = (b : Int) % (p : Int) :=
    emod_congr p _ _ _ _ hmod'.symm (by dsimp [t]; omega)
  have htphase : phase p t = b := phase_eq_of_emod p hp t b (hBp b hb) htmod
  have ht : phase p t ∈ B := by simpa only [htphase] using hb
  have hk : i + 1 ∈ sOffsets (past e t (lag (phase p t))) := by
    rw [sOffsets_mem, past_length, htphase]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel, past_getD e t _ i hi]
    exact (e_of_emod_eq e p hper _ _ (emod_congr p _ _ _ _ htmod (by omega))).trans he
  exact owner_member_avoids_oldest e (fun t => phase p t ∈ B) own
    (fun t => lag (phase p t)) hF u d hP hss hmin t ht (i + 1) hk
    (by dsimp [t, s]; push_cast; omega)

end Recaman.SS2ShortTight
