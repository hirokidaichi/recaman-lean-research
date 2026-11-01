import Recaman.ShortTightDonorAvoidance

/-!
# SS2 terminal patterns and a shorter P2 prefix

These word lemmas have no length cutoff. The proof uses suffix mass and moment
bounds, not the finite donor tables. A separate periodic consequence is needed
before claiming avoidance of an arbitrary-length donor.
-/

namespace Recaman.SS2OldestPattern

open Recaman.LeadingRunSupply
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.LowSSEndpoint

/-- Every suffix ending A has mass at least minus its SS count. Summing
those suffix masses gives a strict moment bound at any fixed SS budget. -/
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

/-- With at most two SS, every suffix of a word ending AA has mass at least -1,
except the last suffix which is A. This forces a positive moment-plus-length. -/
theorem moment_ending_AA_ss2 (w : List Bool)
    (hss : ssCount (w ++ [true, true]) ≤ 2) :
    5 ≤ moment (w ++ [true, true]) + (w ++ [true, true]).length := by
  induction w with
  | nil => decide
  | cons b w ih =>
    have hs := ssCount_tail_le b (w ++ [true, true])
    have hi := ih (by simpa using Nat.le_trans hs hss)
    have hsplit : (b :: w) ++ [true, true] = ((b :: w) ++ [true]) ++ [true] := by simp
    have hm := mass_ending_A (b :: w)
    have hss' : ssCount ((b :: w) ++ [true]) ≤ 2 := by
      simpa only [hsplit, ssCount_post_A] using hss
    have hl : -1 ≤ mass ((b :: w) ++ [true, true]) := by
      rw [hsplit, mass_append]
      simp only [mass_cons, mass_nil, Recaman.ShortPeriodicSupply.sign, ↓reduceIte]
      omega
    simp only [List.cons_append, moment, List.length_cons, Int.natCast_add,
      Int.cast_ofNat_Int] at hi ⊢
    rw [List.cons_append, mass_cons] at hl
    omega

/-- An A-ended mass-zero word at moment at most minus its length and with
at most two SS already contains a strict S-ended P2 prefix. -/
theorem ss2_intervening_prefix (w : List Bool)
    (hm : mass (w ++ [true]) = 0)
    (hM : moment (w ++ [true]) + (w ++ [true]).length ≤ 0)
    (hss : ssCount (w ++ [true]) ≤ 2) :
    ∃ u v : List Bool, w ++ [true] = (u ++ [false]) ++ v ∧
      P2 (u ++ [false]) ∧ v ≠ [] := by
  rcases List.eq_nil_or_concat w with hw | ⟨x, b, hw⟩
  · simp [hw, mass_cons, mass_nil, Recaman.ShortPeriodicSupply.sign] at hm
  · simp only [List.concat_eq_append] at hw
    cases b with
    | true =>
      have hword : w ++ [true] = x ++ [true, true] := by simp [hw, List.append_assoc]
      have hc := moment_ending_AA_ss2 x (by simpa only [hword] using hss)
      rw [hword] at hM
      omega
    | false =>
      have hword : w ++ [true] = x ++ [false, true] := by simp [hw, List.append_assoc]
      have hmx : mass x = 0 := by
        simpa [hword, mass_append, mass_cons, mass_nil, Recaman.ShortPeriodicSupply.sign] using hm
      have hMx : moment x + x.length ≤ 0 := by
        simp [hword, moment_append, moment, mass_cons, mass_nil,
          Recaman.ShortPeriodicSupply.sign] at hM
        omega
      have hsx : ssCount x ≤ 2 := by
        have h := ssCount_append_left_le x [false, true]
        rw [← hword] at h
        omega
      rcases List.eq_nil_or_concat x with hx | ⟨y, c, hx⟩
      · simp [hx, hword, moment, mass_cons, mass_nil, Recaman.ShortPeriodicSupply.sign] at hM
      · simp only [List.concat_eq_append] at hx
        cases c with
        | true =>
          obtain ⟨u, v, heq, hP, _⟩ := ss2_intervening_prefix y
            (hx ▸ hmx) (hx ▸ hMx) (hx ▸ hsx)
          refine ⟨u, v ++ [false, true], ?_, hP, by simp⟩
          simp only [hword, hx, heq, List.append_assoc]
        | false =>
          have hword' : w ++ [true] = y ++ [false, false, true] := by
            simp [hword, hx, List.append_assoc]
          have hmy : mass y = 1 := by
            simp [hx, mass_append, mass_cons, mass_nil, Recaman.ShortPeriodicSupply.sign] at hmx
            omega
          have hMy : moment y ≤ 0 := by
            simp [hword', moment_append, moment, mass_cons, mass_nil,
              Recaman.ShortPeriodicSupply.sign] at hM
            omega
          have hsy : ssCount y ≤ 1 := by
            have h := ssCount_post_SS y
            have hle := ssCount_append_left_le y [false]
            have hs' : ssCount (y ++ [false, false]) ≤ 2 := by
              have heq : w ++ [true] = (y ++ [false, false]) ++ [true] := by
                simp [hword', List.append_assoc]
              simpa only [heq, ssCount_post_A] using hss
            omega
          have hfound : ∃ u v : List Bool, y = (u ++ [false]) ++ v ∧ P2 (u ++ [false]) := by
            rcases List.eq_nil_or_concat y with hy | ⟨z, a, hy⟩
            · simp [hy] at hmy
            · simp only [List.concat_eq_append] at hy
              cases a with
              | true =>
                simpa only [← hy] using lowSS_A_nonpositive_prefix z
                  (hy ▸ hmy) (hy ▸ hMy) (hy ▸ hsy)
              | false =>
                have h1 := ssCount_post_SS z
                have h2 := ssCount_post_SS (z ++ [false])
                have hs' : ssCount ((z ++ [false]) ++ [false, false]) ≤ 2 := by
                  have heq : w ++ [true] = ((z ++ [false]) ++ [false, false]) ++ [true] := by
                    simp [hword', hy, List.append_assoc]
                  simpa only [heq, ssCount_post_A] using hss
                have hzero : ssCount y = 0 := by
                  rw [hy]
                  simp only [List.append_assoc, List.cons_append, List.nil_append] at h2 hs'
                  omega
                exact zero_SS_nonpositive_prefix y hmy hMy hzero
          obtain ⟨u, v, heq, hP⟩ := hfound
          refine ⟨u, v ++ [false, false, true], ?_, hP, by simp⟩
          simp only [hword', heq, List.append_assoc]
termination_by w.length
decreasing_by all_goals simp [hw, hx]

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

open Recaman.LagSevenDonorCoverage (oldestOffset past_getD)
open Recaman.TwoSSLeadingSibling (past_length)

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

end Recaman.SS2OldestPattern
