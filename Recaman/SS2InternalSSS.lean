import Recaman.SS2LowSSTight
import Recaman.OnePerRun

/-!
# An internal SSS cannot be a low-SS P2 endpoint

This is the first, narrower Lean obligation in the E-370 paper proof. The
stream and all windows are actual integer-clock data. An internal SSS
also has a different phase from any earlier S in an SS≤2 window, giving
two excluded phases for a minimal SS2 donor. Neither NoSAAS, positive
period mass, nor a lag cutoff is assumed. No claim about the q = oldest-S
case or the full collision-pair inequality is made here.
-/

namespace Recaman.SS2InternalSSS

open LeadingRunSupply
open OneSSMultiplicity (ssCount)
open SharpPeriodicSupply (phase)
open LowSSPeriodicSupply (endpointPhase)

/-- Two overlapping SS edges are present in any word ending in SSS. -/
theorem ssCount_append_SSS (w : List Bool) :
    2 ≤ ssCount (w ++ [false, false, false]) := by
  have htwo : ssCount [false, false, false] = 2 := by decide
  rw [OnePerRun.ssCount_append, htwo]
  omega

/-- A P2 window with at most one SS edge cannot have its oldest
endpoint at the first clock of an SSS run. The P2 hypothesis supplies the
minimum lag three; the two SS edges then occur inside the actual window. -/
theorem internal_sss_ne_lowSS_endpoint
    (e : Int → Bool) (q t : Int) (l : Nat)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false)
    (htP : P2 (past e t l))
    (htss : ssCount (past e t l) ≤ 1)
    (hend : t - (l : Int) = q) : False := by
  have hlag : 3 ≤ l := by
    have h := p2_length_ge_three (past e t l) htP
    simpa [past] using h
  have hthree : past e (q + 3) 3 = [false, false, false] := by
    rw [TwoSSLeadingSibling.past_three_eq]
    rw [show q + 3 - 1 = q + 2 by omega,
      show q + 3 - 2 = q + 1 by omega,
      show q + 3 - 3 = q by omega,
      hq2, hq1, hq0]
  have hsplit : past e t l =
      past e t (l - 3) ++ [false, false, false] := by
    have heq : l = (l - 3) + 3 := by omega
    calc
      past e t l = past e t ((l - 3) + 3) := congrArg (past e t) heq
      _ = past e t (l - 3) ++ past e (t - ((l - 3 : Nat) : Int)) 3 :=
        past_append e t (l - 3) 3
      _ = past e t (l - 3) ++ [false, false, false] := by
        rw [show t - ((l - 3 : Nat) : Int) = q + 3 by omega, hthree]
  rw [hsplit] at htss
  have htwo := ssCount_append_SSS (past e t (l - 3))
  omega

/-- Periodicity transports every candidate endpoint phase to the first
integer clock of an actual SSS run. This is an all-period, all-lag exclusion;
it does not assert that the SSS lies in a particular donor window. -/
theorem internal_sss_phase_ne_lowSS_endpoint
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (q : Int)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false)
    (t : Int) (l : Nat)
    (htP : P2 (past e t l))
    (htss : ssCount (past e t l) ≤ 1) :
    endpointPhase p t l ≠ phase p q := by
  intro heq
  have hmod : (t - (l : Int)) % p = q % p :=
    SharpPeriodicSupply.phase_eq_mod p hp (t - l) q
      (by simpa [endpointPhase] using heq)
  obtain ⟨k, hk⟩ :=
    SharpPeriodicSupply.lift_equal_mod p q (t - l) hmod.symm
  have hP' : P2 (past e (t + k * p) l) := by
    rw [SharpPeriodicSupply.past_shift e p hper]
    exact htP
  have hss' : ssCount (past e (t + k * p) l) ≤ 1 := by
    rw [SharpPeriodicSupply.past_shift e p hper]
    exact htss
  exact internal_sss_ne_lowSS_endpoint e q (t + k * p) l
    hq0 hq1 hq2 hP' hss' (by omega)

/-- A concrete adjacent pair contributes at least one SS edge. -/
theorem ssCount_pos_of_pair (w : List Bool) (i : Nat)
    (hi : i + 1 < w.length)
    (h0 : w.getD i true = false) (h1 : w.getD (i + 1) true = false) :
    0 < ssCount w := by
  induction w generalizing i with
  | nil => simp at hi
  | cons b w ih =>
    cases i with
    | zero =>
      cases w with
      | nil => simp at hi
      | cons c v =>
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
        subst b; subst c
        simp [ssCount]
        omega
    | succ i =>
      have ht := ih i (by simpa using hi)
        (by simpa only [List.getD_cons_succ] using h0)
        (by simpa only [Nat.succ_add, List.getD_cons_succ] using h1)
      have hm := LowSSEndpoint.ssCount_tail_le b w
      omega

/-- In a word with at most two SS edges, an SSS cannot coexist with
an SS edge starting strictly beyond its second edge (newest first). -/
theorem ss2_triple_no_later_pair (w : List Bool) (i j : Nat)
    (hss : ssCount w ≤ 2) (hi : i + 2 < w.length)
    (hij : i + 2 ≤ j) (hj : j + 1 < w.length)
    (h0 : w.getD i true = false) (h1 : w.getD (i + 1) true = false)
    (h2 : w.getD (i + 2) true = false)
    (hj0 : w.getD j true = false) (hj1 : w.getD (j + 1) true = false) :
    False := by
  induction i generalizing w j with
  | zero =>
    match w with
    | a :: b :: c :: rest =>
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
      subst a; subst b; subst c
      have hbudget : ssCount (false :: rest) = 0 := by
        have he : ssCount (false :: false :: false :: rest) =
            2 + ssCount (false :: rest) := by simp [ssCount]; omega
        omega
      have hpos := ssCount_pos_of_pair (false :: rest) (j - 2)
        (by simp only [List.length_cons] at hj ⊢; omega)
        (by
          rw [show j = Nat.succ (Nat.succ (j - 2)) by omega] at hj0
          simpa only [List.getD_cons_succ] using hj0)
        (by
          rw [show j + 1 = Nat.succ (Nat.succ (j - 2 + 1)) by omega] at hj1
          simpa only [List.getD_cons_succ] using hj1)
      omega
    | [] => simp at hi
    | [_] => simp at hi
    | [_, _] => simp at hi
  | succ i ih =>
    cases w with
    | nil => simp at hi
    | cons b w =>
      apply ih w (j - 1)
      · have hm := LowSSEndpoint.ssCount_tail_le b w; omega
      · simp only [List.length_cons] at hi; omega
      · omega
      · simp only [List.length_cons] at hj; omega
      · simpa only [List.getD_cons_succ] using h0
      · simpa only [Nat.succ_add, List.getD_cons_succ] using h1
      · simpa only [Nat.succ_add, List.getD_cons_succ] using h2
      · rw [show j = Nat.succ (j - 1) by omega] at hj0
        simpa only [List.getD_cons_succ] using hj0
      · rw [show j + 1 = Nat.succ (j - 1 + 1) by omega] at hj1
        simpa only [List.getD_cons_succ] using hj1

/-- An internal SSS has a different phase from every earlier S in the
same SS≤2 window. This is a local sign theorem, with no P2 premise. -/
theorem internal_sss_phase_ne_earlier_S
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (u : Int) (d : Nat) (s q : Int)
    (hss : ssCount (past e u d) ≤ 2)
    (hslo : u - (d : Int) ≤ s) (hsq : s < q) (hqu : q + 2 < u)
    (hs : e s = false) (hq0 : e q = false)
    (hq1 : e (q + 1) = false) (hq2 : e (q + 2) = false) :
    phase p s ≠ phase p q := by
  intro heq
  have hmod := SharpPeriodicSupply.phase_eq_mod p hp s q heq
  obtain ⟨k, hk⟩ := SharpPeriodicSupply.lift_equal_mod p q s hmod.symm
  have hs1 : e (s + 1) = false := by
    have hshift := LagElevenPeriodic.e_shift e p hper k (s + 1)
    rw [show s + 1 + k * p = q + 1 by omega, hq1] at hshift
    exact hshift.symm
  let i := (u - q - 3).toNat
  let j := (u - s - 2).toNat
  have hi : (i : Int) = u - q - 3 := Int.toNat_of_nonneg (by omega)
  have hj : (j : Int) = u - s - 2 := Int.toNat_of_nonneg (by omega)
  apply ss2_triple_no_later_pair (past e u d) i j hss
  · rw [TwoSSLeadingSibling.past_length]; omega
  · omega
  · rw [TwoSSLeadingSibling.past_length]; omega
  · rw [LagSevenDonorCoverage.past_getD e u d i (by omega) true]
    rwa [show u - 1 - (i : Int) = q + 2 by omega]
  · rw [LagSevenDonorCoverage.past_getD e u d (i + 1) (by omega) true]
    rwa [show u - 1 - ((i + 1 : Nat) : Int) = q + 1 by omega]
  · rw [LagSevenDonorCoverage.past_getD e u d (i + 2) (by omega) true]
    rwa [show u - 1 - ((i + 2 : Nat) : Int) = q by omega]
  · rw [LagSevenDonorCoverage.past_getD e u d j (by omega) true]
    rwa [show u - 1 - (j : Int) = s + 1 by omega]
  · rw [LagSevenDonorCoverage.past_getD e u d (j + 1) (by omega) true]
    rwa [show u - 1 - ((j + 1 : Nat) : Int) = s by omega]

/-- The oldest S and an internal SSS start in a minimal SS2 donor give
two distinct actual S phases excluded from every current-A low-SS P2
endpoint. Both clocks are in the original donor window. -/
theorem donor_internal_sss_two_excluded_phases
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (u : Int) (d : Nat)
    (hP : P2 (past e u d)) (hss : ssCount (past e u d) = 2)
    (hmin : ∀ j, 0 < j → j < d → ¬ P2 ((past e u d).take j))
    (q : Int) (hsq : u - LagSevenDonorCoverage.oldestOffset (past e u d) < q)
    (hqu : q + 2 < u)
    (hq0 : e q = false) (hq1 : e (q + 1) = false)
    (hq2 : e (q + 2) = false) :
    phase p (u - LagSevenDonorCoverage.oldestOffset (past e u d)) ≠ phase p q ∧
      ∀ (t : Int) (l : Nat), e t = true → P2 (past e t l) →
        ssCount (past e t l) ≤ 1 →
        endpointPhase p t l ≠ phase p (u - LagSevenDonorCoverage.oldestOffset (past e u d)) ∧
        endpointPhase p t l ≠ phase p q := by
  have hb := SS2ShortTight.oldestOffset_le_length (past e u d)
  rw [TwoSSLeadingSibling.past_length] at hb
  have hs := SS2LowSSTight.donor_oldest_is_S e u d (by omega)
  constructor
  · exact internal_sss_phase_ne_earlier_S e p hp hper u d _ q
      (by omega) (by omega) hsq hqu hs hq0 hq1 hq2
  · intro t l htA htP htss
    exact ⟨SS2LowSSTight.oldest_phase_ne_lowSS_endpoint e p hp hper
      u d hP hss hmin t l htA htP htss,
      internal_sss_phase_ne_lowSS_endpoint e p hp hper q hq0 hq1 hq2 t l htP htss⟩

/-! ## Concrete semantic controls

The antecedents are simultaneously inhabited: the periodic word AAASSS has a
first SSS clock at 3 while clock 2 has a P2/SS=0 AAS window ending at phase 5.
The endpoint exclusion is therefore not relying on the absence of P2 windows.
-/
private def sixStream (x : Int) : Bool := decide (x % 6 < 3)

example : sixStream 3 = false ∧ sixStream 4 = false ∧ sixStream 5 = false ∧
    sixStream 2 = true ∧ P2 (past sixStream 2 3) ∧
    ssCount (past sixStream 2 3) = 0 ∧
    endpointPhase 6 2 3 ≠ phase 6 3 := by decide

/-- Dropping the low-SS bound admits a P2 word with an oldest SSS triple. -/
example : P2 ([false, false, true, true, true, true, true, true,
    false, false, false] : List Bool) ∧
    ssCount ([false, false, true, true, true, true, true, true,
      false, false, false] : List Bool) = 3 := by decide

/-- A wrapping, negative-mass window inhabits the separation assumptions. -/
private def wrapStream (x : Int) : Bool := decide (x % 6 = 1 ∨ x % 6 = 5)

example : ssCount (past wrapStream 7 7) = 2 ∧ wrapStream 0 = false ∧
    wrapStream 2 = false ∧ wrapStream 3 = false ∧ wrapStream 4 = false ∧
    phase 6 0 ≠ phase 6 2 := by decide

end Recaman.SS2InternalSSS
