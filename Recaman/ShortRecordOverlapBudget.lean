import Recaman.DeficitRecordPredecessor

namespace Recaman.ShortRecordOverlapBudget

open Recaman.DeficitRecordPredecessor Recaman.DeficitRecordSourceCharge
open Recaman.ShortSourceTriples Recaman.AdditionRankSlack Recaman.SingleWindowEquality
open Recaman.BlockSuffixPositivity
open Classical

/-! The short SAA triples and the strict deficit record pairs on one original
sign string. If `L` counts internal short endpoints, `R` counts internal strict
records, `B` counts records preceded by a short endpoint and `C` counts records
followed by one inside the interval, then `3L + 2R` is bounded by the internal
additions plus `B + 2C`. This is the E643 overlap correction. -/

noncomputable def shortPairCovered (f : Nat → Bool) (n K p : Nat) : Prop :=
  (∃ e, shortEndpoint f n e ∧ e < n+K ∧ e-2 ≤ p ∧ p ≤ e) ∨
  (∃ t, localRecord f n t ∧ t < n+K ∧ t-1 ≤ p ∧ p ≤ t)

private theorem short_signs (f : Nat → Bool) (n t : Nat) (h : shortEndpoint f n t) :
    f (t-3) = false ∧ f (t-2) = true ∧ f (t-1) = true ∧ f t = true := h.2

private theorem short_sign_false (f : Nat → Bool) (n t : Nat) (h : shortEndpoint f n t) :
    f (t-3) = false := short_signs f n t h |>.1

private theorem short_signs2 (f : Nat → Bool) (n t : Nat) (h : shortEndpoint f n t) :
    f (t-2) = true ∧ f (t-1) = true ∧ f t = true := (short_signs f n t h).2

/-- Two distinct short endpoints are at least four positions apart. -/
theorem short_endpoints_gap (f : Nat → Bool) (n a b : Nat) (ha : shortEndpoint f n a)
    (hb : shortEndpoint f n b) (hab : a<b) : a+3 < b := by
  by_cases hgap : a+3 < b
  · exact hgap
  · have hb3 : f (b-3) = false := short_sign_false f n b hb
    have hcand : b-3 = a-2 ∨ b-3 = a-1 ∨ b-3 = a := by omega
    rcases hcand with hc|hc|hc
    · rw [hc,(short_signs2 f n a ha).1] at hb3
      cases hb3
    · rw [hc,(short_signs2 f n a ha).2.1] at hb3
      cases hb3
    · rw [hc,(short_signs2 f n a ha).2.2] at hb3
      cases hb3

/-- A strict record has original additions at its two charged positions. -/
theorem record_pair_additions (f : Nat → Bool) (n t : Nat) (hr : localRecord f n t) :
    n < t ∧ f (t-1) = true ∧ f t = true := by
  have hp := local_record_supplied_predecessor f n t hr
  exact ⟨hp.1, hp.2.1.1, hr.1.1⟩

theorem record_not_short (f : Nat → Bool) (n t : Nat) (hr : localRecord f n t) :
    ¬ shortEndpoint f n t := hr.2.1

/-- A strict record has no strict record predecessor. -/
theorem record_predecessor_not_record (f : Nat → Bool) (n t : Nat)
    (hr : localRecord f n t) : ¬ localRecord f n (t-1) :=
  (local_record_supplied_predecessor f n t hr).2.2

theorem record_successor_not_record (f : Nat → Bool) (n t : Nat)
    (hr : localRecord f n t) : ¬ localRecord f n (t+1) := by
  intro hR1
  exact record_predecessor_not_record f n (t+1) hR1 hr

/-- A short endpoint excludes a record at the position before its S. -/
theorem short_excludes_previous_record (f : Nat → Bool) (n m : Nat)
    (hm : shortEndpoint f n m) (hr : localRecord f n (m-2)) : False := by
  have hA : f (m-3) = true :=
    (local_record_supplied_predecessor f n (m-2) hr).2.1.1
  have hS : f (m-3) = false := short_sign_false f n m hm
  rw [hA] at hS
  cases hS

theorem triple_cover (f : Nat → Bool) (n K e p : Nat) (hE : shortEndpoint f n e)
    (he : e < n+K) (h1 : e-2 ≤ p) (h2 : p ≤ e) : shortPairCovered f n K p :=
  .inl ⟨e,hE,he,h1,h2⟩

theorem pair_cover (f : Nat → Bool) (n K t p : Nat) (ht : localRecord f n t)
    (htK : t < n+K) (h1 : t-1 ≤ p) (h2 : p ≤ t) : shortPairCovered f n K p :=
  .inr ⟨t,ht,htK,h1,h2⟩

/-- Extending the interval only adds candidates, never removes them. -/
theorem covered_increasing (f : Nat → Bool) (n k p : Nat)
    (hp : shortPairCovered f n k p) : shortPairCovered f n (k+1) p := by
  rcases hp with ⟨e,hE,he,hle,hge⟩ | ⟨t,ht,htK,hle,hge⟩
  · exact .inl ⟨e,hE,by omega,hle,hge⟩
  · exact .inr ⟨t,ht,by omega,hle,hge⟩

private theorem cN_single (s k : Nat) (hk : 0 < k) :
    cN (fun p => p = s+k-1) s k = 1 := by
  let P := fun p => p = s+k-1
  have hadd : cN P s k = cN P s (k-1) + cN P (s+(k-1)) 1 := by
    have hk2 : k = (k-1)+1 := by omega
    conv => lhs; rw [hk2]
    exact cN_add P s (k-1) 1
  have hz : cN P s (k-1) = 0 := by
    apply cN_zero_of
    intro p h1 h2 hp
    omega
  have hP : s + (k-1) = s+k-1 := by omega
  have hone : cN P (s+k-1) 1 = 1 := by
    have hz0 : cN P (s+k-1) 0 = 0 := rfl
    rw [show (1:Nat) = 0+1 from rfl, cN_succ_pos P (s+k-1) 0 (by omega), hz0]
  rw [hadd, hz, hP, hone]

private theorem cN_double (s k : Nat) (hk : s+2 ≤ s+k) :
    cN (fun p => p = s+k-2 ∨ p = s+k-1) s k = 2 := by
  let P := fun p => p = s+k-2 ∨ p = s+k-1
  have hadd : cN P s k = cN P s (k-2) + cN P (s+(k-2)) 2 := by
    have hk2 : k = (k-2)+2 := by omega
    conv => lhs; rw [hk2]
    exact cN_add P s (k-2) 2
  have hz : cN P s (k-2) = 0 := by
    apply cN_zero_of
    intro p h1 h2 hp
    rcases hp with h | h <;> omega
  have hP : s + (k-2) = s+k-2 := by omega
  have htwo : cN P (s+k-2) 2 = 2 := by
    have h0 : cN P (s+k-2) 0 = 0 := rfl
    rw [show (2:Nat) = 1+1 from rfl,
      cN_succ_pos P (s+k-2) 1 (by right; omega),
      show (1:Nat) = 0+1 from rfl,
      cN_succ_pos P (s+k-2) 0 (by left; omega)]
    omega
  rw [hadd, hz, hP, htwo]

private theorem cN_inclusion_delta (P Q : Nat → Prop) (s k : Nat)
    (hsub : ∀ p, P p → Q p) :
    cN Q s k = cN P s k + cN (fun p => Q p ∧ ¬ P p) s k := by
  have hsplit := cN_split (P := Q) (Q := P) s k
  have hcong : cN (fun p => Q p ∧ P p) s k = cN P s k :=
    cN_congr (P := fun p => Q p ∧ P p) (Q := P) s k
      (fun p _ _ => ⟨fun h => h.2, fun hp => ⟨hsub p hp, hp⟩⟩)
  rw [hcong] at hsplit
  omega

theorem covered_le_additions (f : Nat → Bool) (n K : Nat) :
    cN (shortPairCovered f n K) n K ≤ additions f n K := by
  apply cN_mono (P := fun p => shortPairCovered f n K p)
    (Q := fun t => f t = true) n K
  intro p hp1 hp2 hp
  cases hp with
  | inl h =>
    obtain ⟨e,hE,he,hle,hge⟩ := h
    obtain ⟨_,hS,h2,h1,hA⟩ := hE
    have hpos : p = e-2 ∨ p = e-1 ∨ p = e := by omega
    rcases hpos with rfl|rfl|rfl
    · exact h2
    · exact h1
    · exact hA
  | inr h =>
    obtain ⟨t,ht,htK,hle,hge⟩ := h
    have hpos : p = t-1 ∨ p = t := by omega
    rcases hpos with rfl|rfl
    · exact (local_record_supplied_predecessor f n t ht).2.1.1
    · exact ht.1.1

private theorem after_step (f : Nat → Bool) (n k : Nat) :
    cN (fun t => localRecord f n t ∧ t+1 < n+k+1 ∧ shortEndpoint f n (t+1)) n (k+1)
    = cN (fun t => localRecord f n t ∧ t+1 < n+k ∧ shortEndpoint f n (t+1)) n k
      + (if localRecord f n (n+k-1) ∧ shortEndpoint f n (n+k) then 1 else 0) := by
  let Ck1 := fun t => localRecord f n t ∧ t+1 < n+k+1 ∧ shortEndpoint f n (t+1)
  let Ck := fun t => localRecord f n t ∧ t+1 < n+k ∧ shortEndpoint f n (t+1)
  by_cases hk : k = 0
  · subst hk
    have h1 : cN Ck1 n 1 = 0 := by
      have hn : ¬ Ck1 n := by
        intro h
        exact (show ¬ (n+1) < n+1 by omega) h.2.1
      rw [cN_succ_neg Ck1 n 0 hn, cN]
    have h2 : cN Ck n 0 = 0 := rfl
    have h3 : ¬(localRecord f n (n+0-1) ∧ shortEndpoint f n (n+0)) := by
      intro h; have : n+3 ≤ n+0 := (h.2).1; omega
    rw [h1,h2,if_neg h3]
  · have hM : ¬ Ck1 (n+k) := by
      intro h
      exact (show ¬ (n+k)+1 < n+k+1 by omega) h.2.1
    have hstep1 : cN Ck1 n (k+1) = cN Ck1 n k := cN_succ_neg Ck1 n k hM
    have hN : ¬ Ck (n+(k-1)) := by
      intro h
      exact (show ¬ (n+(k-1))+1 < n+k by omega) h.2.1
    have hstep2 : cN Ck n k = cN Ck n (k-1) := by
      conv => lhs; rw [show k = (k-1)+1 from by omega]
      exact cN_succ_neg Ck n (k-1) hN
    have hstep3 : cN Ck1 n k = cN Ck1 n (k-1) +
        (if Ck1 (n+(k-1)) then 1 else 0) := by
      rcases Classical.em (Ck1 (n+(k-1))) with h | h
      · conv => lhs; rw [show k = (k-1)+1 from by omega]
        rw [cN_succ_pos Ck1 n (k-1) h, if_pos h]
      · conv => lhs; rw [show k = (k-1)+1 from by omega]
        rw [cN_succ_neg Ck1 n (k-1) h, if_neg h]
        omega
    have hshift : n+k-1 = n+(k-1) := by omega
    have hcong : cN Ck1 n (k-1) = cN Ck n (k-1) := by
      apply cN_congr (P := Ck1) (Q := Ck) n (k-1)
      intro t h1 h2
      constructor
      · intro h
        exact ⟨h.1,by omega,h.2.2⟩
      · intro h
        exact ⟨h.1,by omega,h.2.2⟩
    have heq : (Ck1 (n+(k-1)) ↔
        (localRecord f n (n+k-1) ∧ shortEndpoint f n (n+k))) := by
      constructor
      · intro h
        have h1 : localRecord f n (n+k-1) := by rw [hshift]; exact h.1
        have h2 : shortEndpoint f n (n+k) := by
          rw [show n+k = (n+(k-1))+1 from by omega]
          exact h.2.2
        exact ⟨h1, h2⟩
      · intro h
        have h1 : localRecord f n (n+(k-1)) := by rw [← hshift]; exact h.1
        have h2 : shortEndpoint f n ((n+(k-1))+1) := by
          rw [show (n+(k-1))+1 = n+k from by omega]
          exact h.2
        exact ⟨h1, by omega, h2⟩
    rcases Classical.em (Ck1 (n+(k-1))) with h | h
    · rw [hstep1, hstep3, if_pos h, if_pos (heq.mp h), hcong, hstep2]

    · rw [hstep1, hstep3, if_neg h, if_neg (fun hc => h (heq.mpr hc)), hcong, hstep2]

/-- A new short endpoint adds its three original A positions unless a record
already covers part of the triple. -/
theorem step_short (f : Nat → Bool) (n k : Nat) (hm : shortEndpoint f n (n+k))
    (hRm1 : ¬ localRecord f n (n+k-1)) :
    cN (shortPairCovered f n (k+1)) n (k+1) ≥
      cN (shortPairCovered f n k) n k + 3 := by
  have hge3 : 3 ≤ k := by
    obtain ⟨hge, _, _, _, _⟩ := hm
    omega
  have hfresh1 : ¬ shortPairCovered f n k (n+k-1) := by
    intro hP
    rcases hP with (⟨e,hE,he,le,ge⟩ | ⟨t,ht,htK,le,ge⟩)
    · have hgap := short_endpoints_gap f n e (n+k) hE hm (by omega)
      omega
    · have ht' : t = n+k-1 := by omega
      subst ht'; exact hRm1 ht
  have hfresh2 : ¬ shortPairCovered f n k (n+k-2) := by
    intro hP
    rcases hP with (⟨e,hE,he,le,ge⟩ | ⟨t,ht,htK,le,ge⟩)
    · have hgap := short_endpoints_gap f n e (n+k) hE hm (by omega)
      omega
    · have ht' : t = n+k-2 ∨ t = n+k-1 := by omega
      rcases ht' with rfl | rfl
      · exact short_excludes_previous_record f n (n+k) hm ht
      · exact hRm1 ht
  have hnew1 : shortPairCovered f n (k+1) (n+k-2) :=
    triple_cover f n (k+1) (n+k) (n+k-2) hm (by omega) (by omega) (by omega)
  have hnew2 : shortPairCovered f n (k+1) (n+k-1) :=
    triple_cover f n (k+1) (n+k) (n+k-1) hm (by omega) (by omega) (by omega)
  have hnew : shortPairCovered f n (k+1) (n+k) :=
    triple_cover f n (k+1) (n+k) (n+k) hm (by omega) (by omega) (by omega)
  have hstepk : cN (shortPairCovered f n (k+1)) n (k+1) =
      cN (shortPairCovered f n (k+1)) n k + 1 :=
    cN_succ_pos (shortPairCovered f n (k+1)) n k hnew
  have hinc := cN_inclusion_delta (P := shortPairCovered f n k)
    (Q := shortPairCovered f n (k+1)) n k
    (fun p hp => covered_increasing f n k p hp)
  have hmono2 := cN_mono (fun p => p = n+k-2 ∨ p = n+k-1)
    (fun p => shortPairCovered f n (k+1) p ∧ ¬ shortPairCovered f n k p) n k
    (fun p _ _ hp => by
      rcases hp with rfl | rfl
      · exact ⟨hnew1,hfresh2⟩
      · exact ⟨hnew2,hfresh1⟩)
  have hfin := cN_double n k (by omega)
  omega

/-- A record preceded by a short endpoint adds only its endpoint; the pair
overlaps the triple. This is the C type of the E642 example. -/
theorem step_short_overlap (f : Nat → Bool) (n k : Nat) (hm : shortEndpoint f n (n+k))
    (_hRm1 : localRecord f n (n+k-1)) :
    cN (shortPairCovered f n (k+1)) n (k+1) ≥
      cN (shortPairCovered f n k) n k + 1 := by
  have hnew : shortPairCovered f n (k+1) (n+k) :=
    triple_cover f n (k+1) (n+k) (n+k) hm (by omega) (by omega) (by omega)
  have hstepk : cN (shortPairCovered f n (k+1)) n (k+1) =
      cN (shortPairCovered f n (k+1)) n k + 1 :=
    cN_succ_pos (shortPairCovered f n (k+1)) n k hnew
  have hmono := cN_mono (shortPairCovered f n k) (shortPairCovered f n (k+1)) n k
    (fun p _ _ hp => covered_increasing f n k p hp)
  omega

/-- A record followed by no short endpoint adds both pair positions. -/
theorem step_record_fresh (f : Nat → Bool) (n k : Nat) (hR : localRecord f n (n+k))
    (hLm1 : ¬ shortEndpoint f n (n+k-1)) :
    cN (shortPairCovered f n (k+1)) n (k+1) ≥
      cN (shortPairCovered f n k) n k + 2 := by
  have hn : n+1 ≤ n+k := by
    have hlt := (local_record_supplied_predecessor f n (n+k) hR).1
    omega
  have hfresh : ¬ shortPairCovered f n k (n+k-1) := by
    intro hP
    rcases hP with (⟨e,hE,he,le,ge⟩ | ⟨t,ht,htK,le,ge⟩)
    · have he' : e = n+k-1 := by omega
      subst he'; exact hLm1 hE
    · have ht' : t = n+k-1 := by omega
      subst ht'
      exact record_predecessor_not_record f n (n+k) hR ht
  have hnew1 : shortPairCovered f n (k+1) (n+k-1) :=
    pair_cover f n (k+1) (n+k) (n+k-1) hR (by omega) (by omega) (by omega)
  have hnew : shortPairCovered f n (k+1) (n+k) :=
    pair_cover f n (k+1) (n+k) (n+k) hR (by omega) (by omega) (by omega)
  have hstepk : cN (shortPairCovered f n (k+1)) n (k+1) =
      cN (shortPairCovered f n (k+1)) n k + 1 :=
    cN_succ_pos (shortPairCovered f n (k+1)) n k hnew
  have hinc := cN_inclusion_delta (P := shortPairCovered f n k)
    (Q := shortPairCovered f n (k+1)) n k
    (fun p hp => covered_increasing f n k p hp)
  have hmono1 := cN_mono (fun p => p = n+k-1)
    (fun p => shortPairCovered f n (k+1) p ∧ ¬ shortPairCovered f n k p) n k
    (fun p _ _ hp => by subst hp; exact ⟨hnew1,hfresh⟩)
  have hfin := cN_single n k (by omega)
  omega

/-- A record preceded by a short endpoint adds only its endpoint. This is the
B type of the E642 example. -/
theorem step_record_left (f : Nat → Bool) (n k : Nat) (hR : localRecord f n (n+k))
    (_hLm1 : shortEndpoint f n (n+k-1)) :
    cN (shortPairCovered f n (k+1)) n (k+1) ≥
      cN (shortPairCovered f n k) n k + 1 := by
  have hnew : shortPairCovered f n (k+1) (n+k) :=
    pair_cover f n (k+1) (n+k) (n+k) hR (by omega) (by omega) (by omega)
  have hstepk : cN (shortPairCovered f n (k+1)) n (k+1) =
      cN (shortPairCovered f n (k+1)) n k + 1 :=
    cN_succ_pos (shortPairCovered f n (k+1)) n k hnew
  have hmono := cN_mono (shortPairCovered f n k) (shortPairCovered f n (k+1)) n k
    (fun p _ _ hp => covered_increasing f n k p hp)
  omega

theorem step_none (f : Nat → Bool) (n k : Nat) :
    cN (shortPairCovered f n (k+1)) n (k+1) ≥ cN (shortPairCovered f n k) n k := by
  have hpre := count_prefix_le (shortPairCovered f n k) n k (k+1) (by omega)
  have hmono := cN_mono (shortPairCovered f n k) (shortPairCovered f n (k+1)) n (k+1)
    (fun p _ _ hp => covered_increasing f n k p hp)
  omega

/-- Per-position inclusion delta: the growth of a monotone count is the count
of newly included positions. -/
private theorem covered_step (f : Nat → Bool) (n k : Nat) :
    cN (shortPairCovered f n (k+1)) n (k+1)
    + (if localRecord f n (n+k) ∧ shortEndpoint f n (n+k-1) then 1 else 0)
    + 2*(if localRecord f n (n+k-1) ∧ shortEndpoint f n (n+k) then 1 else 0) ≥
      cN (shortPairCovered f n k) n k
      + 3*(if shortEndpoint f n (n+k) then 1 else 0)
      + 2*(if localRecord f n (n+k) then 1 else 0) := by
  rcases Classical.em (shortEndpoint f n (n+k)) with hm | hm
  · have hnR : ¬ localRecord f n (n+k) := fun h => record_not_short f n (n+k) h hm
    rcases Classical.em (localRecord f n (n+k-1)) with hRm1 | hRm1
    · -- overlap of type C: the record's pair lies inside the new triple
      rw [if_neg (fun h => hnR h.1), if_pos ⟨hRm1, hm⟩, if_pos hm, if_neg hnR]
      have hstep := step_short_overlap f n k hm hRm1
      omega
    · have hCfalse : ¬ (localRecord f n (n+k-1) ∧ shortEndpoint f n (n+k)) :=
        fun h => hRm1 h.1
      rw [if_neg (fun h => hnR h.1), if_neg hCfalse, if_pos hm, if_neg hnR]
      have hstep := step_short f n k hm hRm1
      omega
  · rcases Classical.em (localRecord f n (n+k)) with hR | hR
    · rcases Classical.em (shortEndpoint f n (n+k-1)) with hLm1 | hLm1
      · -- overlap of type B: the endpoint position was covered by the triple
        rw [if_pos ⟨hR, hLm1⟩, if_neg (fun h => hm h.2), if_neg hm, if_pos hR]
        have hstep := step_record_left f n k hR hLm1
        omega
      · rw [if_neg (fun h => hLm1 h.2), if_neg (fun h => hm h.2), if_neg hm, if_pos hR]
        have hstep := step_record_fresh f n k hR hLm1
        omega
    · rw [if_neg (fun h => hR h.1), if_neg (fun h => hm h.2), if_neg hm, if_neg hR]
      have hstep := step_none f n k
      omega

/-- **E643 overlap budget, covered form.** The weighted supply of short
triples and records is bounded by covered original additions plus the
overlap corrections. -/
theorem budget_covered (f : Nat → Bool) (n K : Nat) :
    3*cN (shortEndpoint f n) n K + 2*cN (localRecord f n) n K ≤
      cN (shortPairCovered f n K) n K
      + cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n K
      + 2*cN (fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)) n K := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    cases K with
    | zero => simp [cN]
    | succ k =>
      obtain hprev := ih k (by omega)
      change 3*cN (shortEndpoint f n) n k + 2*cN (localRecord f n) n k ≤
        cN (shortPairCovered f n k) n k
        + cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n k
        + 2*cN (fun t => localRecord f n t ∧ t+1 < n+k ∧ shortEndpoint f n (t+1)) n k at hprev
      have hL : cN (shortEndpoint f n) n (k+1) = cN (shortEndpoint f n) n k +
          (if shortEndpoint f n (n+k) then 1 else 0) := by
        by_cases h : shortEndpoint f n (n+k)
        · rw [cN_succ_pos (shortEndpoint f n) n k h, if_pos h]
        · rw [cN_succ_neg (shortEndpoint f n) n k h, if_neg h]
          omega
      have hR : cN (localRecord f n) n (k+1) = cN (localRecord f n) n k +
          (if localRecord f n (n+k) then 1 else 0) := by
        by_cases h : localRecord f n (n+k)
        · rw [cN_succ_pos (localRecord f n) n k h, if_pos h]
        · rw [cN_succ_neg (localRecord f n) n k h, if_neg h]
          omega
      have hB : cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n (k+1) =
          cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n k +
          (if localRecord f n (n+k) ∧ shortEndpoint f n (n+k-1) then 1 else 0) := by
        by_cases h : localRecord f n (n+k) ∧ shortEndpoint f n (n+k-1)
        · rw [cN_succ_pos _ n k h, if_pos h]
        · rw [cN_succ_neg _ n k h, if_neg h]
          omega
      have hC := after_step f n k
      have cs := covered_step f n k
      rw [hL]
      rw [hR]
      rw [hB]
      rw [show n+(k+1) = n+k+1 from by omega]
      rw [hC]
      rcases Classical.em (shortEndpoint f n (n+k)) with hm | hm
      · have hnR : ¬ localRecord f n (n+k) := fun h => record_not_short f n (n+k) h hm
        rcases Classical.em (localRecord f n (n+k-1)) with hrm | hrm
        · rw [if_pos hm, if_neg hnR, if_neg (fun h => hnR h.1), if_pos ⟨hrm, hm⟩]
          rw [if_pos hm, if_neg hnR, if_neg (fun h => hnR h.1), if_pos ⟨hrm, hm⟩] at cs
          omega
        · rw [if_pos hm, if_neg hnR, if_neg (fun h => hnR h.1), if_neg (fun h => hrm h.1)]
          rw [if_pos hm, if_neg hnR, if_neg (fun h => hnR h.1), if_neg (fun h => hrm h.1)] at cs
          omega
      · rcases Classical.em (localRecord f n (n+k)) with hr | hr
        · rcases Classical.em (shortEndpoint f n (n+k-1)) with hsm | hsm
          · rw [if_neg hm, if_pos hr, if_pos ⟨hr, hsm⟩, if_neg (fun h => hm h.2)]
            rw [if_neg hm, if_pos hr, if_pos ⟨hr, hsm⟩, if_neg (fun h => hm h.2)] at cs
            omega
          · rw [if_neg hm, if_pos hr, if_neg (fun h => hsm h.2), if_neg (fun h => hm h.2)]
            rw [if_neg hm, if_pos hr, if_neg (fun h => hsm h.2), if_neg (fun h => hm h.2)] at cs
            omega
        · rw [if_neg hm, if_neg hr, if_neg (fun h => hr h.1), if_neg (fun h => hm h.2)]
          rw [if_neg hm, if_neg hr, if_neg (fun h => hr h.1), if_neg (fun h => hm h.2)] at cs
          omega

/-- **E643 overlap budget.** For one original history and interval,
`3 * (short supplies) + 2 * (strict records)` is at most the internal
additions plus once the overlap of a record with a preceding short triple
and twice the overlap with a following one. -/
theorem short_record_overlap_budget (f : Nat → Bool) (n K : Nat) :
    3*cN (shortEndpoint f n) n K + 2*cN (localRecord f n) n K ≤
      additions f n K
      + cN (fun t => localRecord f n t ∧ shortEndpoint f n (t-1)) n K
      + 2*cN (fun t => localRecord f n t ∧ t+1 < n+K ∧ shortEndpoint f n (t+1)) n K := by
  have h := budget_covered f n K
  have hc := covered_le_additions f n K
  omega

end Recaman.ShortRecordOverlapBudget
