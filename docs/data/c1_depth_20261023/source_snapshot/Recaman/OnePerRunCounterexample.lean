import Recaman.NoSSMassOne

namespace Recaman.OnePerRunCounterexample

open LeadingRunSupply OnePerRun NoSSMassOne OneSSMultiplicity
open LowSSEndpoint SSFreeSupply

/-! Unrestricted consecutive one-per-run is false on abstract streams.
Gluing the sharp NoSS mass-1 extra `minWord (|v|-1)` to a mass-0,
moment-(-1), SS=2 tail `v` yields two minimum P2 SS=2 windows at
consecutive A times: later `A++v` and earlier `v++minWord`. This is
the equality case of E-140, not a Recamán-orbit fact. -/

theorem minWord_head (r : Nat) : (minWord r).head? = some true := rfl

theorem A_cons_P2 (v : List Bool) (hm : mass v = 0) (hM : moment v = -1) :
    P2 (true :: v) := by
  constructor
  · simp [mass_cons, ShortPeriodicSupply.sign, hm]
  · simp [moment, ShortPeriodicSupply.sign, hm, hM]

/-- Mass and moment of a reverse-nested consecutive pair, with no SS
hypothesis. Later `A++v` and earlier `v++extra` being P2 forces
`mass v = 0`, `moment v = -1`, `mass extra = 1`, and
`moment extra = 1-|v|`. The SS=3 extras and the high-SS gap-1 pairs
both satisfy this. -/
theorem reverse_nested_mass_moment (v extra : List Bool)
    (hnew : P2 (true :: v)) (hold : P2 (v ++ extra)) :
    mass v = 0 ∧ moment v = -1 ∧ mass extra = 1 ∧
      moment extra = 1 - (v.length : Int) := by
  have hmassv : mass v = 0 := by
    simp [P2, mass_cons, ShortPeriodicSupply.sign] at hnew
    omega
  have hMv : moment v = -1 := by
    simp [P2, moment, ShortPeriodicSupply.sign] at hnew
    omega
  have hmasse : mass extra = 1 := by
    have hm := mass_append v extra
    have := hold.1
    rw [hm, hmassv] at this
    omega
  have hMe : moment extra = 1 - (v.length : Int) := by
    have hma := moment_append v extra
    have := hold.2
    rw [hma, hMv, hmasse] at this
    omega
  exact ⟨hmassv, hMv, hmasse, hMe⟩

/-- Reverse-nested pair identity, any SS count. The later window is `A++v`
and the earlier is `v++extra`. Extra is SS-free of mass 1 with the E-140
moment. This covers both the minWord equality family (k=2) and the
canonical SS=3 extras (k=3, extra starts SA). -/
theorem reverse_nested_identities (v extra : List Bool) (k : Nat)
    (hm : mass v = 0) (hM : moment v = -1)
    (he : mass extra = 1)
    (hMe : moment extra = 1 - (v.length : Int))
    (hssv : ssCount v = k) (hsse : ssCount extra = 0)
    (hjoin : ¬ (v.getLast? = some false ∧ extra.head? = some false)) :
    P2 (true :: v) ∧ ssCount (true :: v) = k ∧
      P2 (v ++ extra) ∧ ssCount (v ++ extra) = k := by
  refine ⟨A_cons_P2 v hm hM, ?ssn, ⟨?mass, ?mom⟩, ?sso⟩
  case ssn => simpa [ssCount_cons_A] using hssv
  case mass => rw [mass_append, hm, he]; omega
  case mom => rw [moment_append, hM, he, hMe]; omega
  case sso =>
    have happ := ssCount_append v extra
    by_cases hj : v.getLast? = some false ∧ extra.head? = some false
    · exact False.elim (hjoin hj)
    · simp [hj, hssv, hsse] at happ
      omega

/-- Family identity: any mass-0 moment-(-1) SS=2 tail of length `r+1`
glued to `minWord r` is P2 with SS=2. Join SS cannot occur because
`minWord` starts with A. -/
theorem equality_glue (v : List Bool) (r : Nat)
    (hm : mass v = 0) (hM : moment v = -1)
    (hlen : v.length = r + 1) (hss : ssCount v = 2) :
    P2 (v ++ minWord r) ∧ ssCount (v ++ minWord r) = 2 := by
  have hMe : moment (minWord r) = 1 - (v.length : Int) := by
    rw [minWord_moment]
    have : (v.length : Int) = ↑r + 1 := by exact_mod_cast hlen
    omega
  have hjoin : ¬ (v.getLast? = some false ∧ (minWord r).head? = some false) := by
    simp [minWord_head]
  have h := reverse_nested_identities v (minWord r) 2 hm hM (minWord_mass r) hMe
    hss (minWord_ssCount r) hjoin
  exact ⟨h.2.2.1, h.2.2.2⟩

def vWord : List Bool :=
  [false, false, true, true, true, false, true, true, false, false]

def extraWord : List Bool := minWord 9

def newWord : List Bool := true :: vWord

def oldWord : List Bool := vWord ++ extraWord

theorem vWord_data :
    mass vWord = 0 ∧ moment vWord = -1 ∧ ssCount vWord = 2 ∧
      vWord.length = 10 := by
  unfold vWord mass moment ssCount
  decide

theorem extraWord_eq : extraWord = minWord 9 := rfl

theorem newWord_P2 : P2 newWord :=
  A_cons_P2 vWord vWord_data.1 vWord_data.2.1

theorem newWord_ss : ssCount newWord = 2 := by
  simpa [newWord, ssCount_cons_A] using vWord_data.2.2.1

set_option maxHeartbeats 0 in
theorem newWord_min : ∀ d : Fin 11, ¬ P2 (newWord.take d.val) := by
  unfold P2 newWord vWord
  decide

theorem oldWord_P2_ss : P2 oldWord ∧ ssCount oldWord = 2 :=
  equality_glue vWord 9 vWord_data.1 vWord_data.2.1
    (by simpa using vWord_data.2.2.2) vWord_data.2.2.1

def extraLit : List Bool :=
  [true, true,
   false, true, false, true, false, true, false, true, false, true,
   false, true, false, true, false, true, false, true,
   false]

theorem extraLit_eq : extraWord = extraLit := by
  unfold extraWord extraLit minWord alt
  decide

set_option maxHeartbeats 0 in
theorem oldWord_min : ∀ d : Fin 31, ¬ P2 (oldWord.take d.val) := by
  have h : oldWord = vWord ++ extraLit := by simp [oldWord, extraLit_eq]
  rw [h]
  unfold P2 vWord extraLit
  decide

/-- Embed a newest-first word as the backward history ending just
before clock `t`. Signs at `t` and later default to A. -/
def fromWord (w : List Bool) (t : Int) (s : Int) : Bool :=
  let k := t - s - 1
  if 0 ≤ k then w.getD k.toNat true else true

theorem fromWord_at (w : List Bool) (t : Int) (i : Nat) (hi : i < w.length) :
    fromWord w t (t - ((i + 1 : Nat) : Int)) = w[i] := by
  unfold fromWord
  have hk : t - (t - ((i + 1 : Nat) : Int)) - 1 = (i : Int) := by omega
  rw [hk]
  simp [Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem past_fromWord (w : List Bool) (t : Int) :
    past (fromWord w t) t w.length = w := by
  apply List.ext_getElem
  · simp [past]
  · intro i hi hw
    simp [past]
    exact fromWord_at w t i hw

def eqFamilySign : Int → Bool := fromWord oldWord 31

theorem eqFamily_old_past : past eqFamilySign 31 31 = oldWord := by
  simpa [eqFamilySign, oldWord, extraWord, minWord_length, vWord] using
    past_fromWord oldWord 31

theorem eqFamily_current : eqFamilySign 31 = true := by
  unfold eqFamilySign fromWord
  decide

theorem eqFamily_next : eqFamilySign 32 = true := by
  unfold eqFamilySign fromWord
  decide

theorem eqFamily_new_past : past eqFamilySign 32 11 = newWord := by
  have hsplit := past_append eqFamilySign 32 1 10
  have h1 : past eqFamilySign 32 1 = [true] := by
    simp [past, eqFamily_current]
  have h10 : past eqFamilySign 31 10 = vWord := by
    have ht := take_past eqFamilySign 31 31 10 (by decide)
    rw [← ht, eqFamily_old_past]
    simp [oldWord]
    exact List.take_left' (show vWord.length = 10 from rfl)
  have htime : (32 : Int) - (1 : Nat) = 31 := by decide
  simpa [h1, htime, h10, newWord] using hsplit

theorem eqFamily_old_stream_P2 :
    ShortPeriodicSupply.P2 eqFamilySign 31 31 :=
  (past_p2_iff eqFamilySign 31 31).mp
    (eqFamily_old_past ▸ oldWord_P2_ss.1)

theorem eqFamily_new_stream_P2 :
    ShortPeriodicSupply.P2 eqFamilySign 32 11 :=
  (past_p2_iff eqFamilySign 32 11).mp
    (eqFamily_new_past ▸ newWord_P2)

theorem eqFamily_old_stream_min :
    ∀ k : Nat, k < 31 → ¬ ShortPeriodicSupply.P2 eqFamilySign 31 k := by
  intro k hk hP
  have hword := (past_p2_iff eqFamilySign 31 k).mpr hP
  have ht := take_past eqFamilySign 31 31 k (Nat.le_of_lt hk)
  rw [← ht, eqFamily_old_past] at hword
  exact oldWord_min ⟨k, hk⟩ hword

theorem eqFamily_new_stream_min :
    ∀ k : Nat, k < 11 → ¬ ShortPeriodicSupply.P2 eqFamilySign 32 k := by
  intro k hk hP
  have hword := (past_p2_iff eqFamilySign 32 k).mpr hP
  have ht := take_past eqFamilySign 32 11 k (Nat.le_of_lt hk)
  rw [← ht, eqFamily_new_past] at hword
  exact newWord_min ⟨k, hk⟩ hword

/-- Consecutive current-A times can both carry a minimum P2 SS=2 window.
The later lag is 11, the earlier lag is 31, and they share an A-run of
length at least 2. This refutes unrestricted one-per-run on free histories. -/
theorem unrestricted_one_per_run_false :
    ∃ (e : Int → Bool) (t : Int) (d f : Nat),
      e t = true ∧ e (t + 1) = true ∧
      1 ≤ f ∧ f ≤ d ∧
      ShortPeriodicSupply.P2 e t d ∧
      (∀ k, k < d → ¬ ShortPeriodicSupply.P2 e t k) ∧
      ssCount (past e t d) = 2 ∧
      ShortPeriodicSupply.P2 e (t + 1) f ∧
      (∀ k, k < f → ¬ ShortPeriodicSupply.P2 e (t + 1) k) ∧
      ssCount (past e (t + 1) f) = 2 := by
  refine ⟨eqFamilySign, 31, 31, 11, eqFamily_current, eqFamily_next,
    by decide, by decide, eqFamily_old_stream_P2, eqFamily_old_stream_min, ?_,
    eqFamily_new_stream_P2, eqFamily_new_stream_min, ?_⟩
  · simpa [eqFamily_old_past] using oldWord_P2_ss.2
  · simpa [eqFamily_new_past] using newWord_ss

end Recaman.OnePerRunCounterexample

