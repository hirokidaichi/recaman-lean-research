import Recaman.LocalParitySupply

namespace Recaman.SSFreeSupply

open LeadingRunSupply LocalParitySupply

/-! The canonical no-SAAS language turns SS-free P2 windows into clean ones.
The language assumptions are explicit; arbitrary periodic words may have SAAS. -/

def NoSS (w : List Bool) : Prop :=
  ∀ u v : List Bool, w ≠ u ++ false :: false :: v

def NoSAAS (w : List Bool) : Prop :=
  ∀ u v : List Bool, w ≠ u ++ false :: true :: true :: false :: v

def alt (b : Bool) : Nat → List Bool
  | 0 => []
  | n+1 => b :: (!b) :: alt b n

def EvenSlots : List Bool → Prop
  | [] => True
  | [_] => True
  | _ :: b :: w => b = true ∧ EvenSlots w

theorem noSS_tail (b : Bool) (w : List Bool) (h : NoSS (b::w)) : NoSS w := by
  intro u v heq
  apply h (b::u) v
  simp [heq]

theorem noSAAS_tail (b : Bool) (w : List Bool) (h : NoSAAS (b::w)) : NoSAAS w := by
  intro u v heq
  apply h (b::u) v
  simp [heq]

theorem noSS_mass_lower (w : List Bool) (h : NoSS w) : -1 ≤ mass w := by
  cases w with
  | nil => simp
  | cons b w =>
    cases b with
    | true =>
      have ih := noSS_mass_lower w (noSS_tail true w h)
      simp only [mass_cons,ShortPeriodicSupply.sign,↓reduceIte]
      omega
    | false =>
      cases w with
      | nil => decide
      | cons b w =>
        cases b with
        | false => exact False.elim (h [] w rfl)
        | true =>
          have ih := noSS_mass_lower w (noSS_tail true w (noSS_tail false (true::w) h))
          simp only [mass_cons,ShortPeriodicSupply.sign,↓reduceIte]
          omega
termination_by w.length

theorem alt_mass (b : Bool) (n : Nat) : mass (alt b n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases b <;> simp [alt,ShortPeriodicSupply.sign,ih]

theorem alt_S_moment (n : Nat) : moment (alt false n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [alt,moment,ShortPeriodicSupply.sign,alt_mass,ih]; omega

/-- Zero-mass words in this language alternate exactly. This decomposition
is proved from the original forbidden-subword hypotheses. -/
theorem mass_zero_alternates (w : List Bool) (hss : NoSS w) (hsaas : NoSAAS w)
    (hm : mass w = 0) : ∃ n : Nat, w = alt true n ∨ w = alt false n := by
  cases w with
  | nil => exact ⟨0,Or.inl rfl⟩
  | cons b w =>
    cases w with
    | nil => cases b <;> simp [mass_cons,ShortPeriodicSupply.sign] at hm
    | cons c w =>
      have hssw := noSS_tail c w (noSS_tail b (c::w) hss)
      have hsaasw := noSAAS_tail c w (noSAAS_tail b (c::w) hsaas)
      cases b <;> cases c
      · exact False.elim (hss [] w rfl)
      · have hm' : mass w = 0 := by simp [ShortPeriodicSupply.sign] at hm; omega
        obtain ⟨n,hn | hn⟩ := mass_zero_alternates w hssw hsaasw hm'
        · cases n with
          | zero => exact ⟨1,Or.inr (by simp [hn,alt])⟩
          | succ n =>
            exact False.elim (hsaas [] (alt true n) (by simp [hn,alt]))
        · exact ⟨n+1,Or.inr (by simp [hn,alt])⟩
      · have hm' : mass w = 0 := by simp [ShortPeriodicSupply.sign] at hm; omega
        obtain ⟨n,hn | hn⟩ := mass_zero_alternates w hssw hsaasw hm'
        · exact ⟨n+1,Or.inl (by simp [hn,alt])⟩
        · cases n with
          | zero => exact ⟨1,Or.inl (by simp [hn,alt])⟩
          | succ n =>
            exact False.elim (hss [true] (true::alt false n) (by simp [hn,alt]))
      · have hl := noSS_mass_lower w hssw
        simp [ShortPeriodicSupply.sign] at hm
        omega
termination_by w.length

theorem evenSlots_pre_alt_A (b : Bool) (n : Nat) : EvenSlots (b :: alt true n) := by
  induction n generalizing b with
  | zero => trivial
  | succ n ih => exact ⟨rfl,ih false⟩

/-- Mass one and the language constraints already imply cleanliness unless
the first moment is strictly positive. -/
theorem mass_one_even_or_positive (w : List Bool) (hss : NoSS w) (hsaas : NoSAAS w)
    (hm : mass w = 1) : EvenSlots w ∨ 0 < moment w := by
  cases w with
  | nil => simp at hm
  | cons b w =>
    have hssw := noSS_tail b w hss
    have hsaasw := noSAAS_tail b w hsaas
    cases b with
    | true =>
      have hm' : mass w = 0 := by simp [ShortPeriodicSupply.sign] at hm; omega
      obtain ⟨n,hn | hn⟩ := mass_zero_alternates w hssw hsaasw hm'
      · exact Or.inl (hn ▸ evenSlots_pre_alt_A true n)
      · right
        rw [hn]
        simp [moment,ShortPeriodicSupply.sign,alt_mass,alt_S_moment]
        omega
    | false =>
      cases w with
      | nil => simp [ShortPeriodicSupply.sign] at hm
      | cons b w =>
        cases b with
        | false => exact False.elim (hss [] w rfl)
        | true =>
          have hm' : mass w = 1 := by simp [ShortPeriodicSupply.sign] at hm; omega
          rcases mass_one_even_or_positive w (noSS_tail true w hssw)
            (noSAAS_tail true w hsaasw) hm' with he | hp
          · exact Or.inl ⟨rfl,he⟩
          · right
            simp [moment,ShortPeriodicSupply.sign,hm']
            omega
termination_by w.length

theorem p2_noSS_noSAAS_even (w : List Bool) (hss : NoSS w) (hsaas : NoSAAS w)
    (hP : LeadingRunSupply.P2 w) : EvenSlots w := by
  rcases mass_one_even_or_positive w hss hsaas hP.1 with he | hp
  · exact he
  · rw [hP.2] at hp
    omega

theorem evenSlots_get (w : List Bool) (h : EvenSlots w) (i : Nat)
    (hi : i < w.length) (hodd : i % 2 = 1) : w[i] = true := by
  cases w with
  | nil => simp at hi
  | cons a w =>
    cases w with
    | nil => simp at hi; omega
    | cons b w =>
      cases i with
      | zero => omega
      | succ i =>
        cases i with
        | zero => exact h.1
        | succ i =>
          have hilt : i < w.length := by simp at hi; omega
          have hio : i % 2 = 1 := by omega
          exact evenSlots_get w h.2 i hilt hio
termination_by w.length

theorem evenSlots_of_get (w : List Bool)
    (h : ∀ i : Nat, (hi : i < w.length) → i % 2 = 1 → w[i] = true) : EvenSlots w := by
  cases w with
  | nil => trivial
  | cons a w =>
    cases w with
    | nil => trivial
    | cons b w =>
      refine ⟨h 1 (by simp) (by decide),?_⟩
      apply evenSlots_of_get w
      intro i hi hodd
      have hbig : i+2 < (a::b::w).length := by simp; omega
      exact h (i+2) hbig (by omega)
termination_by w.length

theorem evenSlots_past_iff (e : Int → Bool) (t : Int) (d : Nat) :
    EvenSlots (past e t d) ↔ EvenBackA e t d := by
  constructor
  · intro he i hi hid heven
    have hilen : i-1 < (past e t d).length := by simp [past]; omega
    have h := evenSlots_get (past e t d) he (i-1) hilen (by omega)
    simp only [past,List.getElem_map,List.getElem_range] at h
    have htime : t-(((i-1+1 : Nat)) : Int) = t-i := by omega
    rwa [htime] at h
  · intro ha
    apply evenSlots_of_get
    intro i hi hodd
    have hid : i+1 ≤ d := by simp [past] at hi; omega
    have h := ha (i+1) (by omega) hid (by omega)
    simpa only [past,List.getElem_map,List.getElem_range] using h

theorem not_evenSlots_withSS (u v : List Bool) :
    ¬ EvenSlots (u ++ false :: false :: v) := by
  cases u with
  | nil => simp [EvenSlots]
  | cons a u =>
    cases u with
    | nil => simp [EvenSlots]
    | cons b u =>
      intro h
      exact not_evenSlots_withSS u v h.2
termination_by u.length

theorem evenSlots_noSS (w : List Bool) (h : EvenSlots w) : NoSS w := by
  intro u v heq
  rw [heq] at h
  exact not_evenSlots_withSS u v h

theorem p2_noSS_iff_even (w : List Bool) (hsaas : NoSAAS w)
    (hP : LeadingRunSupply.P2 w) : NoSS w ↔ EvenSlots w := by
  exact ⟨fun hss => p2_noSS_noSAAS_even w hss hsaas hP,evenSlots_noSS w⟩

theorem stream_noSS_clean (e : Int → Bool) (t : Int) (d : Nat)
    (hss : NoSS (past e t d)) (hsaas : NoSAAS (past e t d))
    (hP : ShortPeriodicSupply.P2 e t d) : EvenBackA e t d := by
  have he := p2_noSS_noSAAS_even (past e t d) hss hsaas ((past_p2_iff e t d).mpr hP)
  exact (evenSlots_past_iff e t d).mp he

theorem noSS_cons_iff (b c : Bool) (w : List Bool) :
    NoSS (b::c::w) ↔ (b = true ∨ c = true) ∧ NoSS (c::w) := by
  constructor
  · intro h
    refine ⟨?_,noSS_tail b (c::w) h⟩
    cases b <;> cases c <;> simp
    exact False.elim (h [] w rfl)
  · rintro ⟨hbc,h⟩ u v heq
    cases u with
    | nil => simp at heq; rcases hbc with hb | hc <;> simp_all
    | cons a u =>
      have htail : c::w = u ++ false::false::v := (List.cons.inj heq).2
      exact h u v htail

theorem noSS_singleton (b : Bool) : NoSS [b] := by
  intro u v heq
  have hlen := congrArg List.length heq
  simp at hlen
  omega

/-- Dropping no-SAAS really changes the theorem: the lag-seven window has
no adjacent S but its positive even offsets are not all A. -/
theorem noSAAS_premise_counterexample :
    let w := [true,false,true,true,false,true,false]
    LeadingRunSupply.P2 w ∧ NoSS w ∧ ¬ EvenSlots w ∧ ¬ NoSAAS w := by
  refine ⟨by unfold LeadingRunSupply.P2; decide,?_,by simp [EvenSlots],?_⟩
  · simp only [noSS_cons_iff]
    simp [noSS_singleton]
  · intro h
    exact h [true] [true,false] rfl

end Recaman.SSFreeSupply
