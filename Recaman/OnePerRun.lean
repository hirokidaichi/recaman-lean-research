import Recaman.TwoSSLeadingSibling
import Recaman.SSFreeSupply

namespace Recaman.OnePerRun

open LeadingRunSupply OneSSMultiplicity SSFreeSupply
open LowSSEndpoint TwoSSLeadingSibling

/-! Nested half of consecutive one-per-run: a P2 SS=2 window that starts
with A cannot have an SS=2 P2 prefix in its tail. The longer-earlier
extension case is not claimed. -/

theorem ssCount_cons_A (v : List Bool) : ssCount (true::v) = ssCount v := by
  cases v <;> simp [ssCount]

theorem ssCount_append (u v : List Bool) :
    ssCount (u ++ v) = ssCount u + ssCount v +
      if u.getLast? = some false ∧ v.head? = some false then 1 else 0 := by
  induction u with
  | nil => simp [ssCount]
  | cons b u ih =>
    cases u with
    | nil =>
      cases v with
      | nil => simp [ssCount]
      | cons c v => cases b <;> cases c <;> simp [ssCount] <;> omega
    | cons c u =>
      simp only [List.cons_append,ssCount] at ih ⊢
      rw [ih]
      cases b <;> cases c <;> simp at ih ⊢ <;> omega

theorem ssCount_has_SS (u v : List Bool) : 1 ≤ ssCount (u ++ false::false::v) := by
  rw [ssCount_append]
  simp [ssCount]
  omega

/-- Two SS edges at distance 2 force a third: `SSSS` contains three SS.
Hence `ssCount = 2` cannot have SS-gap 2. -/
theorem ssCount_prefix_SSSS (w : List Bool) (h : 4 ≤ w.length)
    (h0 : w[0]'(by omega) = false) (h1 : w[1]'(by omega) = false)
    (h2 : w[2]'(by omega) = false) (h3 : w[3]'(by omega) = false) :
    3 ≤ ssCount w := by
  match w with
  | a :: b :: c :: d :: rest =>
    simp at h0 h1 h2 h3
    subst a; subst b; subst c; subst d
    simp [ssCount]
    omega
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h

theorem ss_gap_two_has_three (w : List Bool) (i : Nat)
    (hi : i + 3 < w.length)
    (h0 : w[i]'(by omega) = false) (h1 : w[i + 1]'(by omega) = false)
    (h2 : w[i + 2]'(by omega) = false) (h3 : w[i + 3]'(by omega) = false) :
    3 ≤ ssCount w := by
  have hdrop : 4 ≤ (w.drop i).length := by simp; omega
  have hd0 : (w.drop i)[0]'(by omega) = false := by
    simpa [List.getElem_drop] using h0
  have hd1 : (w.drop i)[1]'(by omega) = false := by
    simpa [List.getElem_drop] using h1
  have hd2 : (w.drop i)[2]'(by omega) = false := by
    simpa [List.getElem_drop] using h2
  have hd3 : (w.drop i)[3]'(by omega) = false := by
    simpa [List.getElem_drop] using h3
  have hpre := ssCount_prefix_SSSS (w.drop i) hdrop hd0 hd1 hd2 hd3
  have hsplit := (List.take_append_drop i w).symm
  have happ := ssCount_append (w.take i) (w.drop i)
  rw [← hsplit] at happ
  omega

theorem noSAAS_drop (w : List Bool) (i : Nat) (h : NoSAAS w) : NoSAAS (w.drop i) := by
  induction i generalizing w with
  | zero => simpa
  | succ i ih =>
    cases w with
    | nil => intro u v; cases u <;> simp
    | cons b w => exact ih w (noSAAS_tail b w h)

/-- Gap 4 is `SS ?? SS`. Interior `AA` is SAAS; an interior S adds a third SS. -/
theorem ssCount_prefix_gap_four (w : List Bool) (h : 6 ≤ w.length)
    (h0 : w[0]'(by omega) = false) (h1 : w[1]'(by omega) = false)
    (h4 : w[4]'(by omega) = false) (h5 : w[5]'(by omega) = false)
    (hno : NoSAAS w) : 3 ≤ ssCount w := by
  match w with
  | a :: b :: c :: d :: e :: f :: rest =>
    simp at h0 h1 h4 h5
    subst a; subst b; subst e; subst f
    cases c <;> cases d
    · simp [ssCount]; omega
    · simp [ssCount]; omega
    · simp [ssCount]; omega
    · exact False.elim (hno [false] (false :: rest) rfl)
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | [_, _, _, _] => simp at h
  | [_, _, _, _, _] => simp at h

theorem noSAAS_ss_gap_four (w : List Bool) (i : Nat)
    (hi : i + 5 < w.length)
    (h0 : w[i]'(by omega) = false) (h1 : w[i + 1]'(by omega) = false)
    (h4 : w[i + 4]'(by omega) = false) (h5 : w[i + 5]'(by omega) = false)
    (hno : NoSAAS w) : 3 ≤ ssCount w := by
  have hdrop : 6 ≤ (w.drop i).length := by simp; omega
  have hd0 : (w.drop i)[0]'(by omega) = false := by
    simpa [List.getElem_drop] using h0
  have hd1 : (w.drop i)[1]'(by omega) = false := by
    simpa [List.getElem_drop] using h1
  have hd4 : (w.drop i)[4]'(by omega) = false := by
    simpa [List.getElem_drop] using h4
  have hd5 : (w.drop i)[5]'(by omega) = false := by
    simpa [List.getElem_drop] using h5
  have hpre := ssCount_prefix_gap_four (w.drop i) hdrop hd0 hd1 hd4 hd5 (noSAAS_drop w i hno)
  have hsplit := (List.take_append_drop i w).symm
  have happ := ssCount_append (w.take i) (w.drop i)
  rw [← hsplit] at happ
  omega

/-- Under NoSAAS and `ssCount≤2`, an SS-gap of 6 is exactly `SSAAAA SS`. -/
theorem ssCount_prefix_gap_six (w : List Bool) (h : 8 ≤ w.length)
    (h0 : w[0]'(by omega) = false) (h1 : w[1]'(by omega) = false)
    (h6 : w[6]'(by omega) = false) (h7 : w[7]'(by omega) = false)
    (hss : ssCount w ≤ 2) (hno : NoSAAS w) :
    w[2]'(by omega) = true ∧ w[3]'(by omega) = true ∧
      w[4]'(by omega) = true ∧ w[5]'(by omega) = true := by
  match w with
  | a :: b :: c :: d :: e :: f :: g :: hrest :: rest =>
    simp at h0 h1 h6 h7
    subst a; subst b; subst g; subst hrest
    cases c
    · simp [ssCount] at hss; omega
    · cases f
      · simp [ssCount] at hss; omega
      · cases d
        · cases e
          · simp [ssCount] at hss; omega
          · exact False.elim (hno [false, false, true] (false :: rest) rfl)
        · cases e
          · exact False.elim (hno [false] (true :: false :: false :: rest) rfl)
          · simp
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | [_, _, _, _] => simp at h
  | [_, _, _, _, _] => simp at h
  | [_, _, _, _, _, _] => simp at h
  | [_, _, _, _, _, _, _] => simp at h

theorem noSAAS_ss_gap_six_form (w : List Bool) (i : Nat)
    (hi : i + 7 < w.length)
    (h0 : w[i]'(by omega) = false) (h1 : w[i + 1]'(by omega) = false)
    (h6 : w[i + 6]'(by omega) = false) (h7 : w[i + 7]'(by omega) = false)
    (hss : ssCount w = 2) (hno : NoSAAS w) :
    w[i + 2]'(by omega) = true ∧ w[i + 3]'(by omega) = true ∧
      w[i + 4]'(by omega) = true ∧ w[i + 5]'(by omega) = true := by
  have hdrop : 8 ≤ (w.drop i).length := by simp; omega
  have hd0 : (w.drop i)[0]'(by omega) = false := by
    simpa [List.getElem_drop] using h0
  have hd1 : (w.drop i)[1]'(by omega) = false := by
    simpa [List.getElem_drop] using h1
  have hd6 : (w.drop i)[6]'(by omega) = false := by
    simpa [List.getElem_drop] using h6
  have hd7 : (w.drop i)[7]'(by omega) = false := by
    simpa [List.getElem_drop] using h7
  have hssdrop : ssCount (w.drop i) ≤ 2 := by
    have happ := ssCount_append (w.take i) (w.drop i)
    have hsplit := (List.take_append_drop i w).symm
    rw [← hsplit] at happ
    omega
  have hform := ssCount_prefix_gap_six (w.drop i) hdrop hd0 hd1 hd6 hd7 hssdrop
    (noSAAS_drop w i hno)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [List.getElem_drop] using hform.1
  · simpa [List.getElem_drop] using hform.2.1
  · simpa [List.getElem_drop] using hform.2.2.1
  · simpa [List.getElem_drop] using hform.2.2.2

/-- An SS=2 word starting SSS has already spent both SS on the prefix,
so the tail is SS-free and cannot start with S. -/
theorem ss2_SSS_tail (rest : List Bool)
    (hss : ssCount (false :: false :: false :: rest) = 2) :
    ssCount rest = 0 ∧ rest.head? ≠ some false := by
  have hlist : false :: false :: false :: rest = [false, false, false] ++ rest := rfl
  rw [hlist, ssCount_append] at hss
  have hpre : ssCount [false, false, false] = 2 := by simp [ssCount]
  simp [hpre] at hss
  cases hrest : rest.head? with
  | none =>
    simp [hrest] at hss
    simp [hrest]
    omega
  | some b =>
    cases b
    · simp [hrest] at hss
      omega
    · simp [hrest] at hss
      exact ⟨by omega, by simp [hrest]⟩

theorem NoSS_of_ssCount_zero (w : List Bool) (h : ssCount w = 0) : NoSS w := by
  intro u v heq
  have : 1 ≤ ssCount w := by simpa [heq] using ssCount_has_SS u v
  omega

theorem mass_neg_one_form (w : List Bool) (h : NoSS w) (hm : mass w = -1) :
    ∃ n, w = alt false n ++ [false] := by
  match w with
  | [] => simp [mass] at hm
  | true :: t =>
    have ht := noSS_mass_lower t (noSS_tail true t h)
    simp [mass_cons,ShortPeriodicSupply.sign] at hm
    omega
  | false :: [] => exact ⟨0,rfl⟩
  | false :: false :: t => exact False.elim (h [] t rfl)
  | false :: true :: t =>
    have htss := noSS_tail true t (noSS_tail false (true::t) h)
    have hmt : mass t = -1 := by
      simp [mass_cons,ShortPeriodicSupply.sign] at hm
      omega
    obtain ⟨n,hn⟩ := mass_neg_one_form t htss hmt
    refine ⟨n+1,?_⟩
    simp [alt,hn]
termination_by w.length

theorem mass_SA_S (n : Nat) : mass (alt false n ++ [false]) = -1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp [alt,mass_cons,ShortPeriodicSupply.sign,ih]

theorem moment_SA_S (n : Nat) :
    moment (alt false n ++ [false]) = -((n : Int)+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp [alt,List.cons_append,moment,mass_cons,ShortPeriodicSupply.sign,mass_SA_S,ih]
    omega

theorem no_ss2_P2_in_A_started_tail (v x rest : List Bool)
    (hW : P2 (true::v)) (hssW : ssCount (true::v) = 2)
    (hv : v = x ++ rest) (hPx : P2 x) (hssx : ssCount x = 2) : False := by
  have hvss : ssCount v = 2 := by simpa [ssCount_cons_A] using hssW
  have happ := ssCount_append x rest
  have hvss' : ssCount (x ++ rest) = 2 := by simpa [hv] using hvss
  rw [hvss',hssx] at happ
  have hrestss : ssCount rest = 0 := by
    by_cases hj : x.getLast? = some false ∧ rest.head? = some false
    · simp [hj] at happ; omega
    · simp [hj] at happ; omega
  have hmassv : mass v = 0 := by
    simp [P2,mass_cons,ShortPeriodicSupply.sign] at hW
    omega
  have hmassr : mass rest = -1 := by
    have hm := mass_append x rest
    rw [hv,hm,hPx.1] at hmassv
    omega
  have hNo := NoSS_of_ssCount_zero rest hrestss
  obtain ⟨n,hn⟩ := mass_neg_one_form rest hNo hmassr
  have hMv : moment v = -1 := by
    simp [P2,moment,mass_cons,ShortPeriodicSupply.sign] at hW
    omega
  have hxlen : 1 ≤ x.length := by
    cases x with
    | nil => simp [P2,mass] at hPx
    | cons _ _ => simp
  have hcalc := moment_append x (alt false n ++ [false])
  rw [hPx.2,moment_SA_S n,mass_SA_S n] at hcalc
  have hv' : v = x ++ (alt false n ++ [false]) := by simpa [hn] using hv
  rw [hv',hcalc] at hMv
  omega

theorem no_ss2_P2_in_A_started_tail' (v : List Bool)
    (hW : P2 (true::v)) (hssW : ssCount (true::v) = 2) :
    ¬ ∃ x rest, v = x ++ rest ∧ P2 x ∧ ssCount x = 2 := by
  rintro ⟨x,rest,hv,hPx,hssx⟩
  exact no_ss2_P2_in_A_started_tail v x rest hW hssW hv hPx hssx

theorem ssCount_pre_A (k : Nat) (v : List Bool) :
    ssCount (List.replicate k true ++ v) = ssCount v := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [List.replicate_succ,ssCount_cons_A,ih]

/-- For a leading A-run of length at least 2, an SS=2 P2 prefix in the
tail would leave an SS-free remainder of mass at most -2, contradicting
`noSS_mass_lower`. -/
theorem no_ss2_P2_in_long_A_tail (k : Nat) (v x rest : List Bool)
    (hk : 2 ≤ k)
    (hW : P2 (List.replicate k true ++ v))
    (hssW : ssCount (List.replicate k true ++ v) = 2)
    (hv : v = x ++ rest) (hPx : P2 x) (hssx : ssCount x = 2) : False := by
  have hvss : ssCount v = 2 := by simpa [ssCount_pre_A] using hssW
  have happ := ssCount_append x rest
  have : ssCount (x ++ rest) = 2 := by simpa [hv] using hvss
  rw [this,hssx] at happ
  have hrestss : ssCount rest = 0 := by
    by_cases hj : x.getLast? = some false ∧ rest.head? = some false
    · simp [hj] at happ; omega
    · simp [hj] at happ; omega
  have hmassW : mass (List.replicate k true ++ v) = 1 := hW.1
  have hmassv : mass v = 1 - (k : Int) := by
    have hm := mass_append (List.replicate k true) v
    rw [hm,mass_replicate_A] at hmassW
    omega
  have hmassr : mass rest = - (k : Int) := by
    have hm := mass_append x rest
    rw [hv,hm,hPx.1] at hmassv
    omega
  have hNo := NoSS_of_ssCount_zero rest hrestss
  have hlo := noSS_mass_lower rest hNo
  have hkI : (2 : Int) ≤ k := by exact_mod_cast hk
  omega

theorem consecutive_not_both_ss2_nested (e : Int → Bool) (t : Int)
    (d f : Nat) (hf : 1 ≤ f) (hA : e t = true)
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t+1) f)
    (hssold : ssCount (past e t d) = 2)
    (hssnew : ssCount (past e (t+1) f) = 2)
    (hnest : d + 1 ≤ f) : False := by
  have hsplit := past_append e (t+1) 1 (f-1)
  have hd1 : 1+(f-1)=f := by omega
  have htime : (t+1 : Int) - (1 : Nat) = t := by omega
  have hw : past e (t+1) f = past e (t+1) 1 ++ past e t (f-1) := by
    simpa [hd1,htime] using hsplit
  have h1 : past e (t+1) 1 = [true] := by
    simp [past]
    exact hA
  have hword : past e (t+1) f = true :: past e t (f-1) := by
    simpa [h1] using hw
  have hPn : P2 (true :: past e t (f-1)) := by
    have := (past_p2_iff e (t+1) f).mpr hnew
    simpa [hword] using this
  have hssn : ssCount (true :: past e t (f-1)) = 2 := by
    simpa [hword] using hssnew
  have hdrop : past e t (f-1) =
      past e t d ++ past e (t - (d : Int)) (f-1-d) := by
    have hsplit' := past_append e t d (f-1-d)
    have : d+(f-1-d)=f-1 := by omega
    simpa [this] using hsplit'
  have hPold : P2 (past e t d) := (past_p2_iff e t d).mpr hold
  exact no_ss2_P2_in_A_started_tail (past e t (f-1)) (past e t d)
    (past e (t-(d : Int)) (f-1-d)) hPn hssn hdrop hPold hssold

/-- Distance 2 in an A-run cannot be two min SS=2 sources: the later
window would start AAS if the earlier source were the run start, and
`stream_min_not_prefix_AAS` forbids that. Hence the run continues
strictly before the earlier source. -/
theorem gap_two_requires_earlier_A (e : Int → Bool) (t : Int) (d : Nat)
    (hA : e t = true) (hA1 : e (t+1) = true) (hA2 : e (t+2) = true)
    (_hP : ShortPeriodicSupply.P2 e (t+2) d)
    (hmin : ∀ f : Nat, f < d → ¬ ShortPeriodicSupply.P2 e (t+2) f)
    (hlen : 3 < d) :
    e (t-1) = true := by
  by_cases hS : e (t-1) = false
  · have hAAS : past e (t+2) 3 = [true,true,false] :=
      (isolated_start_clean_sibling e t hS hA hA1 hA2).2.1
    exact False.elim (stream_min_not_prefix_AAS e (t+2) d hmin hlen hAAS)
  · cases h : e (t-1) <;> simp_all

end Recaman.OnePerRun
