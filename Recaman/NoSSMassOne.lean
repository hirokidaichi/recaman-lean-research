import Recaman.OnePerRun

namespace Recaman.NoSSMassOne

set_option linter.unusedSimpArgs false

open LeadingRunSupply SSFreeSupply OnePerRun OneSSMultiplicity TwoSSLeadingSibling

/-! SS-free mass-1 words have odd length. The word `AA (SA)^r S` has
mass 1, no SS, length `2r+3`, and moment `-r`. This is the candidate
sharp lower bound for the long-earlier one-per-run remainder. -/

theorem p2_length_mod_four (w : List Bool) (h : P2 w) : w.length % 4 = 3 := by
  have hc := p2_count_identities w h
  have hb := ones_bounds w
  have hlen : (w.length : Int) = 2 * ones w - 1 := hc.1
  have he : ones w % 2 = 0 := hc.2.2
  have hnn : 0 ≤ ones w := hb.1
  omega

theorem alt_false_length (n : Nat) : (alt false n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [alt,ih]; omega

theorem alt_false_ssCount (n : Nat) : ssCount (alt false n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [alt,ssCount,ih]

def minWord (r : Nat) : List Bool :=
  true :: true :: (alt false r ++ [false])

theorem minWord_length (r : Nat) : (minWord r).length = 2 * r + 3 := by
  simp [minWord,alt_false_length]

theorem minWord_mass (r : Nat) : mass (minWord r) = 1 := by
  simp [minWord,mass_cons,ShortPeriodicSupply.sign,mass_SA_S]

theorem alt_false_last (n : Nat) :
    (alt false n).getLast? = if n = 0 then none else some true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => simp [alt]
    | succ n =>
      simp [alt] at ih ⊢
      simpa using ih

theorem minWord_ssCount (r : Nat) : ssCount (minWord r) = 0 := by
  induction r with
  | zero => decide
  | succ r ih =>
    simp [minWord,alt,ssCount_cons_A] at ih ⊢
    simp [ssCount]
    simpa [minWord,ssCount_cons_A] using ih

theorem minWord_NoSS (r : Nat) : NoSS (minWord r) :=
  NoSS_of_ssCount_zero _ (minWord_ssCount r)

theorem minWord_moment (r : Nat) : moment (minWord r) = - (r : Int) := by
  have h := moment_append [true,true] (alt false r ++ [false])
  have hAA : moment [true,true] = 3 := by decide
  have hlen : ([true,true] : List Bool).length = 2 := rfl
  simp [minWord] 
  rw [show true :: true :: (alt false r ++ [false]) = [true,true] ++ (alt false r ++ [false]) by rfl]
  rw [h,hAA,moment_SA_S,mass_SA_S,hlen]
  omega

theorem mass_one_length_odd (w : List Bool) (hm : mass w = 1) :
    ∃ r, w.length = 2 * r + 1 := by
  have hmass := mass_eq w
  rw [hm] at hmass
  have hones := ones_bounds w
  refine ⟨(w.length - 1) / 2, ?_⟩
  omega

/-- Sharp: `2 * moment + length ≥ 3`, equality on `minWord`. -/
theorem noss_mass_one_moment_bound (w : List Bool) (hss : NoSS w)
    (hm : mass w = 1) : 3 ≤ 2 * moment w + w.length := by
  match w with
  | [] => simp [mass] at hm
  | [true] => decide
  | [false] => simp [mass_cons,ShortPeriodicSupply.sign] at hm
  | true :: true :: rest =>
    have ht := noSS_tail true rest (noSS_tail true (true::rest) hss)
    have hmr : mass rest = -1 := by
      simp [mass_cons,ShortPeriodicSupply.sign] at hm
      omega
    obtain ⟨n,hn⟩ := mass_neg_one_form rest ht hmr
    have hw : true :: true :: rest = minWord n := by
      simp [minWord,hn]
    rw [hw,minWord_moment,minWord_length]
    omega
  | true :: false :: rest =>
    have ht := noSS_tail false rest (noSS_tail true (false::rest) hss)
    have hmr : mass rest = 1 := by
      simp [mass_cons,ShortPeriodicSupply.sign] at hm
      omega
    have ih := noss_mass_one_moment_bound rest ht hmr
    simp [moment,mass_cons,ShortPeriodicSupply.sign] at hm ih ⊢
    omega
  | false :: false :: rest => exact False.elim (hss [] rest rfl)
  | false :: true :: rest =>
    have ht := noSS_tail true rest (noSS_tail false (true::rest) hss)
    have hmr : mass rest = 1 := by
      simp [mass_cons,ShortPeriodicSupply.sign] at hm
      omega
    have ih := noss_mass_one_moment_bound rest ht hmr
    simp [moment,mass_cons,ShortPeriodicSupply.sign] at hm ih ⊢
    omega
termination_by w.length

theorem minWord_sharp (r : Nat) :
    2 * moment (minWord r) + (minWord r).length = 3 := by
  rw [minWord_moment,minWord_length]
  omega

/-- If extra is SS-free of mass 1 and moment `1-|v|`, it cannot be
shorter than `2|v|`. Later SS=2 has |v|≥10, so extra length ≥21 and
the earlier lag is at least `3f-2`. -/
theorem case5_remainder_too_negative (v extra : List Bool)
    (hNo : NoSS extra) (hm : mass extra = 1)
    (hM : moment extra = 1 - (v.length : Int))
    (hle : extra.length + 1 ≤ 2 * v.length) : False := by
  have hb := noss_mass_one_moment_bound extra hNo hm
  have : 2 * moment extra + extra.length ≤ 1 := by
    have hL : (extra.length : Int) + 1 ≤ 2 * v.length := by exact_mod_cast hle
    omega
  omega

/-- Word-level long-earlier obstruction. If the later window is `A++v` and
the earlier window is `v++extra`, both P2 with SS=2, then extra cannot be
an SS-free mass-1 remainder shorter than `2|v|`. -/
theorem nested_reverse_short_impossible (v extra : List Bool)
    (hnew : P2 (true::v)) (hssnew : ssCount (true::v) = 2)
    (hold : P2 (v ++ extra)) (hssold : ssCount (v ++ extra) = 2)
    (hle : extra.length + 1 ≤ 2 * v.length) : False := by
  have hvss : ssCount v = 2 := by simpa [ssCount_cons_A] using hssnew
  have happ := ssCount_append v extra
  rw [hssold,hvss] at happ
  have hrestss : ssCount extra = 0 := by
    by_cases hj : v.getLast? = some false ∧ extra.head? = some false
    · simp [hj] at happ; omega
    · simp [hj] at happ; omega
  have hmassv : mass v = 0 := by
    simp [P2,mass_cons,ShortPeriodicSupply.sign] at hnew
    omega
  have hmassr : mass extra = 1 := by
    have hm := mass_append v extra
    have := hold.1
    rw [hm,hmassv] at this
    omega
  have hMv : moment v = -1 := by
    simp [P2,moment,mass_cons,ShortPeriodicSupply.sign] at hnew
    omega
  have hMe : moment extra = 1 - (v.length : Int) := by
    have hma := moment_append v extra
    have := hold.2
    rw [hma,hMv,hmassr] at this
    omega
  exact case5_remainder_too_negative v extra
    (NoSS_of_ssCount_zero extra hrestss) hmassr hMe hle

/-- NoSS mass-1 words are `[A]`, `minWord r`, or those with an `AS`/`SA`
prefix. `AS` is allowed only in front of an A-started word, otherwise
the join is SS. This is the exact recursion of `noss_mass_one_moment_bound`. -/
inductive MassOneNoSS : List Bool → Prop where
  | unit : MassOneNoSS [true]
  | min (r : Nat) : MassOneNoSS (minWord r)
  | prefixAS (w : List Bool) : MassOneNoSS w → w.head? ≠ some false →
      MassOneNoSS (true :: false :: w)
  | prefixSA (w : List Bool) : MassOneNoSS w →
      MassOneNoSS (false :: true :: w)

theorem massOneNoSS_mass {w : List Bool} (h : MassOneNoSS w) : mass w = 1 := by
  induction h with
  | unit => decide
  | min r => exact minWord_mass r
  | prefixAS w hw hhead ih =>
    simp [mass_cons, ShortPeriodicSupply.sign, ih]
  | prefixSA w hw ih =>
    simp [mass_cons, ShortPeriodicSupply.sign, ih]

theorem massOneNoSS_ssCount {w : List Bool} (h : MassOneNoSS w) : ssCount w = 0 := by
  induction h with
  | unit => decide
  | min r => exact minWord_ssCount r
  | prefixAS w hw hhead ih =>
    cases w with
    | nil => simp [ssCount]
    | cons b rest =>
      have hb : b = true := by
        cases b
        · have : (false :: rest).head? = some false := rfl
          exact False.elim (hhead this)
        · rfl
      rw [hb] at ih
      simpa [ssCount, hb] using (ssCount_cons_A rest ▸ ih)
  | prefixSA w hw ih =>
    cases w with
    | nil => simp [ssCount]
    | cons b rest =>
      simp [ssCount] at ih ⊢
      cases b <;> simp [ssCount] at ih ⊢
      · omega
      · simpa using (ssCount_cons_A rest ▸ ih)

theorem massOneNoSS_NoSS {w : List Bool} (h : MassOneNoSS w) : NoSS w :=
  NoSS_of_ssCount_zero w (massOneNoSS_ssCount h)

theorem prefixAS_moment (w : List Bool) (hm : mass w = 1) :
    moment (true :: false :: w) = moment w + 1 := by
  simp [moment, mass_cons, ShortPeriodicSupply.sign, hm]
  omega

theorem prefixSA_moment (w : List Bool) (hm : mass w = 1) :
    moment (false :: true :: w) = moment w + 3 := by
  simp [moment, mass_cons, ShortPeriodicSupply.sign, hm]
  omega

/-- Slack of any NoSS mass-1 word is `3 + 8k + 4a` for the number of
`SA` and `AS` prefixes over an atom `[A]` or `minWord`. -/
theorem massOneNoSS_slack {w : List Bool} (h : MassOneNoSS w) :
    ∃ a k : Nat, 2 * moment w + w.length = 3 + 8 * k + 4 * a := by
  induction h with
  | unit => exact ⟨0, 0, by decide⟩
  | min r =>
    refine ⟨0, 0, ?_⟩
    have h3 := minWord_sharp r
    simp [h3]
  | prefixAS w hw hhead ih =>
    obtain ⟨a, k, hs⟩ := ih
    refine ⟨a + 1, k, ?_⟩
    have hm := massOneNoSS_mass hw
    have hlen : (true :: false :: w).length = w.length + 2 := by simp
    rw [prefixAS_moment w hm, hlen]
    omega
  | prefixSA w hw ih =>
    obtain ⟨a, k, hs⟩ := ih
    refine ⟨a, k + 1, ?_⟩
    have hm := massOneNoSS_mass hw
    have hlen : (false :: true :: w).length = w.length + 2 := by simp
    rw [prefixSA_moment w hm, hlen]
    omega

theorem noss_mass_one_classify (w : List Bool) (hss : NoSS w) (hm : mass w = 1) :
    MassOneNoSS w := by
  match w with
  | [] => simp [mass] at hm
  | [true] => exact MassOneNoSS.unit
  | [false] => simp [mass_cons, ShortPeriodicSupply.sign] at hm
  | true :: true :: rest =>
    have ht := noSS_tail true rest (noSS_tail true (true :: rest) hss)
    have hmr : mass rest = -1 := by
      simp [mass_cons, ShortPeriodicSupply.sign] at hm
      omega
    obtain ⟨n, hn⟩ := mass_neg_one_form rest ht hmr
    have hw : true :: true :: rest = minWord n := by simp [minWord, hn]
    rw [hw]
    exact MassOneNoSS.min n
  | true :: false :: rest =>
    have ht := noSS_tail false rest (noSS_tail true (false :: rest) hss)
    have hmr : mass rest = 1 := by
      simp [mass_cons, ShortPeriodicSupply.sign] at hm
      omega
    have ih := noss_mass_one_classify rest ht hmr
    have hhead : rest.head? ≠ some false := by
      intro hr
      cases rest with
      | nil => simp at hr
      | cons b rest =>
        simp at hr
        cases b <;> simp at hr
        exact hss [true] rest rfl
    exact MassOneNoSS.prefixAS rest ih hhead
  | false :: false :: rest => exact False.elim (hss [] rest rfl)
  | false :: true :: rest =>
    have ht := noSS_tail true rest (noSS_tail false (true :: rest) hss)
    have hmr : mass rest = 1 := by
      simp [mass_cons, ShortPeriodicSupply.sign] at hm
      omega
    exact MassOneNoSS.prefixSA rest (noss_mass_one_classify rest ht hmr)
termination_by w.length

/-- The SA-prefixed minWord family used by every canonical SS=3 reverse-nested extra. -/
theorem sa_prefixed_minWord (k r : Nat) :
    MassOneNoSS (alt false k ++ minWord r) := by
  induction k with
  | zero => simpa [alt] using MassOneNoSS.min r
  | succ k ih =>
    simpa [alt] using MassOneNoSS.prefixSA (alt false k ++ minWord r) ih

theorem sa_prefixed_minWord_moment (k r : Nat) :
    moment (alt false k ++ minWord r) = (3 * k : Int) - r := by
  rw [moment_append, alt_S_moment, minWord_moment, minWord_mass, alt_false_length]
  omega

theorem sa_prefixed_minWord_ssCount (k r : Nat) :
    ssCount (alt false k ++ minWord r) = 0 := by
  simpa [minWord_ssCount] using ssCount_pre_alt k (minWord r)

theorem sa_prefixed_minWord_slack (k r : Nat) :
    2 * moment (alt false k ++ minWord r) +
      (alt false k ++ minWord r).length = 3 + 8 * k := by
  rw [sa_prefixed_minWord_moment, List.length_append, alt_false_length,
    minWord_length]
  omega

/-- Consecutive reverse-nested P2 windows, with no SS hypothesis.
The extra remainder always has mass 1 and moment `1-|v|`. -/
theorem consecutive_reverse_extra_mass_moment (e : Int → Bool) (t : Int)
    (d f : Nat) (hA : e t = true) (hf : 1 ≤ f) (hle_d : f ≤ d)
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t + 1) f) :
    mass (past e t (f - 1)) = 0 ∧
      moment (past e t (f - 1)) = -1 ∧
      mass (past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1))) = 1 ∧
      moment (past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1))) =
        1 - ((f - 1 : Nat) : Int) := by
  have hsplit := past_append e (t + 1) 1 (f - 1)
  have hd1 : 1 + (f - 1) = f := by omega
  have htime : (t + 1 : Int) - (1 : Nat) = t := by omega
  have hw : past e (t + 1) f = past e (t + 1) 1 ++ past e t (f - 1) := by
    simpa [hd1, htime] using hsplit
  have h1 : past e (t + 1) 1 = [true] := by
    simp [past]; exact hA
  have hword : past e (t + 1) f = true :: past e t (f - 1) := by
    simpa [h1] using hw
  have hPn : P2 (true :: past e t (f - 1)) := by
    have := (past_p2_iff e (t + 1) f).mpr hnew
    simpa [hword] using this
  have hdrop : past e t d =
      past e t (f - 1) ++ past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1)) := by
    have hs := past_append e t (f - 1) (d - (f - 1))
    have : (f - 1) + (d - (f - 1)) = d := by omega
    simpa [this] using hs
  have hPold : P2 (past e t d) := (past_p2_iff e t d).mpr hold
  have hold' : P2 (past e t (f - 1) ++
      past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1))) := by
    simpa [hdrop] using hPold
  have hmassv : mass (past e t (f - 1)) = 0 := by
    simp [P2, mass_cons, ShortPeriodicSupply.sign] at hPn
    omega
  have hMv : moment (past e t (f - 1)) = -1 := by
    simp [P2, moment, ShortPeriodicSupply.sign] at hPn
    omega
  have hmasse : mass (past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1))) = 1 := by
    have hm := mass_append (past e t (f - 1))
      (past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1)))
    have := hold'.1
    rw [hm, hmassv] at this
    omega
  have hMe : moment (past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1))) =
      1 - ((f - 1 : Nat) : Int) := by
    have hma := moment_append (past e t (f - 1))
      (past e (t - ((f - 1 : Nat) : Int)) (d - (f - 1)))
    have := hold'.2
    have hlen : (past e t (f - 1)).length = f - 1 := past_length e t (f - 1)
    rw [hma, hMv, hmasse, hlen] at this
    omega
  exact ⟨hmassv, hMv, hmasse, hMe⟩

theorem consecutive_reverse_short_impossible (e : Int → Bool) (t : Int)
    (d f : Nat) (hA : e t = true) (hf : 1 ≤ f) (hle_d : f ≤ d)
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t+1) f)
    (hssold : ssCount (past e t d) = 2)
    (hssnew : ssCount (past e (t+1) f) = 2)
    (hshort : d - (f - 1) + 1 ≤ 2 * (f - 1)) : False := by
  have hsplit := past_append e (t+1) 1 (f-1)
  have hd1 : 1+(f-1)=f := by omega
  have htime : (t+1 : Int) - (1 : Nat) = t := by omega
  have hw : past e (t+1) f = past e (t+1) 1 ++ past e t (f-1) := by
    simpa [hd1,htime] using hsplit
  have h1 : past e (t+1) 1 = [true] := by
    simp [past]; exact hA
  have hword : past e (t+1) f = true :: past e t (f-1) := by
    simpa [h1] using hw
  have hPn : P2 (true :: past e t (f-1)) := by
    have := (past_p2_iff e (t+1) f).mpr hnew
    simpa [hword] using this
  have hssn : ssCount (true :: past e t (f-1)) = 2 := by
    simpa [hword] using hssnew
  have hdrop : past e t d =
      past e t (f-1) ++ past e (t - ((f-1 : Nat) : Int)) (d - (f-1)) := by
    have hs := past_append e t (f-1) (d-(f-1))
    have : (f-1)+(d-(f-1))=d := by omega
    simpa [this] using hs
  have hPold : P2 (past e t d) := (past_p2_iff e t d).mpr hold
  have hold' : P2 (past e t (f-1) ++
      past e (t - ((f-1 : Nat) : Int)) (d - (f-1))) := by
    simpa [hdrop] using hPold
  have hssold' : ssCount (past e t (f-1) ++
      past e (t - ((f-1 : Nat) : Int)) (d - (f-1))) = 2 := by
    simpa [hdrop] using hssold
  have hlen : (past e t (f-1)).length = f-1 := past_length e t (f-1)
  have hextra : (past e (t - ((f-1 : Nat) : Int)) (d - (f-1))).length =
      d - (f-1) := past_length _ _ _
  have hle : (past e (t - ((f-1 : Nat) : Int)) (d - (f-1))).length + 1 ≤
      2 * (past e t (f-1)).length := by
    simpa [hlen,hextra] using hshort
  exact nested_reverse_short_impossible (past e t (f-1))
    (past e (t - ((f-1 : Nat) : Int)) (d - (f-1)))
    hPn hssn hold' hssold' hle

end Recaman.NoSSMassOne




