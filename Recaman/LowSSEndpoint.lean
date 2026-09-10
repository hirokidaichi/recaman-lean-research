import Recaman.OneSSMultiplicity

namespace Recaman.LowSSEndpoint

open LeadingRunSupply OneSSMultiplicity

/-! A common-endpoint obstruction. The current-A and SS-count hypotheses
are explicit; no minimum-lag, NoSAAS, or actual-orbit hypothesis is used. -/

theorem ssCount_tail_le (b : Bool) (w : List Bool) :
    ssCount w ≤ ssCount (b::w) := by
  simp only [ssCount]
  split <;> omega

theorem ssCount_append_left_le (u v : List Bool) :
    ssCount u ≤ ssCount (u++v) := by
  induction u with
  | nil => simp [ssCount]
  | cons b u ih =>
    cases u with
    | nil => simp [ssCount]
    | cons c u =>
      cases b <;> cases c <;> simp [ssCount] at ih ⊢ <;> omega

/-- Pair an S with the following A. Only adjacent SS edges can leave an
unpaid S when the final sign is A. -/
theorem mass_ending_A (w : List Bool) :
    -(ssCount (w++[true]) : Int) ≤ mass (w++[true]) := by
  cases w with
  | nil => decide
  | cons b w =>
    cases b with
    | true =>
      have ih := mass_ending_A w
      simp [ssCount,mass_cons,ShortPeriodicSupply.sign]
      omega
    | false =>
      cases w with
      | nil => decide
      | cons b w =>
        cases b with
        | false =>
          have ih := mass_ending_A (false::w)
          simp [ssCount,mass_cons,ShortPeriodicSupply.sign] at ih ⊢
          omega
        | true =>
          have ih := mass_ending_A w
          simp [ssCount,mass_cons,ShortPeriodicSupply.sign]
          omega
termination_by w.length

/-- Each suffix has mass at least -1 and the final A contributes +1.
The two-unit strict margin is what prevents a P2 endpoint collision. -/
theorem moment_ending_A (w : List Bool) (hss : ssCount (w++[true]) ≤ 1) :
    2 ≤ moment (w++[true])+(w++[true]).length := by
  induction w with
  | nil => decide
  | cons b w ih =>
    have hs := ssCount_tail_le b (w++[true])
    have hi := ih (by simpa using Nat.le_trans hs hss)
    have hm := mass_ending_A (b::w)
    have hl : -1 ≤ mass ((b::w)++[true]) := by omega
    simp only [List.cons_append,moment,List.length_cons,Int.natCast_add,
      Int.cast_ofNat_Int] at hi ⊢
    rw [List.cons_append,mass_cons] at hl
    omega

theorem ssCount_post_A (w : List Bool) : ssCount (w++[true])=ssCount w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases w with
    | nil => cases b <;> decide
    | cons c w => cases b <;> cases c <;> simp [ssCount] at ih ⊢ <;> omega

theorem ssCount_post_SS (w : List Bool) :
    ssCount (w++[false,false])=ssCount (w++[false])+1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases w with
    | nil => cases b <;> decide
    | cons c w => cases b <;> cases c <;> simp [ssCount] at ih ⊢ <;> omega

theorem moment_ending_AA (w : List Bool) (hss : ssCount (w++[true,true])≤1) :
    3 ≤ moment (w++[true,true]) := by
  have hs := ssCount_append_left_le (w++[true]) [true]
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hs
  have hM := moment_ending_A w (by omega)
  have heq : w++[true,true]=(w++[true])++[true] := by simp
  rw [heq,moment_append]
  simp only [moment,mass_cons,mass_nil,ShortPeriodicSupply.sign,↓reduceIte]
  omega

/-- With no SS, a nonpositive moment at mass one must already have
passed a zero-moment prefix ending S. The induction removes final pairs. -/
theorem zero_SS_nonpositive_prefix (w : List Bool) (hm : mass w=1)
    (hM : moment w≤0) (hss : ssCount w=0) :
    ∃ u v : List Bool, w=(u++[false])++v ∧ P2 (u++[false]) := by
  rcases List.eq_nil_or_concat w with hw | ⟨x,c,hw⟩
  · simp [hw] at hm
  · simp only [List.concat_eq_append] at hw
    rcases List.eq_nil_or_concat x with hx | ⟨u,b,hx⟩
    · subst x
      cases c <;> simp [hw,moment,mass_cons,ShortPeriodicSupply.sign] at hm hM
    · simp only [List.concat_eq_append] at hx
      have hword : w=u++[b,c] := by simp [hw,hx,List.append_assoc]
      have hs := ssCount_append_left_le u [b,c]
      have hsu : ssCount u=0 := by rw [← hword] at hs; omega
      cases b <;> cases c
      · have hc := ssCount_post_SS u
        rw [← hword] at hc
        omega
      · have hmu : mass u=1 := by simpa [hword,mass_append,ShortPeriodicSupply.sign] using hm
        have hMu : moment u≤0 := by
          simp [hword,moment_append,moment,mass_cons,ShortPeriodicSupply.sign] at hM
          omega
        obtain ⟨a,v,hu,hP⟩ := zero_SS_nonpositive_prefix u hmu hMu hsu
        exact ⟨a,v++[false,true],by simp [hword,hu,List.append_assoc],hP⟩
      · by_cases hzero : moment w=0
        · exact ⟨u++[true],[],by simpa [List.append_assoc] using hword,
            by simpa [P2,hword,List.append_assoc] using And.intro hm hzero⟩
        · have hmu : mass u=1 := by simpa [hword,mass_append,ShortPeriodicSupply.sign] using hm
          have hMu : moment u≤0 := by
            have hh : moment w<0 := by omega
            simp [hword,moment_append,moment,mass_cons,ShortPeriodicSupply.sign] at hh
            omega
          obtain ⟨a,v,hu,hP⟩ := zero_SS_nonpositive_prefix u hmu hMu hsu
          exact ⟨a,v++[true,false],by simp [hword,hu,List.append_assoc],hP⟩
      · have hc := moment_ending_AA u (by rw [← hword,hss]; omega)
        rw [← hword] at hc
        omega
termination_by w.length
decreasing_by all_goals simp [hword]

/-- A nonpositive mass-one word ending A already has an S-ended P2
prefix. The only new boundary case consumes the unique SS and reduces
to the zero-SS lemma. No forbidden-subword classification is needed. -/
theorem lowSS_A_nonpositive_prefix (w : List Bool)
    (hm : mass (w++[true])=1) (hM : moment (w++[true])≤0)
    (hss : ssCount (w++[true])≤1) :
    ∃ u v : List Bool, w++[true]=(u++[false])++v ∧ P2 (u++[false]) := by
  rcases List.eq_nil_or_concat w with hw | ⟨x,b,hw⟩
  · simp [hw,moment,ShortPeriodicSupply.sign] at hM
  · simp only [List.concat_eq_append] at hw
    cases b with
    | true =>
      have hc := moment_ending_AA x (by simpa [hw,List.append_assoc] using hss)
      simp only [hw,List.append_assoc,List.cons_append,List.nil_append] at hM
      omega
    | false =>
      have hword : w++[true]=x++[false,true] := by simp [hw,List.append_assoc]
      have hmx : mass x=1 := by simpa [hword,mass_append,ShortPeriodicSupply.sign] using hm
      have hMx : moment x≤0 := by
        simp [hword,moment_append,moment,mass_cons,ShortPeriodicSupply.sign] at hM
        omega
      have hs := ssCount_append_left_le x [false,true]
      have hsx : ssCount x≤1 := by rw [← hword] at hs; omega
      have hfound : ∃ u v : List Bool, x=(u++[false])++v ∧ P2 (u++[false]) := by
        rcases List.eq_nil_or_concat x with hx | ⟨y,c,hx⟩
        · simp [hx] at hmx
        · simp only [List.concat_eq_append] at hx
          cases c with
          | true =>
            simpa only [hx] using lowSS_A_nonpositive_prefix y (hx ▸ hmx) (hx ▸ hMx) (hx ▸ hsx)
          | false =>
            have hc := ssCount_post_SS y
            have he : ssCount (w++[true])=ssCount (y++[false,false]) := by
              rw [ssCount_post_A,hw,hx]
              simp [List.append_assoc]
            have hzero : ssCount x=0 := by rw [he] at hss; rw [hx]; omega
            exact zero_SS_nonpositive_prefix x hmx hMx hzero
      obtain ⟨u,v,hx,hP⟩ := hfound
      exact ⟨u,v++[false,true],by simp [hword,hx,List.append_assoc],hP⟩
termination_by w.length
decreasing_by all_goals simp [hw,hx]

/-- Every low-SS P2 witness can be shortened to one ending S. This
derives the endpoint condition, even without NoSAAS or minimality. -/
theorem lowSS_S_prefix (w : List Bool) (hP : P2 w) (hss : ssCount w≤1) :
    ∃ u v : List Bool, w=(u++[false])++v ∧ P2 (u++[false]) := by
  rcases List.eq_nil_or_concat w with hw | ⟨u,b,hw⟩
  · simp [P2,hw] at hP
  · simp only [List.concat_eq_append] at hw
    cases b with
    | false => exact ⟨u,[],by simpa using hw,hw ▸ hP⟩
    | true =>
      have h := lowSS_A_nonpositive_prefix u (hw ▸ hP.1) (by rw [← hw,hP.2]; omega) (hw ▸ hss)
      simpa only [← hw] using h

theorem take_past (e : Int → Bool) (t : Int) (d f : Nat) (hf : f≤d) :
    (past e t d).take f=past e t f := by
  simp [past,← List.map_take,List.take_range,Nat.min_eq_left hf]

/-- Shortening is performed inside the same actual backward history.
The output supplies the S endpoint needed by the periodic injection. -/
theorem stream_S_witness (e : Int → Bool) (t : Int) (d : Nat)
    (hP : ShortPeriodicSupply.P2 e t d) (hss : ssCount (past e t d)≤1) :
    ∃ f : Nat, 0<f ∧ f≤d ∧ ShortPeriodicSupply.P2 e t f ∧
      ssCount (past e t f)≤1 ∧ e (t-f)=false := by
  obtain ⟨u,v,hw,hshort⟩ := lowSS_S_prefix (past e t d) ((past_p2_iff e t d).mpr hP) hss
  let f := (u++[false]).length
  have hflen : f=u.length+1 := by simp [f]
  have hf : f≤d := by
    have hlen := congrArg List.length hw
    simp only [List.length_append,List.length_cons,List.length_nil] at hlen
    simp only [past,List.length_map,List.length_range] at hlen
    omega
  have hpre : past e t f=u++[false] := by
    rw [← take_past e t d f hf,hw]
    exact List.take_left
  have hS : e (t-f)=false := by
    have hget := congrArg (fun w : List Bool => w[u.length]?) hpre
    simp [past,hflen] at hget
    simpa [hflen] using hget
  have hs := ssCount_append_left_le (u++[false]) v
  rw [← hw] at hs
  refine ⟨f,by omega,hf,(past_p2_iff e t f).mp ?_,?_,hS⟩
  · simpa [hpre] using hshort
  · rw [hpre]
    omega

theorem noSS_count_zero (w : List Bool) (h : SSFreeSupply.NoSS w) : ssCount w=0 := by
  cases w with
  | nil => rfl
  | cons b w =>
    have ih := noSS_count_zero w (SSFreeSupply.noSS_tail b w h)
    cases w with
    | nil => cases b <;> rfl
    | cons c w =>
      cases b <;> cases c
      · exact False.elim (h [] w rfl)
      all_goals simpa [ssCount] using ih

theorem minimum_endpoint_S (e : Int → Bool) (t : Int) (d : Nat)
    (hP : ShortPeriodicSupply.P2 e t d) (hss : ssCount (past e t d)≤1)
    (hmin : ∀ f : Nat, f<d → ¬ ShortPeriodicSupply.P2 e t f) : e (t-d)=false := by
  obtain ⟨f,_,hfd,hfP,_,hfS⟩ := stream_S_witness e t d hP hss
  have heq : f=d := by
    by_cases heq : f=d
    · exact heq
    · exact False.elim (hmin f (by omega) hfP)
  simpa [heq] using hfS

/-- Two P2 windows cannot have the same old endpoint when the intervening
nonempty word ends at the older current A and has at most one SS. -/
theorem no_shared_endpoint (v u : List Bool)
    (hss : ssCount ((v++[true])++u) ≤ 1)
    (hnew : P2 ((v++[true])++u)) (hold : P2 u) : False := by
  have hs := ssCount_append_left_le (v++[true]) u
  have hM := moment_ending_A v (by omega)
  have heq := moment_append (v++[true]) u
  rw [hnew.2,hold.2,hold.1] at heq
  omega

theorem stream_no_delayed_endpoint (e : Int → Bool) (t : Int) (k d : Nat)
    (hk : 0 < k) (hA : e t = true)
    (hss : ssCount (past e (t+k) (k+d)) ≤ 1)
    (hnew : P2 (past e (t+k) (k+d))) (hold : P2 (past e t d)) : False := by
  have hklen : k=(k-1)+1 := by omega
  have hlast : past e (t+k-(k-1 : Nat)) 1=[true] := by
    have htime : t+(k : Int)-((k-1 : Nat) : Int)-1=t := by omega
    simpa [past,htime] using congrArg (fun b => [b]) hA
  have hfirst : past e (t+k) k=past e (t+k) (k-1)++[true] := by
    calc
      past e (t+k) k = past e (t+k) ((k-1)+1) := congrArg (past e (t+k)) hklen
      _ = past e (t+k) (k-1)++past e (t+k-(k-1 : Nat)) 1 := past_append _ _ _ _
      _ = past e (t+k) (k-1)++[true] := by rw [hlast]
  have htime : t+(k : Int)-k=t := by omega
  rw [past_append,hfirst,htime] at hss hnew
  exact no_shared_endpoint _ _ hss hnew hold

/-- The actual P2 windows, not classified proxy words, have distinct
integer endpoints. Either direction uses the later window's SS bound. -/
theorem endpoint_injective (e : Int → Bool) (t u : Int) (d f : Nat)
    (htA : e t=true) (huA : e u=true)
    (htss : ssCount (past e t d)≤1) (huss : ssCount (past e u f)≤1)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u f)
    (heq : t-d=u-f) : t=u := by
  have ht := (past_p2_iff e t d).mpr htP
  have hu := (past_p2_iff e u f).mpr huP
  by_cases htu : t=u
  · exact htu
  · by_cases hlt : t<u
    · let k := (u-t).toNat
      have hk : (k : Int)=u-t := Int.toNat_of_nonneg (by omega)
      have hkpos : 0<k := by omega
      have htime : t+(k : Int)=u := by omega
      have hlen : k+d=f := by omega
      have hf := stream_no_delayed_endpoint e t k d hkpos htA
      rw [htime,hlen] at hf
      exact False.elim (hf huss hu ht)
    · let k := (t-u).toNat
      have hk : (k : Int)=t-u := Int.toNat_of_nonneg (by omega)
      have hkpos : 0<k := by omega
      have htime : u+(k : Int)=t := by omega
      have hlen : k+f=d := by omega
      have hf := stream_no_delayed_endpoint e u k f hkpos huA
      rw [htime,hlen] at hf
      exact False.elim (hf htss ht hu)

/-- Removing current A permits a shared endpoint, already with one SS. -/
theorem current_A_control :
    P2 ([true,true,false,false]++[true,true,false]) ∧
    P2 [true,true,false] ∧
    ssCount ([true,true,false,false]++[true,true,false])=1 := by unfold P2; decide

/-- Two SS edges suffice to break the strict moment margin, while the
intervening word still ends A and both windows are genuine P2 words. -/
theorem two_SS_control :
    let v := [true,true,false,true,false,true,false,true,false,false,false,true]
    P2 (v++[true,true,false]) ∧ P2 [true,true,false] ∧
    ssCount (v++[true,true,false])=2 ∧ moment v=-(v.length : Int) := by
  dsimp
  unfold P2
  decide

/-- S-ending does not hold for the supplied window before shortening. -/
theorem A_ended_nonminimum_control :
    P2 [true,true,false,true,false,false,true] ∧
    ssCount [true,true,false,true,false,false,true]=1 ∧
    P2 [true,true,false] := by unfold P2; decide

/-- At two SS, even the normalization to an S-ended prefix can fail.
The unique P2 prefix has length eleven and ends A. -/
theorem two_SS_minimum_end_A_control :
    let w := [false,true,true,true,false,true,true,false,false,false,true]
    P2 w ∧ ssCount w=2 ∧ ∀ d : Fin 11, ¬ P2 (w.take d.val) := by
  dsimp
  unfold P2
  decide

end Recaman.LowSSEndpoint
