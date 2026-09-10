import Recaman.OneSSGapAlgebra

namespace Recaman.OneSSMultiplicity

open LeadingRunSupply SSFreeSupply

/-! A single SS pair can support arbitrarily many distinct current-A P2
windows. Minimum lag, NoSAAS, the actual finite common-history embedding,
and current-A positions are all checked here. -/

def core : List Bool := [false,true,true,true,true,false,false]
def window (k : Nat) : List Bool := alt false k ++ core ++ alt true (3*k)

def ssCount : List Bool → Nat
  | [] => 0
  | b::w => (if b=false ∧ w.head?=some false then 1 else 0)+ssCount w

theorem alt_length (b : Bool) (k : Nat) : (alt b k).length=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alt,ih]; omega

theorem alt_append (b : Bool) (m n : Nat) : alt b (m+n)=alt b m++alt b n := by
  induction m with
  | zero => simp [alt]
  | succ m ih => simp [alt,ih,Nat.succ_add]

theorem alt_A_moment (k : Nat) : moment (alt true k)=-(k : Int) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alt,moment,mass_cons,alt_mass,ShortPeriodicSupply.sign,ih]; omega

theorem window_length (k : Nat) : (window k).length=8*k+7 := by simp [window,core,alt_length]; omega

theorem window_P2 (k : Nat) : P2 (window k) := by
  have hm : mass core=1 := by decide
  have hM : moment core=0 := by decide
  have hL := alt_length false k
  constructor
  · simp [window,mass_append,alt_mass,hm]
  · simp only [window,moment_append,alt_mass,hm,hM,alt_S_moment,alt_A_moment,
      List.length_append,hL,Int.mul_zero,Int.add_zero,Int.mul_one,Int.natCast_mul,Int.cast_ofNat_Int]
    omega

theorem ssCount_pre_SA (w : List Bool) : ssCount (false::true::w)=ssCount w := by simp [ssCount]

theorem ssCount_append_AS (w : List Bool) : ssCount (w++[true,false])=ssCount w := by
  induction w with
  | nil => decide
  | cons b w ih =>
    cases w with
    | nil => cases b <;> decide
    | cons c w => simpa [ssCount] using ih

theorem ssCount_pre_alt (k : Nat) (w : List Bool) : ssCount (alt false k++w)=ssCount w := by
  induction k with
  | zero => simp [alt]
  | succ k ih => simpa [alt,ssCount] using ih

theorem ssCount_post_alt (k : Nat) (w : List Bool) : ssCount (w++alt true k)=ssCount w := by
  induction k with
  | zero => simp [alt]
  | succ k ih =>
    have heq : alt true (k+1)=alt true k++[true,false] := by rw [alt_append]; rfl
    rw [heq,← List.append_assoc,ssCount_append_AS,ih]

theorem window_single_SS (k : Nat) : ssCount (window k)=1 := by
  rw [window,ssCount_post_alt,ssCount_pre_alt]
  decide

/-- Every smaller window occurs in one common finite history. -/
theorem window_embedding (K k : Nat) (hk : k≤K) :
    window K=alt false (K-k)++window k++alt true (3*(K-k)) := by
  have hS : alt false K=alt false (K-k)++alt false k := by
    have heq : K=(K-k)+k := by omega
    have h := alt_append false (K-k) k
    rw [← heq] at h
    exact h
  have hA : alt true (3*K)=alt true (3*k)++alt true (3*(K-k)) := by
    have heq : 3*K=3*k+3*(K-k) := by omega
    rw [heq,alt_append]
  unfold window
  rw [hS,hA]
  simp [List.append_assoc]

theorem current_prefix_A (K r : Nat) (tail : List Bool) (hr : r≤K) :
    (true::(alt false K++tail))[2*r]?=some true := by
  induction K generalizing r with
  | zero =>
    have hr0 : r=0 := by omega
    subst r
    rfl
  | succ K ih =>
    cases r with
    | zero => rfl
    | succ r =>
      have h := ih r (by omega)
      simpa [alt,Nat.mul_add] using h

theorem source_A (K k : Nat) (hk : k≤K) : (true::window K)[2*(K-k)]?=some true := by
  have h := current_prefix_A K (K-k) (core++alt true (3*K)) (by omega)
  simpa [window,List.append_assoc] using h

theorem sources_distinct (K k j : Nat) (hk : k≤K) (hj : j≤K)
    (heq : 2*(K-k)=2*(K-j)) : k=j := by omega

theorem shared_SS_location (K : Nat) :
    (true::window K)[2*K+6]?=some false ∧ (true::window K)[2*K+7]?=some false := by
  simp [window,List.append_assoc,alt_length,core]

/-- K+1 injectively indexed A positions, with P2 windows embedded in the
same finite word whose total SS count is one. -/
theorem finite_history_certificate (K : Nat) :
    ssCount (true::window K)=1 ∧
    ∀ k : Nat, k≤K → P2 (window k) ∧
      (true::window K)[2*(K-k)]?=some true ∧
      window K=alt false (K-k)++window k++alt true (3*(K-k)) := by
  constructor
  · simpa [ssCount] using window_single_SS K
  · intro k hk
    exact ⟨window_P2 k,source_A K k hk,window_embedding K k hk⟩

theorem alt_S_prefix_nonpositive (k d : Nat) : mass ((alt false k).take d) ≤ 0 := by
  induction k generalizing d with
  | zero => simp [alt]
  | succ k ih =>
    cases d with
    | zero => simp
    | succ d =>
      cases d with
      | zero => simp [alt,mass_cons,ShortPeriodicSupply.sign]
      | succ d =>
        have h := ih d
        simp [alt,mass_cons,ShortPeriodicSupply.sign]
        omega

theorem alt_A_zero_prefix_moment (k d : Nat) (hd : d≤2*k)
    (hm : mass ((alt true k).take d)=0) : 2*moment ((alt true k).take d)=-(d : Int) := by
  induction k generalizing d with
  | zero =>
    have h : d=0 := by omega
    subst d
    rfl
  | succ k ih =>
    cases d with
    | zero => rfl
    | succ d =>
      cases d with
      | zero => simp [alt,mass_cons,ShortPeriodicSupply.sign] at hm
      | succ d =>
        have hm' : mass ((alt true k).take d)=0 := by
          simp [alt,mass_cons,ShortPeriodicSupply.sign] at hm
          omega
        have h := ih d (by omega) hm'
        simp only [alt,Bool.not_true,List.take_succ_cons,moment,mass_cons,ShortPeriodicSupply.sign,
          Bool.false_eq_true,if_false,if_true,hm',Int.add_zero,Int.natCast_add,Int.cast_ofNat_Int]
        omega

/-- The supply is minimal for every k, proved directly on all proper prefixes. -/
theorem window_minimum (k d : Nat) (hd : d≤(window k).length) (hP : P2 ((window k).take d)) :
    d=(window k).length := by
  by_cases hshort : d≤2*k
  · have heq : (window k).take d=(alt false k).take d := by
      rw [window,List.append_assoc,List.take_append_of_le_length (by rw [alt_length]; exact hshort)]
    have hm := hP.1
    rw [heq] at hm
    have hbound := alt_S_prefix_nonpositive k d
    omega
  · let r := d-2*k
    have hdeq : d=2*k+r := by dsimp [r]; omega
    have heq : (window k).take d=alt false k++(core++alt true (3*k)).take r := by
      rw [window,List.append_assoc,List.take_append,List.take_of_length_le (by rw [alt_length]; omega),alt_length]
    have hm := hP.1
    have hM := hP.2
    rw [heq] at hm hM
    by_cases hr : r≤7
    · have ht : (core++alt true (3*k)).take r=core.take r :=
        List.take_append_of_le_length (by simpa [core] using hr)
      rw [ht] at hm hM
      have hrCases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by omega
      rcases hrCases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
      all_goals rw [‹r = _›] at hm hM
      all_goals simp [core,mass_append,mass_cons,moment_append,moment,alt_mass,
        alt_S_moment,alt_length,ShortPeriodicSupply.sign] at hm hM
      all_goals rw [window_length]; omega
    · let v := (alt true (3*k)).take (r-7)
      have ht : (core++alt true (3*k)).take r=core++v := by
        rw [List.take_append,List.take_of_length_le (by simp [core]; omega)]
        rfl
      rw [ht] at hm hM
      have hmcore : mass core=1 := by decide
      have hMcore : moment core=0 := by decide
      have hm0 : mass v=0 := by
        simp [mass_append,alt_mass,hmcore] at hm
        omega
      have hlen : r-7≤2*(3*k) := by rw [window_length] at hd; omega
      have hvM := alt_A_zero_prefix_moment (3*k) (r-7) hlen hm0
      change 2*moment v=-((r-7 : Nat) : Int) at hvM
      simp only [moment_append,mass_append,hmcore,hMcore,hm0,alt_S_moment,
        alt_length,Int.mul_zero,Int.add_zero,Int.mul_one,Int.natCast_mul,Int.cast_ofNat_Int] at hM
      rw [window_length]
      omega

def saasCount : List Bool → Nat
  | [] => 0
  | b::w => (if b=false ∧ w.take 3=[true,true,false] then 1 else 0)+saasCount w

theorem saasCount_pre_SAS (w : List Bool) :
    saasCount (false::true::false::w)=saasCount (false::w) := by simp [saasCount]

theorem saasCount_append_SAS (u : List Bool) :
    saasCount (u++[false,true,false])=saasCount (u++[false]) := by
  induction u with
  | nil => decide
  | cons b u ih =>
    cases u with
    | nil => cases b <;> decide
    | cons c u =>
      cases u with
      | nil => cases b <;> cases c <;> decide
      | cons d u =>
        cases u with
        | nil => cases b <;> cases c <;> cases d <;> decide
        | cons e u => simpa [saasCount] using ih

theorem saasCount_pre_alt (k : Nat) (w : List Bool) :
    saasCount (alt false k++false::w)=saasCount (false::w) := by
  induction k with
  | zero => simp [alt]
  | succ k ih =>
    cases k with
    | zero => simpa [alt] using saasCount_pre_SAS w
    | succ k => simpa [alt,saasCount] using ih

theorem saasCount_post_alt (k : Nat) (u : List Bool) :
    saasCount ((u++[false])++alt true k)=saasCount (u++[false]) := by
  induction k generalizing u with
  | zero => simp [alt]
  | succ k ih =>
    have heq : (u++[false])++alt true (k+1)=((u++[false,true])++[false])++alt true k := by
      simp [alt,List.append_assoc]
    rw [heq,ih]
    simpa [List.append_assoc] using saasCount_append_SAS u

theorem window_saasCount_zero (k : Nat) : saasCount (window k)=0 := by
  have hpost := saasCount_post_alt (3*k) (alt false k++[false,true,true,true,true,false])
  have hpre := saasCount_pre_alt k [true,true,true,true,false,false]
  have hc : saasCount core=0 := by decide
  have hpost' : saasCount (window k)=saasCount (alt false k++core) := by
    simpa [window,core,List.append_assoc] using hpost
  exact hpost'.trans (hpre.trans hc)

theorem saas_occurrence_positive (u v : List Bool) :
    0<saasCount (u++false::true::true::false::v) := by
  induction u with
  | nil => simp [saasCount]; omega
  | cons b u ih => simp only [List.cons_append,saasCount]; omega

theorem window_noSAAS (k : Nat) : NoSAAS (window k) := by
  intro u v heq
  have hpos := saas_occurrence_positive u v
  rw [← heq,window_saasCount_zero] at hpos
  omega

theorem history_noSAAS (K : Nat) : NoSAAS (true::window K) := by
  intro u v heq
  cases u with
  | nil => simp at heq
  | cons b u =>
    have ht : window K=u++false::true::true::false::v := (List.cons.inj heq).2
    exact window_noSAAS K u v ht

def sourcePositions (K : Nat) : List Nat := (List.range (K+1)).map fun k => 2*(K-k)

theorem sourcePositions_data (K : Nat) :
    (sourcePositions K).length=K+1 ∧ (sourcePositions K).Nodup := by
  constructor
  · simp [sourcePositions]
  · apply LagElevenPeriodic.nodup_map_of_inj List.nodup_range
    intro k j hk hj heq
    have hk' := List.mem_range.mp hk
    have hj' := List.mem_range.mp hj
    exact sources_distinct K k j (by omega) (by omega) heq

/-- Any proposed constant demand budget per SS pair is exceeded by a finite
NoSAAS history. The many other S positions remain available globally. -/
theorem unbounded_SS_demand (C : Nat) :
    C*ssCount (true::window C)<(sourcePositions C).length ∧
    (sourcePositions C).Nodup ∧ NoSAAS (true::window C) := by
  have hc := (finite_history_certificate C).1
  have hs := sourcePositions_data C
  exact ⟨by rw [hc,hs.1]; omega,hs.2,history_noSAAS C⟩

theorem window_S_budget (k : Nat) :
    ones (window k)=(4*k+4 : Nat) ∧ ((window k).length : Int)-ones (window k)=(4*k+3 : Nat) := by
  have hm := mass_eq (window k)
  have hP := (window_P2 k).1
  have hl := window_length k
  rw [hl,hP] at hm
  constructor <;> omega

end Recaman.OneSSMultiplicity
