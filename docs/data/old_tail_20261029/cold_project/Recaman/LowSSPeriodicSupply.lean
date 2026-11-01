import Recaman.LowSSEndpoint
import Recaman.SharpPeriodicSupply

namespace Recaman.LowSSPeriodicSupply

open LeadingRunSupply OneSSMultiplicity LowSSEndpoint SharpPeriodicSupply

/-! One endpoint injection for all S-ended P2 windows with at most one SS.
There is no restriction on the period mass, lag, or SAAS language. -/

def endpointPhase (p : Nat) (t : Int) (d : Nat) : Nat := phase p (t-d)

theorem endpoint_is_S (e : Int → Bool) (p : Nat) (hp : 0<p)
    (hper : ∀ x : Int, e (x+p)=e x) (t : Int) (d : Nat)
    (hend : e (t-d)=false) : e (endpointPhase p t d)=false := by
  rw [endpointPhase,phase_cast p hp]
  let q := t-(d : Int)
  have htime : q=q%p+(q/p)*p := by
    have := Int.ediv_mul_add_emod q (p : Int)
    omega
  change e q=false at hend
  rw [htime,LagElevenPeriodic.e_shift e p hper] at hend
  exact hend

theorem endpoint_mod_injective (e : Int → Bool) (p : Nat) (hp : 0<p)
    (hper : ∀ x : Int, e (x+p)=e x) (t u : Int) (d f : Nat)
    (htA : e t=true) (huA : e u=true)
    (htss : ssCount (past e t d)≤1) (huss : ssCount (past e u f)≤1)
    (htP : ShortPeriodicSupply.P2 e t d) (huP : ShortPeriodicSupply.P2 e u f)
    (heq : endpointPhase p t d=endpointPhase p u f) : t%p=u%p := by
  have hmod := phase_eq_mod p hp (t-d) (u-f) heq
  obtain ⟨z,hz⟩ := lift_equal_mod p _ _ hmod
  have huA' : e (u+z*p)=true := by rw [LagElevenPeriodic.e_shift e p hper]; exact huA
  have huss' : ssCount (past e (u+z*p) f)≤1 := by rw [past_shift e p hper]; exact huss
  have huP' := (p2_shift e p hper u z f).mpr huP
  have htu := endpoint_injective e t (u+z*p) d f htA huA' htss huss' htP huP' (by omega)
  rw [htu]
  simp [Int.add_emod]

/-- A joint capacity theorem: one map handles all members of U. S-ending
is a substantive premise, not silently inferred from the P2 equations. -/
theorem periodic_Sended_lowSS_capacity (e : Int → Bool) (p : Nat) (hp : 0<p)
    (hper : ∀ x : Int, e (x+p)=e x)
    (U : List Nat) (hUnodup : U.Nodup) (hUrange : ∀ u, u∈U → u<p)
    (hSupply : ∀ u, u∈U → e u=true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d)≤1 ∧ e (u-d)=false) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  classical
  let lag := fun u : Nat => if hu : u∈U then Classical.choose (hSupply u hu).2 else 0
  have hlag : ∀ u, u∈U → ShortPeriodicSupply.P2 e u (lag u) ∧
      ssCount (past e u (lag u))≤1 ∧ e (u-lag u)=false := by
    intro u hu
    dsimp [lag]
    rw [dif_pos hu]
    exact Classical.choose_spec (hSupply u hu).2
  let f := fun u : Nat => endpointPhase p u (lag u)
  have hinj : ∀ u v, u∈U → v∈U → f u=f v → u=v := by
    intro u v hu hv heq
    have hmod := endpoint_mod_injective e p hp hper u v (lag u) (lag v)
      (hSupply u hu).1 (hSupply v hv).1 (hlag u hu).2.1 (hlag v hv).2.1
      (hlag u hu).1 (hlag v hv).1 heq
    have hult := hUrange u hu
    have hvlt := hUrange v hv
    rw [Int.emod_eq_of_lt (by omega) (by omega),Int.emod_eq_of_lt (by omega) (by omega)] at hmod
    omega
  have hnodup := LagElevenPeriodic.nodup_map_of_inj hUnodup hinj
  have hsub : U.map f ⊆ LagElevenPeriodic.subPhases e 0 p := by
    intro q hq
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hq
    apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
    refine ⟨phase_lt p hp _,?_⟩
    simpa [f] using endpoint_is_S e p hp hper u (lag u) (hlag u hu).2.2
  have hlen := hnodup.length_le_of_subset hsub
  simpa using hlen

/-- Full low-SS capacity. Every witness is shortened inside its own
history, so S-ending is derived rather than assumed. -/
theorem periodic_lowSS_capacity (e : Int → Bool) (p : Nat) (hp : 0<p)
    (hper : ∀ x : Int, e (x+p)=e x)
    (U : List Nat) (hUnodup : U.Nodup) (hUrange : ∀ u, u∈U → u<p)
    (hSupply : ∀ u, u∈U → e u=true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d)≤1) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  apply periodic_Sended_lowSS_capacity e p hp hper U hUnodup hUrange
  intro u hu
  obtain ⟨hA,d,hP,hss⟩ := hSupply u hu
  obtain ⟨f,_,_,hfP,hfss,hfS⟩ := stream_S_witness e u d hP hss
  exact ⟨hA,f,hfP,hfss,hfS⟩

/-- The originally requested joint class, with neither minimum-lag nor
NoSAAS left as a premise. Clean and one-SS phases use one common map. -/
theorem periodic_clean_oneSS_capacity (e : Int → Bool) (p : Nat) (hp : 0<p)
    (hper : ∀ x : Int, e (x+p)=e x)
    (U : List Nat) (hUnodup : U.Nodup) (hUrange : ∀ u, u∈U → u<p)
    (hSupply : ∀ u, u∈U → e u=true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧
        (LocalParitySupply.EvenBackA e u d ∨ ssCount (past e u d)=1)) :
    U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length := by
  apply periodic_lowSS_capacity e p hp hper U hUnodup hUrange
  intro u hu
  obtain ⟨hA,d,hP,hclass⟩ := hSupply u hu
  refine ⟨hA,d,hP,?_⟩
  rcases hclass with hclean | hss
  · have hslots := (SSFreeSupply.evenSlots_past_iff e u d).mpr hclean
    have hs := noSS_count_zero _ (SSFreeSupply.evenSlots_noSS _ hslots)
    omega
  · omega

theorem addition_count_filter (e : Int → Bool) (n : Nat) :
    ((List.range n).filter (fun i : Nat => e i)).length=ShortPeriodicSupply.additionCount e 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [LagElevenPeriodic.filter_length_succ,ShortPeriodicSupply.additionCount,ih]
    simp

/-- Every positive-mass period has a current A for which every P2
witness, if any, crosses at least two SS edges. There is no lag cutoff. -/
theorem positive_period_requires_two_SS (e : Int → Bool) (p : Nat) (hp : 0<p)
    (hper : ∀ x : Int, e (x+p)=e x) (hpos : 0<ShortPeriodicSupply.signSum e 0 p) :
    ∃ u : Nat, u<p ∧ e u=true ∧
      ∀ d : Nat, ShortPeriodicSupply.P2 e u d → 2≤ssCount (past e u d) := by
  classical
  apply Classical.byContradiction
  intro hn
  let U := (List.range p).filter (fun i : Nat => e i)
  have hU : U.Nodup := List.Nodup.sublist List.filter_sublist List.nodup_range
  have hmem : ∀ u, u∈U → u<p ∧ e u=true := by
    intro u hu
    have h := List.mem_filter.mp hu
    exact ⟨List.mem_range.mp h.1,h.2⟩
  have hall : ∀ u, u∈U → e u=true ∧ ∃ d : Nat,
      ShortPeriodicSupply.P2 e u d ∧ ssCount (past e u d)≤1 := by
    intro u hu
    refine ⟨(hmem u hu).2,?_⟩
    apply Classical.byContradiction
    intro hnone
    apply hn
    refine ⟨u,(hmem u hu).1,(hmem u hu).2,?_⟩
    intro d hP
    by_cases hss : 2≤ssCount (past e u d)
    · exact hss
    · exact False.elim (hnone ⟨d,hP,by omega⟩)
  have hcap := periodic_lowSS_capacity e p hp hper U hU (fun u hu => (hmem u hu).1) hall
  have hA := addition_count_filter e p
  have hS := LagElevenPeriodic.subtractionCount_eq_filter e 0 p
  have hm := ShortPeriodicSupply.signSum_eq_counts e 0 p
  change U.length=ShortPeriodicSupply.additionCount e 0 p at hA
  omega

end Recaman.LowSSPeriodicSupply
