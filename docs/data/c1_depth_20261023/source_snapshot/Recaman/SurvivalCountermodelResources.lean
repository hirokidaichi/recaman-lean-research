import Recaman.SurvivalCountermodelReplay

namespace Recaman.SurvivalFamily.Geometry
variable (g : Geometry) {F : List Nat}

/-- Candidate at the l-th transition after the comb end. -/
def candidate (F : List Nat) (l : Nat) : Int := g.val F (g.T+l-1)-(g.C+l : Nat)

theorem rise_candidate (hF : ∀ z ∈ F, (z : Int)<g.w) {l : Nat}
    (hl : 1≤l) (hld : l≤g.D) : g.candidate F l=g.addPoint ((l : Int)-2)-1 := by
  have ht : g.T+l-1=g.T+(l-1) := by omega
  have he : ((l-1 : Nat) : Int)=(l : Int)-1 := by omega
  unfold candidate
  rw [ht, (g.rise_invariant hF (p := l-1) (by omega)).1]
  have ha := g.add_candidate ((l : Int)-1)
  have hc := g.cast_C
  rw [he]
  have ha' : (l : Int)-1-1=(l : Int)-2 := by omega
  rw [ha'] at ha
  omega

theorem rise_candidate_positive (hF : ∀ z ∈ F, (z : Int)<g.w) {l : Nat}
    (hl : 5≤l) (hld : l≤g.D) : 0<g.candidate F l := by
  rw [g.rise_candidate hF (by omega) hld]
  have hd := g.cast_D
  have ht := g.tri_bounds (p := (l : Int)-2) (by omega) (by omega)
  have hj := g.j_pos
  have hc := g.c_pos
  have hm := Int.mul_nonneg (show 0≤(l : Int)-2 by omega) (show 0≤g.c by omega)
  unfold addPoint
  omega

theorem candidate_seen_iff (hF : ∀ z ∈ F, (z : Int)<g.w) {l : Nat}
    (hl : 5≤l) (hld : l≤2*g.D) :
    0<g.candidate F l ∧ (g.seen F (g.T+l-1) (g.candidate F l) ↔ l≤g.D) := by
  have hb := g.boundary_comb
  have hc := g.cast_C
  have hd := g.cast_D
  have hd' := g.d_ge
  have ht : g.T+l-1+1=g.T+l := by omega
  have hclock : g.B+(g.T+l-1)+1=g.C+l := by omega
  by_cases hr : l≤g.D
  · have hp := g.rise_candidate_positive hF hl hr
    have hcur : (g.C+l : Nat)<g.val F (g.T+l-1) := by
      unfold candidate at hp
      omega
    have hseen := SeededReplay.seen_iff_add (b := g.B) (s := g.start F)
      (t := g.T+l-1) (by omega) (by rw [hclock]; exact hcur)
    change g.seen F (g.T+l-1) _ ↔ g.val F (g.T+l-1+1)=_ at hseen
    rw [hclock, ht] at hseen
    change g.seen F (g.T+l-1) (g.candidate F l) ↔ _ at hseen
    have he : g.T+l-1=g.T+(l-1) := by omega
    have hv := (g.rise_invariant hF hr).1
    have hv' := (g.rise_invariant hF (p := l-1) (by omega)).1
    have ha := g.add_succ ((l-1 : Nat) : Int)
    have ha' : ((l-1 : Nat) : Int)+1=(l : Int) := by omega
    rw [ha'] at ha
    have hadd : g.val F (g.T+l)=g.val F (g.T+l-1)+(g.C+l : Nat) := by
      rw [he, hv, hv']
      omega
    exact ⟨hp, ⟨fun _ => hr, fun _ => hseen.mpr hadd⟩⟩
  · let k := l-g.D-1
    have hk : k+1≤g.D := by dsimp [k]; omega
    have he : g.T+l-1=g.T+g.D+k := by dsimp [k]; omega
    have he' : g.T+l=g.T+g.D+(k+1) := by dsimp [k]; omega
    have hv := (g.down_invariant hF (Nat.le_of_lt (show k<g.D by omega))).1
    have hv' := (g.down_invariant hF hk).1
    have hq : 0≤g.d-((k+1 : Nat) : Int) := by omega
    have hq' : g.d-((k+1 : Nat) : Int)≤g.d := by omega
    have hpos := g.down_ge_w hq hq'
    have hw := g.w_pos
    have hs := g.down_step (g.d-((k+1 : Nat) : Int))
    have hqeq : g.d-((k+1 : Nat) : Int)+1=g.d-(k : Int) := by omega
    rw [hqeq] at hs
    have hn : (g.C+l : Nat)=g.c+2*g.d-(g.d-((k+1 : Nat) : Int)) := by
      dsimp [k]
      omega
    have hcan : g.candidate F l=g.downPoint (g.d-((k+1 : Nat) : Int)) := by
      unfold candidate
      rw [he, hv, hn]
      omega
    have hp : 0<g.candidate F l := by rw [hcan]; omega
    refine ⟨hp, ?_⟩
    constructor
    · intro hm
      have hh := g.add_value (t := g.T+l-1) (Or.inr (by simpa [hclock, candidate] using hm))
      rw [hclock, ht] at hh
      have hval := congrArg (g.val F) he
      have hval' := congrArg (g.val F) he'
      have hc' := g.c_pos
      omega
    · omega

 theorem blocker_one_use (hF : ∀ z ∈ F, (z : Int)<g.w) {l m : Nat}
    (hl : 5<l) (hlD : l≤g.D) (hm : 5<m) (hmD : m≤g.D)
    (he : g.candidate F l=g.candidate F m) : l=m := by
  rw [g.rise_candidate hF (by omega) hlD, g.rise_candidate hF (by omega) hmD] at he
  have hd := g.cast_D
  have hh := g.add_injective (p := (l : Int)-2) (q := (m : Int)-2)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

 theorem comb_blocked (hF : ∀ z ∈ F, (z : Int)<g.w) :
    g.seen F g.T (2*g.j-1) ∧
    g.seen F g.T (2*g.c+2*g.j+2) ∧
    0<g.candidate F 5 ∧ g.seen F (g.T+4) (g.candidate F 5) := by
  have hd := g.cast_D
  have hd' := g.d_ge
  refine ⟨g.core_seen F (Or.inr (Or.inr (Or.inl rfl))) g.T, ?_, ?_, ?_⟩
  · apply g.core_seen F
    right; right; right; right
    refine ⟨2, by omega, by omega, ?_⟩
    simp [addPoint]
    omega
  · exact (g.candidate_seen_iff hF (l := 5) (by omega) (by omega)).1
  · have hh := (g.candidate_seen_iff hF (l := 5) (by omega) (by omega)).2.mpr (by omega)
    simpa using hh

end Recaman.SurvivalFamily.Geometry
