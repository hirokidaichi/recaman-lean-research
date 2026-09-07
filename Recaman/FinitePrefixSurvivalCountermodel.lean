import Recaman.SurvivalCountermodelSeed
import Recaman.SurvivalCountermodelResources
import Recaman.SeededReplayWrap

namespace Recaman.SurvivalFamily

/-! The complete arbitrary-finite-history countermodel of issue #70.
The initial state is explicit; every later state is `Basic.step` generated.
No statement here identifies this continuation with the canonical orbit. -/

theorem finite_prefix_survival_countermodel (F : List Nat) :
    ∃ g : Geometry,
      g.w%2=0 ∧ g.d%2=0 ∧
      (∀ z ∈ F, (z : Int)<g.w) ∧
      ((g.B+2 : Nat) : Int)=16*(5*g.j+1)+2*((5*g.j+1)%2) ∧
      (∀ z ∈ F, z ∈ g.seed F) ∧ 0 ∈ g.seed F ∧ g.X ∈ g.seed F ∧
      (g.seed F).length≤g.B+1 ∧
      (∀ z ∈ g.seed F, z≤g.B*(g.B+1)/2) ∧
      g.X%2=(g.B*(g.B+1)/2)%2 ∧
      g.level F 0=3 ∧ g.level F 1=2 ∧
      g.residue F 2=5*g.j+1 ∧
      g.val F 1=g.upper (g.j+1) ∧
      (∀ i, i≤g.J → g.val F (2+2*i)=g.lower (g.j-i)) ∧
      (∀ i, i<g.J → g.val F (3+2*i)=g.upper (g.j-i)) ∧
      g.val F g.T=2*g.j ∧
      (∀ p, p≤g.D → g.val F (g.T+p)=g.addPoint p) ∧
      (∀ k, k≤g.D → g.val F (g.T+g.D+k)=g.downPoint (g.d-k)) ∧
      g.seen F g.T (2*g.j-1) ∧
      g.seen F g.T (2*g.c+2*g.j+2) ∧
      0<g.candidate F 5 ∧ g.seen F (g.T+4) (g.candidate F 5) ∧
      g.val F (g.T+2*g.D)=g.w ∧
      g.val F (g.T+2*g.D)<(g.B+(g.T+2*g.D) : Nat) ∧
      (∀ t, g.T<t → t<g.T+2*g.D → (g.B+t : Nat)≤g.val F t) ∧
      (∀ t, t<g.T+2*g.D → g.residue F (t+1)≤g.residue F t) ∧
      (∃ t, g.T+2*g.D≤t ∧ g.residue F t<g.residue F (t+1)) ∧
      7*(5*g.j+1)-16*(2*g.j)=3*g.j+7 ∧ 16*(2*g.j)<7*(5*g.j+1) ∧
      (∀ l, 5<l → l≤2*g.D →
        0<g.candidate F l ∧ (g.seen F (g.T+l-1) (g.candidate F l) ↔ l≤g.D)) ∧
      (∀ l m, 5<l → l≤g.D → 5<m → m≤g.D →
        g.candidate F l=g.candidate F m → l=m) := by
  let g := parameters (scale F)
  have hF := parameters_cover F
  have hp := seed_payload F
  change (∀ z ∈ F, z ∈ g.seed F) ∧ 0 ∈ g.seed F ∧ g.X ∈ g.seed F ∧
    (g.seed F).length≤g.B+1 ∧ (∀ z ∈ g.seed F, 2*z≤g.B*(g.B+1)) at hp
  have hw := g.actual_word hF
  have hb := g.comb_blocked hF
  have hl := g.first_late_landing hF
  have hj := g.j_pos
  have hB := g.cast_B
  have hc := g.clock_large
  have hs : 2*((g.start F).value : Int)≤(g.B : Int)*(g.B+1) := by
    have hh := hp.2.2.2.2 g.X hp.2.2.1
    have hi := Int.ofNat_le.mpr hh
    change 2*(g.X : Int)≤(g.B : Int)*(g.B+1)
    simpa using hi
  have hf := SeededReplay.exists_later_wrap (b := g.B) (s := g.start F)
    (by omega) hs (g.T+2*g.D)
  have hr : g.residue F 2=5*g.j+1 := by
    simpa using (g.lower_coordinates hF (i := 0) (Nat.zero_le _)).2
  refine ⟨g, (parameters_even _).1, (parameters_even _).2, hF,
    parameters_paper_clock _, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_,
    parameters_parity _, (g.initial_coordinates F).1, (g.middle_coordinates hF).1,
    hr, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
    hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hl.1, hl.2.1, hl.2.2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have := hp.2.2.2.2 z hz
    omega
  · intro t ht
    exact g.no_wrap hF ht
  · rcases hf with ⟨t, ht, hwrap⟩
    refine ⟨t, ht, ?_⟩
    simpa [Geometry.residue, Nat.add_assoc] using hwrap
  · omega
  · omega
  · intro l hl hlD
    exact g.candidate_seen_iff hF (by omega) hlD
  · intro l m hl hlD hm hmD he
    exact g.blocker_one_use hF hl hlD hm hmD he

end Recaman.SurvivalFamily
